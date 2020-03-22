module Ir = Passes.MipsFlat
module TIR = TigerIR.Ir

module VarSet = Set.Make(String)

let rec add_all set = function
  | [] -> set
  | item::rest -> add_all (VarSet.add item set) rest

let (>>=) list fn = list |> List.map fn |> List.concat

let rec instr_collect_vars (set: VarSet.t): Ir.instr -> VarSet.t = function
  | `Add (dst, rx, ry)
  | `Sub (dst, rx, ry)
  | `And (dst, rx, ry)
  | `Or (dst, rx, ry) -> add_all set [dst; rx; ry]
  | `Addi (dst, rx, _)
  | `Subi (dst, rx, _)
  | `Andi (dst, rx, _)
  | `Ori (dst, rx, _)
  | `Sll (dst, rx, _) -> add_all set [dst; rx]
  | `Mult (rx, ry)
  | `Div (rx, ry)
  | `Beq (rx, ry, _)
  | `Bne (rx, ry, _) -> add_all set [rx; ry]
  | `Mflo dst
  | `Lui (dst, _) -> add_all set [dst]
  | `Jr rx
  | `Blez (rx, _) | `Bltz (rx, _)
  | `Bgez (rx, _) | `Bgtz (rx, _) -> add_all set [rx]
  | `Lw (dst, _, src) | `Sw (src, _, dst) -> add_all set [src; dst]
  | `J _ | `Jal _ |  `Label _ -> set

and collect_vars ?(set=VarSet.empty): Ir.instr list -> VarSet.t = function
  | [] -> set
  | instr::rest -> collect_vars ~set:(instr_collect_vars set instr) rest

(* For spilled variables, we'll reserve the $at (assembler temp) & $v1,
   since we need 2 registers to cover every possible case: instructions
   take <= 3 register operands and 1 of these is always a destination
   (so the dest is safe to overwrite in the case of spilled registers).
   When we need to use the spilled register, we'll load it into $sn,
   perform any operations, and the store $sn back on the stack. The int
   associated with a spill corresponds to its location relative to the
   frame pointer ($fp). *)
type allocation = Spill of int | Reg of string

(* Add identity mapping for each register to itself
   FIXME: We need to have some way of knowing which registers are virtual
   vs. physical, in case a user names a virtual register e.g. "a0" or "zero" *)
let add_registers_id mapping =
  List.iter (fun reg -> Hashtbl.add mapping reg (Reg reg)) [
    "zero"; "at"; "v0"; "v1"; "a0"; "a1"; "a2"; "a3";
    "t0"; "t1"; "t2"; "t3"; "t4"; "t5"; "t6"; "t7"; "t8"; "t9";
    "s0"; "s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7";
    "k0"; "k1"; "gp"; "sp"; "fp"; "ra"
  ];
  mapping

let naive {TIR.intList; _} instrs =
  let all_vars = collect_vars instrs in
  let mapping = Hashtbl.create (VarSet.cardinal all_vars) |> add_registers_id in
  let alloc_sizes =
    List.map (function TIR.Scalar name -> (name, 4) | TIR.Array (name, n) -> (name, n * 4)) intList in
  let locals_size = List.fold_left (fun acc (_, n) -> acc + n) 0 alloc_sizes in
  let locals_base = -8 (* $fp, $ra, locals ... *)
  and temps_base = -8 - locals_size in (* $fp, $ra, locals ..., temps ... *)
  let new_spills = ref 0 in (* # of new spill slots that need to be allocated (in bytes) *)
  let uniq_alloc =
    let counter = ref 0 in
    fun () ->
      let n = !counter in
      counter := n + 4;
      !counter in
  (* Map variables stored in the stack to their spill offset *)
  VarSet.iter begin fun key ->
    if not (Hashtbl.mem mapping key) then begin
      (* Calculate the offset of the var in the stack *)
      let offset = ref 0 and continue = ref true in
      List.iter begin fun (name, size) ->
        if !continue then offset := !offset + size else ();
        if name = then continue := false else ()
      end alloc_sizes;
      if !continue then
        Hashtbl.add mapping key (Spill (locals_base - !offset))
      else begin
        new_spills := !new_spills + 4;
        Hashtbl.add mapping key (Spill (temps_base - uniq_alloc ()))
      end
    end else ()
  end all_vars;
  (mapping, !new_spills)

let apply_alloc_dxy allocs (dst, x, y) instr_fn =
  let a_dst = Hashtbl.find allocs dst
  and a_x = Hashtbl.find allocs x
  and a_y = Hashtbl.find allocs y in

  let (spilled_dst, n_dst, r_dst) = match a_dst with
    | Spill n -> (true, n, "at")
    | Reg r -> (false, 0, r)
  and (spilled_x, n_x, r_x) = match a_x with
    | Spill n -> (true, n, "at")
    | Reg r -> (false, 0, r)
  and (spilled_y, n_y, r_y) = match a_y with
    | Spill n -> (true, n, "v1")
    | Reg r -> (false, 0, r) in
  
  (if spilled_x then [`Lw (r_x, n_x, "fp")] else []) @
  (if spilled_y then [`Lw (r_y, n_y, "fp")] else []) @
  instr_fn r_dst r_x r_y @
  (if spilled_dst then [`Sw (r_dst, n_dst, "fp")] else [])

let apply_alloc_dx allocs (dst, x) instr_fn =
  let a_dst = Hashtbl.find allocs dst
  and a_x = Hashtbl.find allocs x in

  let (spilled_dst, n_dst, r_dst) = match a_dst with
    | Spill n -> (true, n, "at")
    | Reg r -> (false, 0, r)
  and (spilled_x, n_x, r_x) = match a_x with
    | Spill n -> (true, n, "at")
    | Reg r -> (false, 0, r) in

  (if spilled_x then [`Lw (r_x, n_x, "fp")] else []) @
  instr_fn r_dst r_x @
  (if spilled_dst then [`Sw (r_dst, n_dst, "fp")] else [])

let apply_alloc_d allocs dst instr_fn =
  let a_dst = Hashtbl.find allocs dst in

  let (spilled_dst, n_dst, r_dst) = match a_dst with
    | Spill n -> (true, n, "at")
    | Reg r -> (false, 0, r) in

  instr_fn r_dst @
  (if spilled_dst then [`Sw (r_dst, n_dst, "fp")] else [])

let apply_alloc_xy allocs (x, y) instr_fn =
  let a_x = Hashtbl.find allocs x
  and a_y = Hashtbl.find allocs y in

  let (spilled_x, n_x, r_x) = match a_x with
    | Spill n -> (true, n, "at")
    | Reg r -> (false, 0, r)
  and (spilled_y, n_y, r_y) = match a_y with
    | Spill n -> (true, n, "v1")
    | Reg r -> (false, 0, r) in
  
  (if spilled_x then [`Lw (r_x, n_x, "fp")] else []) @
  (if spilled_y then [`Lw (r_y, n_y, "fp")] else []) @
  instr_fn r_x r_y

let apply_alloc_x allocs x instr_fn =
  let a_x = Hashtbl.find allocs x in

  let (spilled_x, n_x, r_x) = match a_x with
    | Spill n -> (true, n, "at")
    | Reg r -> (false, 0, r) in
  
  (if spilled_x then [`Lw (r_x, n_x, "fp")] else []) @
  instr_fn r_x

let apply_allocations allocs instrs =
  instrs >>= begin function
    | `Add (dst, x, y) ->
      let add dst x y = [`Add (dst, x, y)] in
      (apply_alloc_dxy allocs (dst, x, y) add)
    | `Addi (dst, x, imm) ->
      let addi dst x = [`Addi (dst, x, imm)] in
      (apply_alloc_dx allocs (dst, x) addi)
    | `Sub (dst, x, y) ->
      let sub dst x y = [`Sub (dst, x, y)] in
      (apply_alloc_dxy allocs (dst, x, y) sub)
    | `Subi (dst, x, imm) ->
      let subi dst x = [`Subi (dst, x, imm)] in
      (apply_alloc_dx allocs (dst, x) subi)
    | `Mult (x, y) ->
      let mult x y = [`Mult (x, y)] in
      (apply_alloc_xy allocs (x, y) mult)
    | `Div (x, y) ->
      let div x y = [`Div (x, y)] in
      (apply_alloc_xy allocs (x, y) div)
    | `Mflo dst ->
      let mflo dst = [`Mflo dst] in
      (apply_alloc_d allocs dst mflo)
    | `And (dst, x, y) ->
      let and_ dst x y = [`And (dst, x, y)] in
      (apply_alloc_dxy allocs (dst, x, y) and_)
    | `Andi (dst, x, imm) ->
      let andi dst x = [`Andi (dst, x, imm)] in
      (apply_alloc_dx allocs (dst, x) andi)
    | `Or (dst, x, y) ->
      let or_ dst x y = [`Or (dst, x, y)] in
      (apply_alloc_dxy allocs (dst, x, y) or_)
    | `Ori (dst, x, imm) ->
      let ori dst x = [`Ori (dst, x, imm)] in
      (apply_alloc_dx allocs (dst, x) ori)
    | `Sll (dst, x, imm) ->
      let sll dst x = [`Sll (dst, x, imm)] in
      (apply_alloc_dx allocs (dst, x) sll)
    | `Jr x ->
      let jr x = [`Jr x] in
      (apply_alloc_x allocs x jr)
    | `Beq (x, y, lbl) ->
      let beq x y = [`Beq (x, y, lbl)] in
      (apply_alloc_xy allocs (x, y) beq)
    | `Bne (x, y, lbl) ->
      let bne x y = [`Bne (x, y, lbl)] in
      (apply_alloc_xy allocs (x, y) bne)
    | `Blez (x, lbl) ->
      let blez x = [`Blez (x, lbl)] in
      (apply_alloc_x allocs x blez)
    | `Bgez (x, lbl) ->
      let bgez x = [`Bgez (x, lbl)] in
      (apply_alloc_x allocs x bgez)
    | `Bltz (x, lbl) ->
      let bltz x = [`Bltz (x, lbl)] in
      (apply_alloc_x allocs x bltz)
    | `Bgtz (x, lbl) ->
      let bgtz x = [`Bgtz (x, lbl)] in
      (apply_alloc_x allocs x bgtz)
    | `Lw (dst, imm, x) ->
      let lw dst x = [`Lw (dst, imm, x)] in
      (apply_alloc_dx allocs (dst, x) lw)
    | `Sw (x, imm, y) ->
      let sw x y = [`Sw (x, imm, y)] in
      (apply_alloc_xy allocs (x, y) sw)
    | `Lui (dst, imm) ->
      let lui dst = [`Lui (dst, imm)] in
      (apply_alloc_d allocs dst lui)
    | other -> [other]
  end