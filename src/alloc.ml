module Ir = Passes.MipsMem
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
  | `Ori (dst, rx, _) -> add_all set [dst; rx]
  | `Mult (rx, ry)
  | `Div (rx, ry)
  | `Beq (rx, ry, _)
  | `Bne (rx, ry, _) -> add_all set [rx; ry]
  | `Mflo dst
  | `Li (dst, _) -> add_all set [dst]
  | `Blez (rx, _) | `Bltz (rx, _)
  | `Bgez (rx, _) | `Bgtz (rx, _)
  | `Return (`Ident rx) -> add_all set [rx]
  | `Lw (dst, _, src) | `Sw (src, _, dst) -> add_all set [src; dst]
  | `Call (_, ops) ->
    let args = ops >>= (function `Int _ -> [] | `Ident id -> [id]) in
    add_all set args
  | `Callr (dst, _, ops) ->
    let args = ops >>= (function `Int _ -> [] | `Ident id -> [id]) in
    add_all set (dst::args)
  | `Block instrs -> collect_vars ~set instrs
  | `J _ | `Return (`Int _) | `Label _ -> set

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

let naive ~locals_base ~temps_base {TIR.intList; _} instrs =
  let all_vars = collect_vars instrs in
  let mapping = Hashtbl.create (VarSet.cardinal all_vars) in
  let alloc_sizes =
    List.map (function TIR.Scalar name -> (name, 4) | TIR.Array (name, n) -> (name, n * 4)) intList in
  let uniq =
    let counter = ref 0 in
    fun () ->
      let n = !counter in
      counter := n + 1;
      n in
  (* Map variables stored in the stack to their spill offset *)
  VarSet.iter begin fun key ->
    (* Calculate the offset of the var in the stack *)
    let offset = ref 0 and continue = ref true in
    List.iter begin fun (name, size) ->
      if !continue then offset := !offset + size else ();
      if name = key then continue := false else ()
    end alloc_sizes;
    if !continue then
      Hashtbl.add mapping key (Spill (locals_base - !offset))
    else
      Hashtbl.add mapping key (Spill (temps_base - uniq ()))
  end all_vars;
  mapping
