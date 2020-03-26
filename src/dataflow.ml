open Cfg

module Ir = Passes.MipsFlat

module VSet = Set.Make(struct
  type t = string
  let compare = compare
end)

type t = {
  gen_set: VSet.t;
  kill_set: VSet.t;
  in_set: VSet.t;
  out_set: VSet.t
}

let string_of_t elts =
  (* {...} *)
  let string_of_vset_elt elt =
    (* (line, variable) *)
    let var = elt in
    Printf.sprintf "%s" var in
  String.concat ", " (List.map string_of_vset_elt elts)

module VMap = Map.Make(G.V)

let def v =
  let _, instr = G.V.label v in
  let is_virtual name = name.[0] <> '$' in
  match instr with
  | `Add (dst, _, _)
  | `Addi (dst, _, _)
  | `Sub (dst, _, _)
  | `Mflo dst
  | `And (dst, _, _)
  | `Andi (dst, _, _)
  | `Or (dst, _, _)
  | `Ori (dst, _, _)
  | `Sll (dst, _, _)
  | `Lw (dst, _, _)
  | `Sw (_, _, dst) (* Is this the correct thing to do? *)
  | `Lui (dst, _) -> if is_virtual dst then VSet.singleton dst else VSet.empty
  | _ -> VSet.empty

let use v =
  let _, instr = G.V.label v in
  let is_virtual name = name.[0] <> '$' in
  let rec virtual_set = function
    | [] -> VSet.empty
    | id::rest when is_virtual id -> VSet.add id (virtual_set rest)
    | _::rest -> virtual_set rest in
  match instr with
  | `Add (_, x, y)
  | `Sub (_, x, y)
  | `Mult (x, y)
  | `Div (x, y)
  | `And (_, x, y)
  | `Or (_, x, y)
  | `Beq (x, y, _)
  | `Bne (x, y, _)
  | `Sw (x, _, y) -> virtual_set [x; y]
  | `Addi (_, x, _)
  | `Andi (_, x, _)
  | `Ori (_, x, _)
  | `Sll (_, x, _)
  | `Bgtz (x, _)
  | `Bltz (x, _)
  | `Blez (x, _)
  | `Bgez (x, _)
  | `Lw (_, _, x) -> virtual_set [x]
  | _ -> virtual_set []

let sets_converged left right =
  let same_in_out a b =
    VSet.equal a.in_set b.in_set && VSet.equal a.out_set b.out_set in
  VMap.equal same_in_out left right

let all_vars g =
  G.fold_vertex begin fun v set ->
    VSet.union (def v) set
  end g VSet.empty

let rec fixpoint g sets f =
  let sets' = f g sets in
  if sets_converged sets' sets then sets
  else fixpoint g sets' f

let init g =
  let sets = VMap.empty in
  G.fold_vertex begin fun v sets ->
    let def_set = def v
    and use_set = use v in
    let vset = {
      gen_set = use_set;
      kill_set = def_set;
      in_set = VSet.empty;
      out_set = VSet.empty
    } in
    VMap.add v vset sets
  end g sets

let solve g sets =
  let f g sets =
    let visited = Hashtbl.create (G.nb_vertex g) in
    let traverse node sets =
      if not (Hashtbl.mem visited node) then begin
        Hashtbl.add visited node ();
        let { gen_set; kill_set; _ } = VMap.find node sets
        and succ_ins =
          let succs = G.succ g node in
          List.map begin fun succ ->
            let { in_set; _ } = VMap.find succ sets in
            in_set
          end succs in
        let out_set = List.fold_left VSet.union VSet.empty succ_ins in
        let in_set = VSet.union gen_set (VSet.diff out_set kill_set) in
        let sets' = VMap.add node { gen_set; kill_set; in_set; out_set } sets in
        sets'
      end else sets in
    let reversed = Operations.mirror g in
    Topo.fold traverse reversed sets in
  fixpoint g sets f

let string_of_vertex v vset =
  (*
    Vertex[id]:
      IN = {...}
      OUT = {...}
      GEN = {...}
      KILL = {...}
  *)
  let v_id, _ = v in
  let format_set set =
    string_of_t (VSet.elements set) in
  Printf.sprintf {|
    Vertex[%d]:
      IN = {%s}
      OUT = {%s}
      GEN = {%s}
      KILL = {%s}
  |} v_id (format_set vset.in_set) (format_set vset.out_set) (format_set vset.gen_set) (format_set vset.kill_set)

let print_vmap vmap =
  let print_vset v vset =
    print_endline (string_of_vertex v vset) in
  VMap.iter print_vset vmap
