open Graph
module Ir = Passes.MipsFlat

module Vertex = struct
  (* id, instr *)
  type t = int * Ir.instr

  let compare = compare
  let equal = (=)
  let hash = Hashtbl.hash
end

module Edge = struct
  type t = [`Fallthrough | `Branch | `Jump]
  let compare = compare
  let default = `Fallthrough
end

module G =
  Imperative.Digraph.ConcreteBidirectionalLabeled(Vertex)(Edge)

module Operations = Oper.I(G)

module Topo = Topological.Make(G)

let build instrs =
  (* Create our graph *)
  let g = G.create () in

  (* We need each vertex to be unique in order to stop multiple vertices with
     the same code from being merged into one vertex. We can force uniqueness
     by giving each vertex a unique number *)
  let counter = ref 0 in
  let unique () =
    let u = !counter in
    counter := u + 1;
    u in

  (* Create the set of vertices *)
  let vertex_of_instr instr =
    G.V.create (unique (), instr) in
  let vertices = List.map vertex_of_instr instrs in
  List.iter (G.add_vertex g) vertices;

  (* Hash table to let us look up vertices by their label *)
  let vertices_by_label = Hashtbl.create 10 in

  (* Populate the hash table *)
  let populate_table vertex =
    let _, code = G.V.label vertex in
    match code with (* Get vertex contents *)
    | `Label lbl -> Hashtbl.add vertices_by_label lbl vertex
    | _ -> () in
  List.iter populate_table vertices;

  let populate_edges idx vertex =
    (* Get the contents of the vertex *)
    let _, instr = G.V.label vertex in

    (* Adds the default fallthrough edge, i.e. an edge that
       continues to the next instruction *)
    let add_fallthrough lbl =
      (* If there's an edge that comes next in the vertex list
         then add it *)
      match List.nth_opt vertices (idx + 1) with
      | Some next ->
        let edge = G.E.create vertex lbl next in
        G.add_edge_e g edge
      | None -> () in
    (* We base the edges on the last instruction in a block since it's
       the one that edges are "coming" from *)
    match instr with
    (* For gotos, we always jump so the "fallthrough" edge
       becomes the target of the jump. However, if the goto
       causes the next line to be unreachable, it create an
       "unreachable" edge to it *)
    | `J lbl ->
      let target = Hashtbl.find vertices_by_label lbl in
      let edge = G.E.create vertex `Jump target in
      G.add_edge_e g edge
    (* For branches, there are always two edges: the next instruction
       (fallthrough) and the target of the branch (whenever the condition
       is true) *)
    | `Beq (_, _, lbl)
    | `Bne (_, _, lbl)
    | `Bltz (_, lbl)
    | `Bgtz (_, lbl)
    | `Bgez (_, lbl)
    | `Blez (_, lbl) ->
      let target = Hashtbl.find vertices_by_label lbl in
      let edge = G.E.create vertex `Branch target in
      G.add_edge_e g edge;
      add_fallthrough `Fallthrough
    (* Return has no outgoing edges, since it marks the end of the
       procedure *)
    | `Jr _ -> ()
    (* For all other instructions, we only fallthrough into the next
       instruction *)
    | _ ->
      add_fallthrough `Fallthrough in
  List.iteri populate_edges vertices;

  g, List.hd vertices

(* Get the first instruction in a program by its vertex number *)
let first_instr g =
  let found =
    G.fold_vertex begin fun v acc ->
      let v_id, _ = v in
      match acc with
      | Some (old_id, _) when v_id < old_id -> Some v
      | Some (_, _) -> acc
      | None -> Some v
    end g None in
  match found with
  | Some init -> init
  | None -> failwith "Could not find a first instruction for the program"

let hashtbl_of_cfg g =
  let hashtbl = Hashtbl.create (G.nb_vertex g) in
  let add_mapping v =
    let id, _ = v in
    Hashtbl.add hashtbl id v in
  G.iter_vertex add_mapping g;
  hashtbl
