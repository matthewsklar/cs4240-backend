open Graph

module Vertex = struct
  type t = string

  let compare = compare
  let equal = (=)
  let hash = Hashtbl.hash
end

module G =
  Imperative.Graph.Concrete(Vertex)

module Color = Coloring.Make(G)

let build vars sets =
  let open Dataflow in
  let rig = G.create () in

  VSet.iter begin fun var ->
    G.add_vertex rig var
  end vars;

  let rec permute2 seen = function
    | [] -> []
    | curr::unseen ->
      let curr_combos = List.map (fun snd -> (curr, snd)) (seen@unseen)
      and other_permutations = permute2 (curr::seen) unseen in
      curr_combos@other_permutations in

  VMap.iter begin fun _node entry ->
    (* Don't combine the in_set & out_set into one bigger set, because
       these are unique program points. If in_set = {A} and out_set = {B},
       these variables should not be treated as mutually exlcusive during
       coloring. *)
    List.iter begin fun (a, b) ->
      G.add_edge rig a b
    end (permute2 [] (VSet.elements entry.in_set));
    List.iter begin fun (a, b) ->
      G.add_edge rig a b
    end (permute2 [] (VSet.elements entry.out_set))
  end sets;

  rig
