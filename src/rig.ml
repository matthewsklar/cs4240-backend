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
