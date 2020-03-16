module Ir = Passes.MipsMem

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
