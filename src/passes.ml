open TigerIR.Ir

type op = [
  | `Int of int
  | `Ident of string
]

let of_op = function
  | Int i -> `Int i
  | Float _ -> failwith "Floats aren't implemented yet"
  | Ident i -> `Ident i

let of_ir = function
  | Label x -> `Label x
  | Assign (x, y) -> `Assign (x, of_op y)
  | Add (x, y, z) -> `Add (x, of_op y, of_op z)
  | Sub (x, y, z) -> `Sub (x, of_op y, of_op z)
  | Mult (x, y, z) -> `Mult (x, of_op y, of_op z)
  | Div (x, y, z) -> `Div (x, of_op y, of_op z)
  | And (x, y, z) -> `And (x, of_op y, of_op z)
  | Or (x, y, z) -> `Or (x, of_op y, of_op z)
  | Goto x -> `Goto x
  | Breq (x, y, z) -> `Breq (x, of_op y, of_op z)
  | Brneq (x, y, z) -> `Brneq (x, of_op y, of_op z)
  | Brlt (x, y, z) -> `Brlt (x, of_op y, of_op z)
  | Brgt (x, y, z) -> `Brgt (x, of_op y, of_op z)
  | Brleq (x, y, z) -> `Brleq (x, of_op y, of_op z)
  | Brgeq (x, y, z) -> `Brgeq (x, of_op y, of_op z)
  | Return x -> `Return (of_op x)
  | Call (x, y) -> `Call (x, List.map of_op y)
  | Callr (x, y, z) -> `Callr (x, y, List.map of_op z)
  | ArrayStore (x, y, z) -> `ArrayStore (x, y, of_op z)
  | ArrayLoad (x, y, z) -> `ArrayLoad (x, y, of_op z)
  | ArrayAssign (x, y, z) -> `ArrayAssign (x, y, of_op z)

let uniq =
  let num = ref 0 in
  fun () ->
    let n = !num in
    num := n + 1;
    Printf.sprintf "__v%d" n

module%language NestedIr = struct
  type instr = [
    | `Label of label
    | `Assign of string * op
    | `Add of string * op * op
    | `Sub of string * op * op
    | `Mult of string * op * op
    | `Div of string * op * op
    | `And of string * op * op
    | `Or of string * op * op
    | `Goto of label
    | `Breq of label * op * op
    | `Brneq of label * op * op
    | `Brlt of label * op * op
    | `Brgt of label * op * op
    | `Brgeq of label * op * op
    | `Brleq of label * op * op
    | `Return of op
    | `Call of string * op list
    | `Callr of string * string * op list
    | `ArrayStore of op * string * op
    | `ArrayLoad of string * string * op
    | `ArrayAssign of string * int * op
    | `Block of instr list
  ]
end

module%language MipsArith = struct
  include NestedIr
  type instr = {
    add: [
      | `Li of string * int
      | `Move of string * string
      | `Add of string * string * string
      | `Addi of string * string * int
      | `Sub of string * string * string
      | `Subi of string * string * int
      | `Mult of string * string
      | `Div of string * string
      | `And of string * string * string
      | `Andi of string * string * int
      | `Or of string * string * string
      | `Ori of string * string * int
      | `Mfhi of string
      | `Mflo of string
    ];
    del: [
      | `Assign of string * op
      | `Add of string * op * op
      | `Sub of string * op * op
      | `Mult of string * op * op
      | `Div of string * op * op
      | `And of string * op * op
      | `Or of string * op * op
    ]
  }
end

let[@pass NestedIr => MipsArith] translate_arith =
  [%passes
    let[@entry] rec instr = function
      | `Assign (dst, `Ident src) -> `Move (dst, src)
      | `Assign (dst, `Int imm) -> `Li (dst, imm)

      | `Add (dst, `Ident x, `Ident y) -> `Add (dst, x, y)
      | `Add (dst, `Int i, `Ident x) -> `Addi (dst, x, i)
      | `Add (dst, `Ident x, `Int i) -> `Addi (dst, x, i)
      | `Add (dst, `Int x, `Int y) ->
        let v0 = uniq () in
        `Block [
          `Li (v0, x);
          `Addi (dst, v0, y)
        ]
      
      | `Sub (dst, `Ident x, `Ident y) -> `Sub (dst, x, y)
      | `Sub (dst, `Int i, `Ident x) ->
        let v0 = uniq () in
        `Block [
          `Li (v0, i);
          `Sub (dst, v0, x)
        ]
      | `Sub (dst, `Ident x, `Int i) -> `Subi (dst, x, i)
      | `Sub (dst, `Int x, `Int y) ->
        let v0 = uniq () in
        `Block [
          `Li (v0, x);
          `Subi (dst, v0, y)
        ]
      
      | `Mult (dst, `Ident x, `Ident y) ->
        `Block [
          `Mult (x, y);
          `Mflo dst
        ]
      | `Mult (dst, `Ident x, `Int y) ->
        let v0 = uniq () in
        `Block [
          `Li (v0, y);
          `Mult (x, v0);
          `Mflo dst
        ]
      | `Mult (dst, `Int x, `Ident y) ->
        let v0 = uniq () in
        `Block [
          `Li (v0, x);
          `Mult (v0, y);
          `Mflo dst
        ]
      | `Mult (dst, `Int x, `Int y) ->
        let v0 = uniq () and v1 = uniq () in
        `Block [
          `Li (v0, x);
          `Li (v1, y);
          `Mult (v0, v1);
          `Mflo dst
        ]
      
      | `Div (dst, `Ident x, `Ident y) ->
        `Block [
          `Div (x, y);
          `Mflo dst
        ]
      | `Div (dst, `Ident x, `Int y) ->
        let v0 = uniq () in
        `Block [
          `Li (v0, y);
          `Div (x, v0);
          `Mflo dst
        ]
      | `Div (dst, `Int x, `Ident y) ->
        let v0 = uniq () in
        `Block [
          `Li (v0, x);
          `Div (v0, y);
          `Mflo dst
        ]
      | `Div (dst, `Int x, `Int y) ->
        let v0 = uniq () and v1 = uniq () in
        `Block [
          `Li (v0, x);
          `Li (v1, y);
          `Div (v0, v1);
          `Mflo dst
        ]
      
      | `And (dst, `Ident x, `Ident y) -> `And (dst, x, y)
      | `And (dst, `Int i, `Ident x) -> `Andi (dst, x, i)
      | `And (dst, `Ident x, `Int i) -> `Andi (dst, x, i)
      | `And (dst, `Int x, `Int y) ->
        let v0 = uniq () in
        `Block [
          `Li (v0, x);
          `Andi (dst, v0, y)
        ]

      | `Or (dst, `Ident x, `Ident y) -> `Or (dst, x, y)
      | `Or (dst, `Int i, `Ident x) -> `Ori (dst, x, i)
      | `Or (dst, `Ident x, `Int i) -> `Ori (dst, x, i)
      | `Or (dst, `Int x, `Int y) ->
        let v0 = uniq () in
        `Block [
          `Li (v0, x);
          `Ori (dst, v0, y)
        ]
  ]
