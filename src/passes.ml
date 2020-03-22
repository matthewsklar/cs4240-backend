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
  | ArrayStore (x, y, z) -> `ArrayStore (of_op x, y, of_op z)
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

module%language MipsCond = struct
  include MipsArith
  type instr = {
    add: [
      | `J of label
      | `Beq of string * string * label
      | `Bne of string * string * label
      | `Bgtz of string * label
      | `Bltz of string * label
      | `Bgez of string * label
      | `Blez of string * label
    ];
    del: [
      | `Goto of label
      | `Breq of label * op * op
      | `Brneq of label * op * op
      | `Brgt of label * op * op
      | `Brlt of label * op * op
      | `Brgeq of label * op * op
      | `Brleq of label * op * op
    ]
  }
end

module%language MipsMem = struct
  include MipsCond
  type instr = {
    add: [
      | `Lw of string * int * string (* lw dst, off(src) *)
      | `Sw of string * int * string (* sw src, off(dst) *)
      | `Sll of string * string * int
    ];
    del: [
      | `ArrayStore of op * string * op
      | `ArrayLoad of string * string * op
      | `ArrayAssign of string * int * op
    ]
  }
end

module%language MipsCall = struct
  include MipsMem
  type instr = {
    add: [
      | `Jr of string
      | `Jal of string
      | `Push of string
      | `Pop of string
    ];
    del: [
      | `Return of op
      | `Call of string * op list
      | `Callr of string * string * op list
    ]
  }
end

module%language MipsLiStack = struct
  include MipsCall
  type instr = {
    del: [
      | `Li of string * int
      | `Push of string
      | `Pop of string
    ];
    add: [ `Lui of string * int ]
  }
end

module%language MipsFlat = struct
  include MipsLiStack
  type instr = {
    del: [ `Block of instr list ]
  }
end

let use_op op instrs = match op with
  | `Int i ->
    let v0 = uniq () in
    (`Li (v0, i))::(instrs v0)
  | `Ident id ->
    instrs id

let[@pass NestedIr => MipsArith] translate_arith =
  [%passes
    let[@entry] rec instr = function
      | `Assign (dst, `Ident src) -> `Addi (dst, src, 0)
      | `Assign (dst, `Int imm) -> `Li (dst, imm)

      | `Add (dst, `Ident x, `Ident y) -> `Add (dst, x, y)
      | `Add (dst, `Int i, `Ident x) -> `Addi (dst, x, i)
      | `Add (dst, x, `Int y) ->
        `Block (use_op x (fun x -> [`Addi (dst, x, y)]))
      
      | `Sub (dst, i, `Ident x) ->
        `Block (use_op i (fun i -> [`Sub (dst, i, x)]))
      | `Sub (dst, `Ident x, `Int i) -> `Subi (dst, x, i)
      | `Sub (dst, x, y) ->
        `Block (use_op x (fun x -> (use_op y (fun y -> [`Sub (dst, x, y)]))))
      
      | `Mult (dst, x, y) ->
        `Block (use_op x (fun x ->
                use_op y (fun y ->
                [ `Mult (x, y);
                  `Mflo dst ])))
      
      | `Div (dst, x, y) ->
        `Block (use_op x (fun x ->
                use_op y (fun y ->
                [ `Div (x, y);
                  `Mflo dst ])))
      
      | `And (dst, `Ident x, `Ident y) -> `And (dst, x, y)
      | `And (dst, `Int i, `Ident x) -> `Andi (dst, x, i)
      | `And (dst, `Ident x, `Int i) -> `Andi (dst, x, i)
      | `And (dst, `Int x, `Int y) ->
        let v0 = uniq () in
        `Block [ `Li (v0, x);
                 `Andi (dst, v0, y) ]

      | `Or (dst, `Ident x, `Ident y) -> `Or (dst, x, y)
      | `Or (dst, `Int i, `Ident x) -> `Ori (dst, x, i)
      | `Or (dst, `Ident x, `Int i) -> `Ori (dst, x, i)
      | `Or (dst, `Int x, `Int y) ->
        let v0 = uniq () in
        `Block [ `Li (v0, x);
                 `Ori (dst, v0, y) ]
  ]

let[@pass MipsArith => MipsCond] translate_cond =
  [%passes
    let[@entry] rec instr = function
      | `Goto lbl -> `J lbl
      | `Breq (lbl, x, y) ->
        `Block (use_op x (fun x ->
                use_op y (fun y ->
                [`Beq (x, y, lbl)])))
      | `Brneq (lbl, x, y) ->
        `Block (use_op x (fun x ->
                use_op y (fun y ->
                [`Bne (x, y, lbl)])))
      | `Brgt (lbl, x, y) ->
        let v0 = uniq () in
        let bgtz = use_op x (fun x -> use_op y (fun y -> [
          `Sub (v0, x, y);
          `Bgtz (v0, lbl)
        ])) in
        `Block bgtz
      | `Brlt (lbl, x, y) ->
        let v0 = uniq () in
        let bltz = use_op x (fun x -> use_op y (fun y -> [
          `Sub (v0, x, y);
          `Bltz (v0, lbl)
        ])) in
        `Block bltz
      | `Brgeq (lbl, x, y) ->
        let v0 = uniq () in
        let bgez = use_op x (fun x -> use_op y (fun y -> [
          `Sub (v0, x, y);
          `Bgez (v0, lbl)
        ])) in
        `Block bgez
      | `Brleq (lbl, x, y) ->
        let v0 = uniq () in
        let blez = use_op x (fun x -> use_op y (fun y -> [
          `Sub (v0, x, y);
          `Blez (v0, lbl)
        ])) in
        `Block blez
  ]

let[@pass MipsCond => MipsMem] translate_array =
  [%passes
    let[@entry] rec instr = function
      | `ArrayAssign (dst, len, value) ->
        `Block (use_op value (fun value ->
          List.init len (fun i -> `Sw (value, 4 * i, dst))))
      | `ArrayLoad (dst, arr, `Int offset) ->
        `Lw (dst, 4 * offset, arr)
      | `ArrayLoad (dst, arr, `Ident offset) ->
        let v0 = uniq () in
        `Block [ `Sll (v0, offset, 2);
                 `Add (v0, arr, v0); (* arr + offset*4 *)
                 `Lw (dst, 0, v0) ]
      | `ArrayStore (src, arr, `Int offset) ->
        `Block (use_op src (fun src -> [`Sw (src, 4 * offset, arr)]))
      | `ArrayStore (src, arr, `Ident offset) ->
        let v0 = uniq () in
        `Block (use_op src (fun src ->
                [ `Sll (v0, offset, 2);
                  `Add (v0, arr, v0); (* arr + offset*4 *)
                  `Sw (src, 0, v0) ]))
  ]

(* Note: must save $a0..$a3 before any calls *)
let rec push_args ?(regs=["a0"; "a1"; "a2"; "a3"]) args out = match regs, args with
  | _, [] -> out
  | [], (`Int i)::rest ->
    push_args ~regs:[] rest ([ `Li ("a0", i);   (* Safe to use $a0 b/c this is before *)
                               `Push "a0" ]@out)
  | reg::regs, (`Int i)::rest ->
    push_args ~regs rest ((`Li (reg, i))::out)
  | [], (`Ident id)::rest ->
    push_args ~regs:[] rest ((`Push id)::out)
  | reg::regs, (`Ident id)::rest ->
    push_args ~regs rest ((`Addi (reg, id, 0))::out)

(* FIXME: Flesh out stack building *)
let[@pass MipsMem => MipsCall] translate_call =
  [%passes
    let[@entry] rec instr = function
      (* Sidenote: return w/out value is implicit in TigerIR: must return in epilog *)
      | `Return (`Ident reg) ->
        `Block [ `Addi ("v0", reg, 0);  (* mov $v0, $reg *)
                 `Lw ("ra", -4, "fp");  (* pop $ra *)
                 `Addi ("sp", "fp", 4); (* restore $sp *)
                 `Lw ("fp", 0, "fp");   (* restore $fp *)
                 `Jr "ra" ]             (* ret *)
      | `Return (`Int i) ->
        `Block [ `Li ("v0", i);
                 `Lw ("ra", -4, "fp");
                 `Addi ("sp", "fp", 4);
                 `Lw ("fp", 0, "fp");
                 `Jr "ra" ]
      (* FIXME: Use syscall instruction for built-in SPIM functions (or link in wrappers) *)
      | `Call (fn, ops) ->
        `Block (push_args ops [ `Jal fn ])
      | `Callr (res, fn, ops) ->
        `Block (push_args ops [ `Jal fn;
                                `Addi (res, "v0", 0)])
  ]

let[@pass MipsCall => MipsLiStack] remove_pseudos =
  [%passes
    let[@entry] rec instr = function
      | `Li (reg, imm) ->
        `Block [ `Lui (reg, imm lsr 16);             (* reg = imm >> 16 *)
                 `Addi (reg, reg, imm land 0xFFFF) ] (* reg += imm & 0xFFFF *)
      | `Push reg -> (* Optimization: we can fuse multiple pushes/pops into 1 add *)
        `Block [ `Addi ("sp", "sp", -4);
                 `Sw (reg, 0, "sp") ]
      | `Pop reg ->
        `Block [ `Lw (reg, 0, "sp");
                 `Addi ("sp", "sp", 4) ]
  ]

let rec flatten: MipsLiStack.instr list -> MipsFlat.instr list = function
  | [] -> []
  | (`Block parts)::rest ->
    (flatten parts)@(flatten rest)
  | (#MipsFlat.instr as instr)::rest -> instr::(flatten rest)

let build_stack ~new_spills {intList; _} instrs =
  let var_alloc = List.map (function Scalar _ -> 4 | Array (_, n) -> n * 4) intList
                  |> List.fold_left (+) 0 in
  [ `Sw ("fp", -4, "sp");    (* push $fp *)
    `Addi ("sp", "sp", -4);
    `Addi ("fp", "sp", 0);   (* mov $fp, $sp*)
    `Sw ("ra", -4, "sp");    (* push $ra *)
    (* Allocate room for local variables & spilled variables (don't save $s_ reg's) *)
    `Addi ("sp", "sp", -4 - var_alloc - new_spills);
  ] @ instrs @ (* prolog, instrs, epilog *)
  [ `Lw ("ra", -4, "fp");  (* pop $ra *)
    `Addi ("sp", "fp", 4); (* restore $sp *)
    `Lw ("fp", 0, "fp");   (* restore $fp *)
    `Jr "ra" ]             (* ret *)

let rec to_string: MipsFlat.instr list -> string = function
  | [] -> ""
  | (`Label lbl)::rest ->
    Printf.sprintf "%s:\n%s" lbl (to_string rest)
  | (`Add (dst, rx, ry))::rest ->
    Printf.sprintf "\tadd $%s, $%s, $%s\n%s" dst rx ry (to_string rest)
  | (`Addi (dst, rx, imm))::rest ->
    Printf.sprintf "\taddi $%s, $%s, %d\n%s" dst rx imm (to_string rest)
  | (`Sub (dst, rx, ry))::rest ->
    Printf.sprintf "\tsub $%s, $%s, $%s\n%s" dst rx ry (to_string rest)
  | (`Subi (dst, rx, imm))::rest ->
    Printf.sprintf "\tsubi $%s, $%s, %d\n%s" dst rx imm (to_string rest)
  | (`Mult (rx, ry))::rest ->
    Printf.sprintf "\tmult $%s, $%s\n%s" rx ry (to_string rest)
  | (`Div (rx, ry))::rest ->
    Printf.sprintf "\tdiv $%s, $%s\n%s" rx ry (to_string rest)
  | (`Mflo dst)::rest ->
    Printf.sprintf "\tmflo $%s\n%s" dst (to_string rest)
  | (`And (dst, rx, ry))::rest ->
    Printf.sprintf "\tand $%s, $%s, $%s\n%s" dst rx ry (to_string rest)
  | (`Andi (dst, rx, imm))::rest ->
    Printf.sprintf "\tandi $%s, $%s, %d\n%s" dst rx imm (to_string rest)
  | (`Or (dst, rx, ry))::rest ->
    Printf.sprintf "\tor $%s, $%s, $%s\n%s" dst rx ry (to_string rest)
  | (`Ori (dst, rx, imm))::rest ->
    Printf.sprintf "\tori $%s, $%s, %d\n%s" dst rx imm (to_string rest)
  | (`Sll (dst, rx, imm))::rest ->
    Printf.sprintf "\tsll $%s, $%s, %d\n%s" dst rx imm (to_string rest)
  | (`J lbl)::rest ->
    Printf.sprintf "\tj %s\n%s" lbl (to_string rest)
  | (`Jr reg)::rest ->
    Printf.sprintf "\tjr $%s\n%s" reg (to_string rest)
  | (`Jal lbl)::rest ->
    Printf.sprintf "\tjal %s\n%s" lbl (to_string rest)
  | (`Beq (rx, ry, lbl))::rest ->
    Printf.sprintf "\tbeq $%s, $%s, %s\n%s" rx ry lbl (to_string rest)
  | (`Bne (rx, ry, lbl))::rest ->
    Printf.sprintf "\tbne $%s, $%s, %s\n%s" rx ry lbl (to_string rest)
  | (`Blez (rx, lbl))::rest ->
    Printf.sprintf "\tblez $%s, %s\n%s" rx lbl (to_string rest)
  | (`Bgez (rx, lbl))::rest ->
    Printf.sprintf "\tbgez $%s, %s\n%s" rx lbl (to_string rest)
  | (`Bltz (rx, lbl))::rest ->
    Printf.sprintf "\tbltz $%s, %s\n%s" rx lbl (to_string rest)
  | (`Bgtz (rx, lbl))::rest ->
    Printf.sprintf "\tbgtz $%s, %s\n%s" rx lbl (to_string rest)
  | (`Lw (dst, off, reg))::rest ->
    Printf.sprintf "\tlw $%s, %d($%s)\n%s" dst off reg (to_string rest)
  | (`Sw (src, off, reg))::rest ->
    Printf.sprintf "\tsw $%s, %d($%s)\n%s" src off reg (to_string rest)
  | (`Lui (dst, imm))::rest ->
    Printf.sprintf "\tlui $%s, %d\n%s" dst imm (to_string rest)

let compile ~allocator fn =
  let instrs = fn.body in
  let instrs' =
    instrs |> List.map of_ir
           |> List.map translate_arith
           |> List.map translate_cond
           |> List.map translate_array
           |> List.map translate_call
           |> List.map remove_pseudos
           |> flatten in
  let (code, new_spills) = allocator fn instrs' in
  (`Label fn.name)::(build_stack ~new_spills fn.data code) |> to_string
