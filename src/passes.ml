open TigerIR.Ir

type op = [
  | `Int of int
  | `Ident of string
]

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
      | `Sub (dst, `Ident x, `Int i) -> `Addi (dst, x, -i)
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

let[@pass MipsArith => MipsCond] translate_cond fn_name =
  [%passes
    let[@entry] rec instr = function
      | `Label lbl -> `Label (fn_name ^ "_" ^ lbl)
      | `Goto lbl -> `J (fn_name ^ "_" ^ lbl)
      | `Breq (lbl, x, y) ->
        `Block (use_op x (fun x ->
                use_op y (fun y ->
                [`Beq (x, y, fn_name ^ "_" ^ lbl)])))
      | `Brneq (lbl, x, y) ->
        `Block (use_op x (fun x ->
                use_op y (fun y ->
                [`Bne (x, y, fn_name ^ "_" ^ lbl)])))
      | `Brgt (lbl, x, y) ->
        let v0 = uniq () in
        let bgtz = use_op x (fun x -> use_op y (fun y -> [
          `Sub (v0, x, y);
          `Bgtz (v0, fn_name ^ "_" ^ lbl)
        ])) in
        `Block bgtz
      | `Brlt (lbl, x, y) ->
        let v0 = uniq () in
        let bltz = use_op x (fun x -> use_op y (fun y -> [
          `Sub (v0, x, y);
          `Bltz (v0, fn_name ^ "_" ^ lbl)
        ])) in
        `Block bltz
      | `Brgeq (lbl, x, y) ->
        let v0 = uniq () in
        let bgez = use_op x (fun x -> use_op y (fun y -> [
          `Sub (v0, x, y);
          `Bgez (v0, fn_name ^ "_" ^ lbl)
        ])) in
        `Block bgez
      | `Brleq (lbl, x, y) ->
        let v0 = uniq () in
        let blez = use_op x (fun x -> use_op y (fun y -> [
          `Sub (v0, x, y);
          `Blez (v0, fn_name ^ "_" ^ lbl)
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
let rec push_args ?(regs=["$a0"; "$a1"; "$a2"; "$a3"]) args out = match regs, args with
  | _, [] -> out
  | [], (`Int i)::rest ->
    push_args ~regs:[] rest ([ `Li ("$a0", i);   (* Safe to use $a0 b/c this is before *)
                               `Push "$a0" ]@out)
  | reg::regs, (`Int i)::rest ->
    push_args ~regs rest ((`Li (reg, i))::out)
  | [], (`Ident id)::rest ->
    push_args ~regs:[] rest ((`Push id)::out)
  | reg::regs, (`Ident id)::rest ->
    push_args ~regs rest ((`Addi (reg, id, 0))::out)

(* TODO: Optimization: don't emit all these saves if we don't need them *)
let save_regs = [
  `Sw ("$a0", -4, "$sp");
  `Sw ("$a1", -8, "$sp");
  `Sw ("$a2", -12, "$sp");
  `Sw ("$a3", -16, "$sp");
  `Sw ("$t0", -20, "$sp");
  `Sw ("$t1", -24, "$sp");
  `Sw ("$t2", -28, "$sp");
  `Sw ("$t3", -32, "$sp");
  `Sw ("$t4", -36, "$sp");
  `Sw ("$t5", -40, "$sp");
  `Sw ("$t6", -44, "$sp");
  `Sw ("$t7", -48, "$sp");
  `Sw ("$t8", -52, "$sp");
  `Sw ("$t9", -56, "$sp");
  `Addi ("$sp", "$sp", -56)
]

let restore_regs = [
  `Addi ("$sp", "$sp", 56);
  `Lw ("$t9", -56, "$sp");
  `Lw ("$t8", -52, "$sp");
  `Lw ("$t7", -48, "$sp");
  `Lw ("$t6", -44, "$sp");
  `Lw ("$t5", -40, "$sp");
  `Lw ("$t4", -36, "$sp");
  `Lw ("$t3", -32, "$sp");
  `Lw ("$t2", -28, "$sp");
  `Lw ("$t1", -24, "$sp");
  `Lw ("$t0", -20, "$sp");
  `Lw ("$a3", -16, "$sp");
  `Lw ("$a2", -12, "$sp");
  `Lw ("$a1", -8, "$sp");
  `Lw ("$a0", -4, "$sp")
]

(* FIXME: Flesh out stack building *)
let[@pass MipsMem => MipsCall] translate_call =
  [%passes
    let[@entry] rec instr = function
      (* Sidenote: return w/out value is implicit in TigerIR: must return in epilog *)
      | `Return (`Ident reg) ->
        `Block [ `Addi ("$v0", reg, 0);   (* mov $v0, $reg *)
                 `Lw ("$ra", -4, "$fp");  (* pop $ra *)
                 `Addi ("$sp", "$fp", 4); (* restore $sp *)
                 `Lw ("$fp", 0, "$fp");   (* restore $fp *)
                 `Jr "$ra" ]              (* ret *)
      | `Return (`Int i) ->
        `Block [ `Li ("$v0", i);
                 `Lw ("$ra", -4, "$fp");
                 `Addi ("$sp", "$fp", 4);
                 `Lw ("$fp", 0, "$fp");
                 `Jr "$ra" ]
      (* FIXME: Use syscall instruction for built-in SPIM functions (or link in wrappers) *)
      | `Call (fn, ops) ->
        `Block (save_regs @ push_args ops [ `Jal fn ] @ restore_regs)
      | `Callr (res, fn, ops) ->
        `Block (save_regs @
                push_args ops [ `Jal fn ] @ restore_regs @ [`Addi (res, "$v0", 0)])
  ]

let[@pass MipsCall => MipsLiStack] remove_pseudos =
  [%passes
    let[@entry] rec instr = function
      | `Li (reg, imm) ->
        `Block [ `Lui (reg, imm lsr 16);             (* reg = imm >> 16 *)
                 `Addi (reg, reg, imm land 0xFFFF) ] (* reg += imm & 0xFFFF *)
      | `Push reg -> (* Optimization: we can fuse multiple pushes/pops into 1 add *)
        `Block [ `Addi ("$sp", "$sp", -4);
                 `Sw (reg, 0, "$sp") ]
      | `Pop reg ->
        `Block [ `Lw (reg, 0, "$sp");
                 `Addi ("$sp", "$sp", 4) ]
  ]

let rec flatten: MipsLiStack.instr list -> MipsFlat.instr list = function
  | [] -> []
  | (`Block parts)::rest ->
    (flatten parts)@(flatten rest)
  | (#MipsFlat.instr as instr)::rest -> instr::(flatten rest)
