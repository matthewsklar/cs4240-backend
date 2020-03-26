open Passes
open TigerIR.Ir

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

let load_params params body =
  let rec drop n list = match n, list with
    | _, [] -> []
    | 0, list -> list
    | n, _::rest -> drop (n - 1) rest in
  (* Only the last 4 params are on the stack *)
  let stack_params = drop 4 params in
  let param_sizes =
    List.map (function (name, (TyInt | TyFloat)) -> (name, 4) | (name, TyArray (_, n)) -> (name, n * 4)) stack_params in
  let program, _ =
    List.fold_right begin fun (name, size) (program, size_acc) ->
      let size' = size + size_acc in
      let load = `Lw (name, size', "$fp") in
      (load::program, size')
    end param_sizes (body, 0) in
  program

let build_stack ~new_spills {intList; _} instrs =
  let var_alloc = List.map (function Scalar _ -> 4 | Array (_, n) -> n * 4) intList
                  |> List.fold_left (+) 0 in
  [ `Sw ("$fp", -4, "$sp");    (* push $fp *)
    `Addi ("$sp", "$sp", -4);
    `Addi ("$fp", "$sp", 0);   (* mov $fp, $sp*)
    `Sw ("$ra", -4, "$sp");    (* push $ra *)
    `Sw ("$s0", -8, "$sp");
    `Sw ("$s1", -12, "$sp");
    `Sw ("$s2", -16, "$sp");
    `Sw ("$s3", -20, "$sp");
    `Sw ("$s4", -24, "$sp");
    `Sw ("$s5", -28, "$sp");
    `Sw ("$s6", -32, "$sp");
    `Sw ("$s7", -36, "$sp");
    (* Allocate room for local variables & spilled variables (don't save $s_ reg's) *)
    `Addi ("$sp", "$sp", -36 - var_alloc - new_spills);
  ] @ instrs @ (* prolog, instrs, epilog *)
  [ `Lw ("$s7", -36, "$sp");
    `Lw ("$s6", -32, "$sp");
    `Lw ("$s5", -28, "$sp");
    `Lw ("$s4", -24, "$sp");
    `Lw ("$s3", -20, "$sp");
    `Lw ("$s2", -16, "$sp");
    `Lw ("$s1", -12, "$sp");
    `Lw ("$s0", -8, "$sp");
    `Lw ("$ra", -4, "$fp");  (* pop $ra *)
    `Addi ("$sp", "$fp", 4); (* restore $sp *)
    `Lw ("$fp", 0, "$fp");   (* restore $fp *)
    `Jr "$ra" ]              (* ret *)

let rec to_string: MipsFlat.instr list -> string = function
  | [] -> ""
  | (`Label lbl)::rest ->
    Printf.sprintf "%s:\n%s" lbl (to_string rest)
  | (`Add (dst, rx, ry))::rest ->
    Printf.sprintf "\tadd %s, %s, %s\n%s" dst rx ry (to_string rest)
  | (`Addi (dst, rx, imm))::rest ->
    Printf.sprintf "\taddi %s, %s, %d\n%s" dst rx imm (to_string rest)
  | (`Sub (dst, rx, ry))::rest ->
    Printf.sprintf "\tsub %s, %s, %s\n%s" dst rx ry (to_string rest)
  | (`Mult (rx, ry))::rest ->
    Printf.sprintf "\tmult %s, %s\n%s" rx ry (to_string rest)
  | (`Div (rx, ry))::rest ->
    Printf.sprintf "\tdiv %s, %s\n%s" rx ry (to_string rest)
  | (`Mflo dst)::rest ->
    Printf.sprintf "\tmflo %s\n%s" dst (to_string rest)
  | (`And (dst, rx, ry))::rest ->
    Printf.sprintf "\tand %s, %s, %s\n%s" dst rx ry (to_string rest)
  | (`Andi (dst, rx, imm))::rest ->
    Printf.sprintf "\tandi %s, %s, %d\n%s" dst rx imm (to_string rest)
  | (`Or (dst, rx, ry))::rest ->
    Printf.sprintf "\tor %s, %s, %s\n%s" dst rx ry (to_string rest)
  | (`Ori (dst, rx, imm))::rest ->
    Printf.sprintf "\tori %s, %s, %d\n%s" dst rx imm (to_string rest)
  | (`Sll (dst, rx, imm))::rest ->
    Printf.sprintf "\tsll %s, %s, %d\n%s" dst rx imm (to_string rest)
  | (`J lbl)::rest ->
    Printf.sprintf "\tj %s\n%s" lbl (to_string rest)
  | (`Jr reg)::rest ->
    Printf.sprintf "\tjr %s\n%s" reg (to_string rest)
  | (`Jal lbl)::rest ->
    Printf.sprintf "\tjal %s\n%s" lbl (to_string rest)
  | (`Beq (rx, ry, lbl))::rest ->
    Printf.sprintf "\tbeq %s, %s, %s\n%s" rx ry lbl (to_string rest)
  | (`Bne (rx, ry, lbl))::rest ->
    Printf.sprintf "\tbne %s, %s, %s\n%s" rx ry lbl (to_string rest)
  | (`Blez (rx, lbl))::rest ->
    Printf.sprintf "\tblez %s, %s\n%s" rx lbl (to_string rest)
  | (`Bgez (rx, lbl))::rest ->
    Printf.sprintf "\tbgez %s, %s\n%s" rx lbl (to_string rest)
  | (`Bltz (rx, lbl))::rest ->
    Printf.sprintf "\tbltz %s, %s\n%s" rx lbl (to_string rest)
  | (`Bgtz (rx, lbl))::rest ->
    Printf.sprintf "\tbgtz %s, %s\n%s" rx lbl (to_string rest)
  | (`Lw (dst, off, reg))::rest ->
    Printf.sprintf "\tlw %s, %d(%s)\n%s" dst off reg (to_string rest)
  | (`Sw (src, off, reg))::rest ->
    Printf.sprintf "\tsw %s, %d(%s)\n%s" src off reg (to_string rest)
  | (`Lui (dst, imm))::rest ->
    Printf.sprintf "\tlui %s, %d\n%s" dst imm (to_string rest)

let compile_function ~allocator fn =
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

let compile_program ~allocator prog =
  (* `.set noat` disables the SPIM error when using the $at register *)
  let prog_header = ".set noat\n.globl main" in
  List.fold_left (fun output fn -> output ^ "\n" ^ compile_function ~allocator fn) prog_header prog
