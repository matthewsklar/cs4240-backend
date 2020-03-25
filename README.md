# cs4240-backend
Compiler backend that generates MIPS32 assembly code from Tiger-IR.

Uses instruction selection and register allocation.

# Running
To build the backend compiler, run
```
$ dune build src/codegen.exe
```
To run it, run
```
$ dune exec src/codegen.exe -- -i <input file> -o <output file> --allocator [Naive, Graph]
```