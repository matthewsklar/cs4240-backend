let example_program =
  let open TigerIR.Ir in
  let body =
    [ Assign ("__x", Int 0);
      ArrayAssign ("__xs", 3, Ident "__x");
      Assign ("__n", Ident "__x");
      Label "start";
      ArrayStore (Ident "__n", "__xs", Ident "__n");
      Add ("__n", Ident "__n", Int 1);
      Brgeq ("start", Ident "__n", Int 3);
      Callr ("__x", "do_stuff", [Ident "__x"; Ident "__n"; Int 3; Int 6; Int 7]) ] in
  let data = { floatList = []; intList = [
    Scalar "__x";
    Array ("__xs", 3);
    Scalar "__n"
  ] } in
  {
    name = "example";
    returnType = None;
    params = [];
    data;
    body
  }

let () =
  let allocator fn body =
    let (allocs, new_spills) = Alloc.naive fn body in
    (Alloc.apply_allocations allocs body, new_spills) in
  print_endline (Isel.compile ~allocator example_program)
