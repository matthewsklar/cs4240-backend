module%language M = struct
  type expr = [ `Print of string ]
end

let () =
  print_endline "Hello"
