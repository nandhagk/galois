open Core

let () =
  Command_unix.run
    (Command.group
       ~summary:"Audit and measure Galois"
       [ "check", Galois_check.Check.command; "bench", Galois_check.Bench.command ])
;;
