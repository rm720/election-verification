(*
  Compiles the crypto example by evaluation inside the logic of HOL
*)
open preamble compilationLib cryptoProgTheory

val _ = new_theory "cryptoCompile"

val crypto_compiled = save_thm("crypto_compiled",
  compile_x64 "crypto" crypto_prog_def);

val _ = export_theory ();
