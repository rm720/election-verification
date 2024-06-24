
(* ------------------------------------------------------------------------- *)
(* Pedersen Commitment Scheme -- Binding and Hiding Properties               *)
(* ------------------------------------------------------------------------- *)


(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "instancePlay";

(* ------------------------------------------------------------------------- *)

open jcLib;
open monoidTheory;
open monoidOrderTheory;
open groupTheory;
open groupOrderTheory;
open groupCyclicTheory;
open groupInstancesTheory;
(*
open ringTheory;
open ringInstancesTheory;
open fieldTheory;
open fieldInstancesTheory;
*)
open arithmeticTheory;
open congruencesTheory;
open helperNumTheory; 
open dividesTheory;
open mlstringTheory;
open mlintTheory;

open pedersenCommitmentTheory;


(* h^d * k^m *)
(*
Definition commit_def:
  commit (g: 'a group) (h: 'a)  d k m = g.op (monoid_exp g h d) (monoid_exp g k m)
End                                          

Definition verify_def:
  verify (g: 'a group) (h: 'a) c d k m ⇔ commit g h d k m = c
End
*)

val _ = temp_overload_on("Z*", ``Zstar``);

(*assuming p is prime, and h mod p, k mod p  are generators*)
Overload z_commit = “λ p. commit (Z* p)”

Theorem z_commit_thm:
  (*Assumptions*)
  h ≠ 0 ∧ h < p ∧ k ≠ 0 ∧ k < p ∧ prime p ⇒
  z_commit p h d k m = (h**d * k**m) MOD p
Proof
  simp[commit_def, FUN_EQ_THM, Zstar_exp, Zstar_carrier_alt]
QED

Definition z_code_def:
  z_code p a b c d = if p = 0 ∨ a MOD p = 0 ∨ c MOD p = 0 then 0 else (a**b * c**d) MOD p
End

Definition z_code_string_def:
  z_code_string p a b c d = mlint$num_to_str (z_code p a b c d) ^ strlit"\n"
End
      
Theorem crypto_math_spec:
  prime p ∧ a MOD p ≠ 0 ∧ c MOD p ≠ 0 ⇒ z_code p a b c d  = z_commit p (a MOD p) b (c MOD p) d
Proof
  rw[z_code_def, commit_def] >>
  simp[Zstar_exp,  Zstar_element]
QED
        
val _ = export_theory();        
                                  
