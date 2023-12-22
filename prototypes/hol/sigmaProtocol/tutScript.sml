open arithmeticTheory listTheory;

Definition divides_def:
  divides a b = ∃x. b = a*x
End

set_fixity "divides" (Infix(NONASSOC, 450));

Definition prime_def:
  prime p ⇔ p ≠ 1 ∧ ∀x. x divides p ⇒ (x=1) ∨ (x=p)
End

Theorem g:
  ∀x. x divides 0
Proof
  metis_tas[divides_def] >>
  qexists_tac ‘0’ >>
  rw[]
QED


