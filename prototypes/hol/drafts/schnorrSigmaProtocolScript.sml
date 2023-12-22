
(* ------------------------------------------------------------------------- *)
(* -- Sigma Protocol -- *)
(* ------------------------------------------------------------------------- *)
(*
Holidays
16 dec - 2 Jan + 1 week in Jan Michael
26 dec - 7 Jan Thomas
print_match [] “n DIV m ≤ k”
print_match [] “_ * (_ / )”
print_match [] “$|/”
print_match [] “$MOD”  MOD_MULT_DIST
type_of “Schnorr_SP”
type_of “o” irule suffices_by
type_of_def “|/”
print_match [] “g.exp _ ( _ MOD _ )”
M-x replace-string
 ⊘
2298
\oslash
*)
       

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "schnorrSigmaProtocol";

open jcLib;
open monoidTheory;
open monoidOrderTheory;
open groupTheory;
open groupOrderTheory;
open groupCyclicTheory;
open groupInstancesTheory;
open ringTheory;
open ringInstancesTheory;
open fieldTheory;
open fieldInstancesTheory;
open arithmeticTheory;
open congruencesTheory;
open helperNumTheory; 
open dividesTheory;
open pairTheory;
open pred_setTheory;
open pedersenCommitmentTheory;
open sigmaProtocolTheory;

(*overload operation to avod ambiguity*)   
Overload "_0_" = “(GF q).sum.id”; 
Overload "_1_" = “(GF q).prod.id”; 

Overload "⊕" = “(GF q).sum.op”;
val _ = set_fixity "⊕" (Infixl 500); 
Overload "⊖" = “ring_sub (GF q)”;
val _ = set_fixity "⊖" (Infixl 500); 
Overload "⊗" = “(GF q).prod.op”;
val _ = set_fixity "⊗" (Infixl 600); 
Overload "⊘" = “field_div (GF q)”;
val _ = set_fixity "⊘" (Infixl 600);

    

(* ------------------------------------------------------------------------- *)
   


Definition Schnorr_SP_def:
  Schnorr_SP gr q =  <|Statements:= gr.carrier × gr.carrier;
                      Witnesses:= count q;
                      Relation:= (λ (s1, s2) w. monoid_exp gr s1 w = s2);
                      RandomCoins:= count q;
                      Commitments:= gr.carrier;
                      Challenges:= Zadd q;
                      Disjoint:= λ a b.  a ≠ b;
                      Responses:= count q;
                      Prover_0:= (λ (s1, s2) w r. monoid_exp gr s1 r);
                      Prover_1:= (λ (s1, s2) w r c e. r ⊕ e ⊗ w);
                      HonestVerifier:= (λ ((s1, s2), c, e, t). monoid_exp gr s1 t = gr.op c  (monoid_exp gr s2 e)); 
                      Extractor:= (λ t1 t2 e1 e2. (t1 ⊖ t2) ⊘ (e1 ⊖ e2));
                      Simulator:= (λ (s1, s2) t e. ((s1, s2), gr.op (monoid_exp gr s1 t) (gr.inv (monoid_exp gr s2 e)), e ,t));
                      SimulatorMap:= (λ (s1, s2) w e r.  r ⊕ e ⊗ w);
                      SimulatorMapInverse:=  (λ (s1, s2) w e t.  t ⊖ e ⊗ w); 
                     |> 
End

        
Theorem schnorr_wellformed_thm: 
  prime q ∧ cyclic g ∧ FINITE g.carrier ∧ (order g (cyclic_gen g) = q) ⇒ 
   WellFormed_SP (Schnorr_SP g q)
Proof
  simp[Schnorr_SP_def, WellFormed_SP_def, pairTheory.FORALL_PROD] >>
  rpt strip_tac >-

  (* proving Group (Zadd q) *)
  (‘0 < q’ by metis_tac[NOT_PRIME_0, NOT_ZERO] >>
  ‘Group (Zadd q)’by metis_tac[Zadd_group])>-

  (* proiving  r ⊕ e ⊗ w < q *)
  (‘Field (GF q)’by metis_tac[GF_field]>>
  ‘r ∈ (GF q).carrier ∧ e ∈ (GF q).carrier ∧ w ∈ (GF q).carrier’by metis_tac[GF_element]>>
  ‘r ⊕ e ⊗ w < q’by metis_tac[field_mult_element, field_add_element, GF_element])>-

  (*proving  (t1 ⊕ (GF q).sum.inv t2) ⊗ Inv (GF q) (e1 ⊕ (GF q).sum.inv e2) < q *)
  (‘Field (GF q)’by metis_tac[GF_field]>>
   ‘t1 ∈ (GF q).carrier ∧ t2 ∈ (GF q).carrier ∧ e1 ∈ (GF q).carrier ∧ e2 ∈ (GF q).carrier’by metis_tac[GF_element]>>  
  qabbrev_tac‘dt = (t1 ⊕ (GF q).sum.inv t2)’>>
  qabbrev_tac‘de = (e1 ⊕ (GF q).sum.inv e2)’>>
  qabbrev_tac‘x =  dt ⊗ Inv (GF q) de’>>
  (* Maybe I need to add this property to Schnorr protocol as Extractor does not require at the moment that e1 ≠ e2 so it is not well formed*)
  ‘e2 ≠ e1’ by cheat>>
  ‘de = (e1 ⊖ e2)’ by rw[] >>
  ‘de ≠ _0_’  by metis_tac[GF_sub_not_eq_zero]>>
  ‘dt = (t1 ⊖ t2)’ by rw[] >>
  ‘de ∈ (GF q).carrier ∧ dt ∈ (GF q).carrier’ by metis_tac[field_neg_element, field_sub_element] >>
  ‘de ∈ ring_nonzero (GF q)’ by metis_tac[field_nonzero_eq]>>
  ‘(Inv (GF q) de) ∈ (GF q).carrier’by metis_tac[field_inv_element]>>
  ‘(dt ⊗ Inv (GF q) de) ∈ (GF q).carrier’by metis_tac[field_mult_element]>>
  ‘x ∈ (GF q).carrier’by rw[Abbr‘x’]>>
  ‘x < q’ by metis_tac[GF_element])>-

  (*proving  p_1 ** t * |/ (p_2 ** e) ∈ G*)
   (‘Group g’ by gs[cyclic_def] >>
  qabbrev_tac ‘p1 = g.exp p_1 t’ >>
   qabbrev_tac ‘p2 = g.exp p_2 e’ >>
   ‘p1 ∈ g.carrier ∧ p2 ∈ g.carrier’ by metis_tac[group_exp_element] >>
  ‘g.inv p2 ∈ g.carrier’ by metis_tac[group_inv_element] >>
  ‘(g.op p1 (g.inv p2)) ∈ g.carrier’ by metis_tac[group_op_element])>-

  (* proving  r ⊕ e ⊗ w < q *)
  (‘Field (GF q)’by metis_tac[GF_field]>>
  ‘r ∈ (GF q).carrier ∧ e ∈ (GF q).carrier ∧ w ∈ (GF q).carrier’by metis_tac[GF_element]>>
  ‘r ⊕ e ⊗ w < q’by metis_tac[field_mult_element, field_add_element, GF_element])>-

  (* proving  t ⊕ (GF q).sum.inv (e ⊗ w) < q  *)
  (‘Field (GF q)’by metis_tac[GF_field]>>
   ‘t ⊕ (GF q).sum.inv (e ⊗ w) < q’by metis_tac[field_mult_element, field_add_element, GF_element, field_neg_element, field_sub_element])    
QED
        
       
        
(*Define special soundness property for general protocol*)
Theorem schnorr_correctness_thm: 
  prime q ∧ cyclic g ∧ FINITE g.carrier ∧ (order g (cyclic_gen g) = q) ⇒ 
  Correct_SP (Schnorr_SP g q)
Proof
  simp[Schnorr_SP_def, Correct_SP_def, pairTheory.FORALL_PROD] >>
  rpt strip_tac >-
   (
   rename [‘g.exp p w ∈ g.carrier’] >>
   ‘Group g’ by gs[cyclic_def] >>
   simp[group_exp_add, group_exp_mult, GF_eval] >>
   fs[GSYM group_exp_mult, Excl "monoid_exp_mult", GSYM group_exp_add, Excl "monoid_exp_add"] >>
   qabbrev_tac ‘x = r + e * w’ >> 
   qabbrev_tac ‘g' = cyclic_gen g’ >>
   qabbrev_tac ‘LHS =  g.exp p (x MOD q)’ >>
   qabbrev_tac ‘RHS = g.exp p x’ >>    
   ‘∃n. p = monoid_exp g g' n’ by metis_tac[cyclic_element] >>
   ‘LHS =  g.exp (g.exp g' n) (x MOD q)’ by rw[] >>
   ‘g' IN g.carrier’ by metis_tac[cyclic_gen_element] >>  
   ‘LHS = g.exp g' (n * (x MOD q))’ by metis_tac[GSYM group_exp_mult, Excl "monoid_exp_mult"] >> 
   qabbrev_tac ‘k =  n * x MOD q’ >>
   ‘0 < order g g' ’ by rw[] >>
   ‘LHS = g.exp g' (k MOD (order g g'))’ by metis_tac[GSYM group_exp_mod] >>
   qabbrev_tac ‘kmodq = k MOD (order g g')’ >>
   ‘kmodq = ((n * x MOD q) MOD q)’ by rw[] >>
   ‘kmodq = ((n MOD q) * (x MOD q) MOD q) MOD q’ by metis_tac[MOD_TIMES2] >>
   ‘kmodq = ((n MOD q) * (x MOD q)) MOD q’ by metis_tac[MOD_MOD] >>
   ‘kmodq = (n * x)  MOD q’ by metis_tac[MOD_TIMES2] >>
   ‘LHS = g.exp g' ((n*x)MOD q)’ by rw[] >>
   ‘LHS = g.exp g' (n*x)’ by metis_tac[group_exp_mod] >>
   ‘RHS = g.exp (g.exp g' n) x’ by rw[] >>
   ‘RHS = g.exp g' (n * x)’ by metis_tac[GSYM group_exp_mult, Excl "monoid_exp_mult"] >>
   ‘LHS = RHS’ by rw[])>-
   (
   ‘WellFormed_SP (Schnorr_SP g q)’ suffices_by rw[Schnorr_SP_def]>>
   ‘WellFormed_SP (Schnorr_SP g q)’by metis_tac[schnorr_wellformed_thm, Schnorr_SP_def, pairTheory.FORALL_PROD]
   )
QED


        

Theorem schnorr_special_soundness_thm: 
  prime q ∧ cyclic g ∧ FINITE g.carrier ∧ (order g (cyclic_gen g) = q) ⇒ 
  SpecialSoundness_SP (Schnorr_SP g q)
Proof
   simp[Schnorr_SP_def,  SpecialSoundness_SP_def, pairTheory.FORALL_PROD] >>
   rpt strip_tac >-
    (
       ‘Group g’ by metis_tac[cyclic_def] >>
       qabbrev_tac ‘y1 = g.exp p_2 e1’ >>
       qabbrev_tac ‘z1 = g.exp p_1 t1’ >>
       ‘y1 ∈ g.carrier’ by metis_tac[group_exp_element] >>
       ‘z1 ∈ g.carrier’ by metis_tac[group_op_element] >>
       ‘c = g.op z1 ((monoid_inv g) y1)’ by metis_tac[group_lsolve] >>
       qabbrev_tac ‘y2 = g.exp p_2 e2’ >>
       qabbrev_tac ‘z2 = g.exp p_1 t2’ >>
       ‘y2 ∈ g.carrier’ by metis_tac[group_exp_element] >>
       ‘z2 ∈ g.carrier’ by metis_tac[group_op_element] >>
       ‘c = g.op z2 ((monoid_inv g) y2)’ by metis_tac[group_lsolve] >>
       ‘g.op z1 (g.inv y1) =  g.op z2 (g.inv y2)’ by rw[] >>
       ‘g.inv y2 ∈ g.carrier’ by metis_tac[group_inv_element] >>
       ‘g.inv y1 ∈ g.carrier’ by metis_tac[group_inv_element] >>
       ‘g.inv y2 ∈ g.carrier’ by metis_tac[group_inv_element] >>
       ‘z2 =  g.op c (g.inv (g.inv y2))’ by metis_tac[group_lsolve, group_inv_inv] >>
       ‘z2 =  g.op c y2’ by metis_tac[group_lsolve, group_inv_inv] >>
       ‘AbelianGroup g’ by metis_tac[cyclic_group_abelian] >>
       ‘z2 =  g.op y2 c’ by metis_tac[AbelianGroup_def] >>
       ‘z2 =  g.op y2 (g.op z1 ((monoid_inv g) y1))’ by rw[] >>
       ‘z2 =  g.op y2 (g.op z1 ((monoid_inv g) y1))’ by rw[] >>   
       ‘z2 =  g.op (g.op y2 z1) ((monoid_inv g) y1)’ by metis_tac[group_assoc, AbelianGroup_def] >>
       ‘g.op y2 z1 =  g.op z2 (g.inv (g.inv y1))’ by metis_tac[group_lsolve,group_op_element] >>
       ‘g.op y2 z1 =  g.op z2 y1’ by metis_tac[group_inv_inv] >>
       qabbrev_tac‘h = cyclic_gen g’ >> 
       ‘h = cyclic_gen g’ by rw[] >>
       ‘h ∈ g.carrier’ by metis_tac[cyclic_gen_def] >>
       ‘q = CARD g.carrier’ by metis_tac[cyclic_gen_order] >>
       ‘∃i. i < q ∧ p_1 = g.exp h i’ by metis_tac[cyclic_element_by_gen, Abbr‘h’] >>
       ‘z1 = g.exp (g.exp h i) t1’ by rw[] >>
       ‘z1 = g.exp h (i*t1)’ by metis_tac[group_exp_mult]  >>
       ‘z2 = g.exp (g.exp h i) t2’ by metis_tac[] >>
       ‘z2 = g.exp h (i*t2)’ by metis_tac[group_exp_mult]  >>
       ‘∃j. j < q ∧ p_2 = g.exp h j’ by metis_tac[cyclic_element_by_gen, Abbr‘h’] >>
       ‘y1 = g.exp (g.exp h j) e1’ by rw[] >>
       ‘y1 = g.exp h (j*e1)’ by   metis_tac[group_exp_mult] >>
       ‘y2 = g.exp (g.exp h j) e2’ by metis_tac[] >>
       ‘y2 = g.exp h (j*e2)’ by  metis_tac[group_exp_mult]   >>
       ‘g.op (g.exp h (j*e2)) (g.exp h (i*t1)) = g.op (g.exp h (i*t2)) (g.exp h (j*e1))’ by metis_tac[] >> 
       ‘g.exp h (j * e2 + i * t1) = g.exp h (i * t2 + j * e1)’  by metis_tac[ group_exp_add] >>
       qabbrev_tac‘LHS =  g.exp h (j * e2 + i * t1)’ >>
       qabbrev_tac‘RHS =  g.exp h (i * t2 + j * e1)’ >>
       ‘0 < q’ by metis_tac[NOT_PRIME_0, NOT_ZERO]>>

          
       ‘LHS =  g.exp h ((j * e2 + i * t1) MOD q) ∧
        RHS =  g.exp h ((i * t2 + j * e1) MOD q)’ by metis_tac[group_exp_mod] >>
       ‘LHS ∈ g.carrier ∧ RHS ∈ g.carrier’ by metis_tac[group_exp_element] >>
       ‘cyclic_index g LHS  =  ((j * e2 + i * t1) MOD q) ∧
        cyclic_index g RHS = ((i * t2 + j * e1) MOD q)’ by metis_tac[finite_cyclic_index_unique, MOD_LESS] >>
       ‘((j * e2 + i * t1) MOD q)  =  ((i * t2 + j * e1) MOD q)’ by metis_tac[] >>
       ‘j ⊗ e2 ⊕ i ⊗ t1 = i ⊗ t2 ⊕ j ⊗ e1’ by metis_tac[MOD_PLUS, MOD_MOD, GF_eval] >>       
       ‘Field (GF q)’ by rw[GF_field] >>   
       ‘(i ⊗ t1) ⊖ (i ⊗ t2) = (j ⊗ e1) ⊖ (j ⊗ e2)’  by rw[GF_add_sub_identity, GF_eval] >>
       ‘i ∈ (GF q).carrier ∧
        j ∈ (GF q).carrier ∧
        t1 ∈ (GF q).carrier ∧
        t2 ∈ (GF q).carrier ∧
        e1 ∈ (GF q).carrier ∧
        e2 ∈ (GF q).carrier’ by metis_tac[GF_element] >> 
       ‘i ⊗ (t1 ⊖ t2) = j ⊗ (e1 ⊖ e2)’  by metis_tac[GF_mult_rsub] >>
       ‘(t1 ⊖ t2) ∈ (GF q).carrier’ by rw[] >>
       ‘(e1 ⊖ e2) ∈ (GF q).carrier’ by rw[] >>
       ‘(e1 ⊖ e2) ≠ _0_’ by metis_tac[GF_sub_not_eq_zero]>>
       ‘j ⊗ (e1 ⊖ e2) = i ⊗ (t1 ⊖ t2)’ by  metis_tac[Once EQ_SYM_EQ] >>
       ‘j ⊗ (e1 ⊖ e2) ∈ (GF q).carrier’ by rw[] >>
       qabbrev_tac‘d' = i ⊗ (t1 ⊖ t2)’ >>
       qabbrev_tac‘m' = (e1 ⊖ e2)’ >>
       ‘m' = (e1 ⊖ e2)’ by rw[] >>        
       ‘m' ≠ _0_’ by rw[] >>
       ‘d' = j ⊗ m' ∧ d' ∈ (GF q).carrier ∧ m' ∈ (GF q).carrier ∧ m' ≠ _0_’ by rw[] >>
       ‘d' ⊘ m' = j’ by metis_tac[GF_mult_solve_eqn] >>
       ‘(i ⊗ (t1 ⊖ t2)) ⊘ (e1 ⊖ e2) = j’ by metis_tac[] >>
       ‘i ⊗ (t1 ⊖ t2) ⊗ (Inv (GF q) (e1 ⊖ e2)) = j’ by metis_tac [field_div_def] >>
       qabbrev_tac‘tt = (t1 ⊖ t2)’>>
       qabbrev_tac‘ee = (Inv (GF q) (e1 ⊖ e2))’>>
       ‘tt ∈ (GF q).carrier’ by metis_tac[field_neg_element, field_sub_element] >>
       ‘(e1 ⊖ e2) ∈ (GF q).carrier’ by metis_tac[field_neg_element, field_inv_element, field_sub_element] >>
       ‘m' ∈ ring_nonzero (GF q)’ by metis_tac[field_nonzero_eq]>>
       ‘ee  ∈ (GF q).carrier’ by metis_tac[field_inv_element] >>
       ‘ i ⊗ (tt ⊗ ee) = j’ by metis_tac[field_mult_assoc] >>
       qmatch_abbrev_tac‘LHS1 = _’>>           
       ‘Ring (GF q)’ by rw[Field_def]>>      
       ‘(t1 ⊕ (GF q).sum.inv t2) = (t1 ⊖ t2)’ by metis_tac[ring_sub_def] >>
       ‘LHS1 = g.exp p_1 ((t1 ⊖ t2) ⊗ Inv (GF q) (e1 ⊖ e2))’ by metis_tac[ring_sub_def] >>
       ‘LHS1 = g.exp p_1 ((t1 ⊖ t2) ⊘ (e1 ⊖ e2))’ by metis_tac[field_div_def] >>
       ‘LHS1 = g.exp (g.exp h i) ((t1 ⊖ t2) ⊘ (e1 ⊖ e2))’ by metis_tac[] >>      
       ‘LHS1 = g.exp h (i * ((t1 ⊖ t2) ⊘ (e1 ⊖ e2)))’ by  metis_tac[group_exp_mult]   >>     
       ‘LHS1 = g.exp h (i ⊗ ((t1 ⊖ t2) ⊘ (e1 ⊖ e2)))’ by  metis_tac[group_exp_mod, MOD_TIMES2, MOD_MOD, GF_eval, MOD_LESS]   >>
       qabbrev_tac‘x =  (t1 ⊖ t2) ⊘ (e1 ⊖ e2)’ >>
       ‘x = (tt ⊗ ee)’ by metis_tac[field_div_def] >>
       ‘i ⊗ x = j’ by rw[] >>
       ‘p_2 = g.exp h j’ by rw[]>>
       ‘cyclic_index g p_2 = j’  by metis_tac[finite_cyclic_index_unique, MOD_LESS] >>
       ‘cyclic_index g p_2 = i ⊗ x’  by metis_tac[] >>
       ‘p_2 = g.exp h (i ⊗ x)’  by metis_tac[finite_cyclic_index_unique] >>
       ‘LHS1 =  g.exp h ((i * x) MOD q)’ by metis_tac[group_exp_mod] >>
       ‘LHS1 = g.exp h (i ⊗ x)’ by metis_tac[GF_eval] >>
       ‘LHS1 = p_2’by rw[])>-
   (
   ‘WellFormed_SP (Schnorr_SP g q)’ suffices_by rw[Schnorr_SP_def]>>
   ‘WellFormed_SP (Schnorr_SP g q)’by metis_tac[schnorr_wellformed_thm, Schnorr_SP_def, pairTheory.FORALL_PROD]
   )
QED



        
        
Theorem schnorr_simulator_correctness_thm:
  ∀q. prime q ⇒ ∀g: 'a group. cyclic g ∧ FINITE G ∧ (ord (cyclic_gen g) = q) ⇒ 
  SimulatorCorrectness_SP (Schnorr_SP g q)
Proof
  simp[Schnorr_SP_def, SimulatorCorrectness_SP_def, pairTheory.FORALL_PROD] >>
  rpt strip_tac >-
  (‘Group g’ by gs[cyclic_def] >>
  qabbrev_tac‘a = g.exp p_2 e’>>
  qabbrev_tac‘b = g.exp p_1 t’>>
  ‘a ∈ g.carrier ∧ b ∈ g.carrier’ by metis_tac[group_exp_element]>>
   rw[group_rinv_assoc])>-
           (
   ‘WellFormed_SP (Schnorr_SP g q)’ suffices_by rw[Schnorr_SP_def]>>
   ‘WellFormed_SP (Schnorr_SP g q)’by metis_tac[schnorr_wellformed_thm, Schnorr_SP_def, pairTheory.FORALL_PROD]
   )
QED


(* error *)
Theorem schnorr_honest_verifier_zk_thm:
  ∀q. prime q ⇒ ∀g: 'a group. cyclic g ∧ FINITE G ∧ (ord (cyclic_gen g) = q) ⇒ 
  HonestVerifierZeroKnowledge_SP (Schnorr_SP g q)
Proof
  simp[Schnorr_SP_def, HonestVerifierZeroKnowledge_SP_def, pairTheory.FORALL_PROD] >>
  ‘WellFormed_SP (Schnorr_SP g q)’by metis_tac[schnorr_wellformed_thm, Schnorr_SP_def]>>
  rpt strip_tac >>
  
   (
   ‘Group g’ by gs[cyclic_def] >>
  ‘Field (GF q)’ by rw[GF_field] >>
  ‘w ∈ (GF q).carrier ∧
   r ∈ (GF q).carrier ∧
   e ∈ (GF q).carrier ∧
   t ∈ (GF q).carrier’ by metis_tac[GF_element] >>
  ‘0 < q’ by metis_tac[NOT_PRIME_0, NOT_ZERO] >>
   qabbrev_tac‘h = cyclic_gen g’ >>
   ‘h = cyclic_gen g’ by rw[] >>
   ‘h ∈ g.carrier’ by metis_tac[cyclic_gen_def] >>
   ‘q = CARD g.carrier’ by metis_tac[cyclic_gen_order] >>
  ‘∃i. i < q ∧ p_1 = g.exp h i’ by metis_tac[cyclic_element_by_gen, Abbr‘h’] >>
  qabbrev_tac‘a = g.exp p_1 r’ >>
  qabbrev_tac‘b =  g.exp p_1 (r ⊕ e ⊗ w)’ >>
  qabbrev_tac‘c = g.exp (g.exp p_1 w) e’ >>
  ‘a = g.exp (g.exp h i) r’ by rw[] >>
  ‘b = g.exp (g.exp h i) (r ⊕ e ⊗ w)’ by rw[] >>
  ‘c = g.exp (g.exp (g.exp h i) w) e’ by rw[] >>
  ‘a = g.exp h (i*r) /\
   b = g.exp h (i * (r ⊕ e ⊗ w)) /\
   c = g.exp h (i * w * e)’ by metis_tac[group_exp_mult]>>
   ‘a ∈ g.carrier /\
   b ∈ g.carrier /\
   c ∈ g.carrier’ by metis_tac[group_exp_element]>>
  ‘g.op a c = b’ suffices_by metis_tac[group_lsolve]>>
  ‘g.op a c = g.exp h (i*r + i*w*e)’ by metis_tac[group_exp_add]>>
  qabbrev_tac‘d = (i * r + i * w * e)’ >>
  ‘d = i * (r + e * w)’ by metis_tac[MULT_ASSOC, LEFT_ADD_DISTRIB, MULT_COMM, Abbr‘d’]>>
  ‘g.exp h d = g.exp h (d MOD q)’  by metis_tac[group_exp_mod]>>
  ‘g.exp h d = g.exp h ((i * (r + e * w)) MOD q)’  by rw[]>>
  ‘i ∈ (GF q).carrier’ by metis_tac[GF_element] >>
  ‘(i * (r + e * w)) MOD q = i ⊗ (r ⊕ e ⊗ w)’ by metis_tac[MOD_TIMES2, MOD_PLUS, MOD_MOD, GF_eval] >>
  ‘g.op a c = g.exp h (i ⊗ (r ⊕ e ⊗ w))’ by rw[]>>
  ‘g.exp h (i * (r ⊕ e ⊗ w)) = g.exp h ((i * (r ⊕ e ⊗ w)) MOD q)’ by metis_tac[group_exp_mod]>>
  ‘(i * (r ⊕ e ⊗ w)) MOD q = i ⊗ (r ⊕ e ⊗ w)’ by metis_tac[MOD_TIMES2, MOD_PLUS, MOD_MOD, GF_eval] >>
  ‘b = g.exp h (i ⊗ (r ⊕ e ⊗ w))’ by rw[]>>
  ‘g.op a c = b’by rw[])>-
  (* one goal prooved *)
        
  (qabbrev_tac‘ew = (e ⊗ w)’ >>
 ‘Field (GF q)’ by rw[GF_field] >>
  ‘ew ∈ (GF q).carrier’ by metis_tac[GF_element, field_mult_element]>>
  ‘((GF q).sum.inv ew) ∈ (GF q).carrier’by metis_tac[field_neg_element]>>
  ‘ r ⊕ ew ⊕ (GF q).sum.inv ew =  r ⊕ (ew ⊕ (GF q).sum.inv ew)’by metis_tac[GF_element, field_add_assoc]>>
  ‘ew ⊕ (GF q).sum.inv ew = (GF q).sum.id’by metis_tac[field_add_rneg]>>
  ‘ r ⊕ _0_ = r’ by metis_tac[GF_element, field_add_rzero]>>
  ‘ r ⊕ ew ⊕ (GF q).sum.inv ew = r’ by rw[])>-
  (* one goal prooved *) 

    
  (qabbrev_tac‘ew =  (e ⊗ w)’ >>
  ‘Field (GF q)’ by rw[GF_field] >>
  ‘ew ∈ (GF q).carrier’ by metis_tac[GF_element, field_mult_element]>>
  ‘((GF q).sum.inv ew) ∈ (GF q).carrier’by metis_tac[field_neg_element]>>

  ‘ t ⊕ (GF q).sum.inv ew ⊕ ew =  t ⊕ ( ((GF q).sum.inv ew) ⊕ ew )’by metis_tac[GF_element, field_add_assoc]>>
  ‘ ( ((GF q).sum.inv ew) ⊕ ew ) = (GF q).sum.id’by metis_tac[field_add_lneg]>>
  ‘ t ⊕ _0_ = t’ by metis_tac[GF_element, field_add_rzero]>>
   ‘t ⊕ (GF q).sum.inv ew ⊕ ew = t’ by rw[])>-
         (
   ‘WellFormed_SP (Schnorr_SP g q)’ suffices_by rw[Schnorr_SP_def]>>
   ‘WellFormed_SP (Schnorr_SP g q)’by metis_tac[schnorr_wellformed_thm, Schnorr_SP_def, pairTheory.FORALL_PROD]
   )
QED



val _ = export_theory();

