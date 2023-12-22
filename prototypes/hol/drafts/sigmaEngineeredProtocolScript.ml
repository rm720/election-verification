
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
type_of “|/”
print_match [] “g.exp _ ( _ MOD _ )”
M-x replace-string
 ⊘
2298
\oslash
*)
       

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "sigmaEngineeredProtocol";

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


Datatype:
 RTuple = Tuple2 'a 'b
          | Tuple1 'a
End

Definition disjoint_def:
 (disjoint (Tuple2 a1 a2) (Tuple2 b1 b2) ⇔ a1 ≠ b1 ∧ a2 ≠ b2) ∧
 (disjoint (Tuple1 a) (Tuple1 b) ⇔ a ≠ b) ∧
 (disjoint _ _ ⇔ T)
End

        

Datatype: SigmaProtocol = <| (*TODO make Challenges a Group*) 
                             Statements: 's set;
                             Witnesses: 'w set;
                             Relation: 's -> 'w -> bool;
                             RandomCoins: 'r set;
                             Commitments: 'c set;
                             Challenges:  'e set;
                             Responses: 't set;
                             Prover_0: 's -> 'w -> 'r -> 'c; (*why does it need w?*)
                             Prover_1: 's -> 'w -> 'r -> 'c -> 'e -> 't;
                             HonestVerifier: ('s # 'c # 'e # 't) -> bool;
                             Extractor: 't -> 't -> 'e -> 'e -> 'w;
                             Simulator: 's -> 't -> 'e -> ('s # 'c # 'e # 't);
                             SimulatorMap: 's -> 'w -> 'e -> 'r  -> 't;
                             SimulatorMapInverse: 's -> 'w -> 'e -> 't -> 'r;
                             |>
End

Definition SP_and_def:
  SP_and S1 S2 =  <|Statements:= S1.Statements × S2.Statements;
                      Witnesses:= S1.Witnesses × S2.Witnesses;
                      Relation:= (λ (s1, s2) (w1, w2). S1.Relation s1 w1 ∧ S2.Relation s2 w2);
                      RandomCoins:= (S1.RandomCoins × S2.RandomCoins);
                      Commitments:= (S1.Commitments × S2.Commitments);
                      Challenges:= (S1.Challenges × S2.Challenges); (*product group*)
                      Responses:= (S1.Responses × S2.Responses);
                      Prover_0:= (λ (s1, s2) (w1, w2) (r1, r2). (S1.Prover_0 s1 w1 r1, S2.Prover_0 s2 w2 r2));
                      Prover_1:= (λ (s1, s2) (w1, w2) (r1, r2) (c1, c2) (e1, e2). (S1.Prover_1 s1 w1 r1 c1 e1, S2.Prover_1 s2 w2 r2 c2 e2));
                      HonestVerifier:= (λ ((s1, s2), (c1, c2), (e1, e2), (t1, t2)). S1.HonestVerifier (s1, c1, e1, t1) ∧ S2.HonestVerifier (s2, c2, e2, t2));
                      Extractor:= (λ (t1a, t1b) (t2a, t2b) (e1a, e1b) (e2a, e2b). (S1.Extractor t1a t2a e1a e2a, S2.Extractor t1b t2b e1b e2b));
                      Simulator:= (λ (s1, s2) (t1, t2) (e1, e2). let (s1', c1', e1', t1') = S1.Simulator s1 t1 e1;
                                                                     (s2', c2', e2', t2') = S2.Simulator s2 t2 e2
                                                                 in
                                                                   ((s1', s2'),(c1', c2'),(e1', e2'),(t1', t2')));
                                                                                                                        
                      SimulatorMap:= (λ (s1, s2) (w1, w2) (e1, e2) (r1, r2). (S1.SimulatorMap s1 w1 e1 r1, S2.SimulatorMap s2 w2 e2 r2));
                      SimulatorMapInverse:=   (λ (s1, s2) (w1, w2) (e1, e2) (t1, t2). (S1.SimulatorMapInverse s1 w1 e1 t1, S2.SimulatorMapInverse s2 w2 e2 t2));
                     |> 
End
                       

Definition SP_or_def:
  SP_or S1 =  <|Statements:= S1.Statements × S1.Statements;
                      Witnesses:= S1.Witnesses;
                      Relation:= (λ (s1, s2) w. S1.Relation s1 w ∨ S1.Relation s2 w);
                      RandomCoins:= (S1.RandomCoins × (S1.Challenges × S1.Responses));
                      Commitments:= (S1.Commitments × S1.Commitments);
                      Challenges:= S1.Challenges;
                      Responses:= (S1.Responses × (S1.Challenges × S1.Responses));
                                  
                      Prover_0:= (λ (s1, s2) w (r, (e, t)). if S1.Relation s1 w then
                                                              let (s2', c2', e2', t2') = S1.Simulator s2 t e;
                                                              in (S1.Prover_0 s1 w r, c2')
                                                            else
                                                              let (s1', c1', e1', t1') = S1.Simulator s1 t e;
                                                              in (c1', S1.Prover_0 s2 w r));
                                                                
                      Prover_1:= (λ (s1, s2) w (rr,(re,rt)) (c1, c2) e. if S1.Relation s1 w then
                                                                          let (s2', c2', e2', t2') = S1.Simulator s2 rt re;
                                                                          in (S1.Prover_1 s1 w rr c1 (e-te), (re,t2'));
                                                                        else
                                                                          let  (s1', c1', e1', t1') = S1.Simulator s1 rt re;
                                                                          in (t1', (e-re, S2.Prover_1 s2 w rr c2 (e-re)));
                                                                                  
                                  
                      HonestVerifier:= (λ ((s1, s2), (c1, c2), e, (t1, (te,t2))). S1.HonestVerifier (s1, c1, (e-te), t1) ∧ S1.HonestVerifier (s2, c2, te, t2));
                                                   
                      Extractor:= (λ (t1a, (t1e,t1b)) (t2a, (t2e,t2b)) e1 e2. if t1e ≠ t2e then
                                                                                    S1.Extractor t1b t2b t1e t2e
                                                                                  else
                                                                                    S1.Extractor t1a t2a (e1-t1e) (e2-t2e));
                                  
                      Simulator:= (λ (s1, s2) (t1, (te,t2)) e. let (s1', c1', e1', t1') = S1.Simulator s1 t1 (e-te);
                                                                   (s2', c2', e2', t2') = S1.Simulator s2 t2 te
                                                               in
                                                                 ((s1', s2'),(c1', c2'),e,(t1', t2')));
                                                                                                                        
                      SimulatorMap:= (λ (s1, s2) w e (rr,(re,rt)). if S1.Relation s1 w then
                                                                     (S1.SimulatorMap s1 w (e-re) rr, (e, rt))
                                                                   else
                                                                     (rt, (e, S1.SimulatorMap s2 w e rr)));
                                     
                      SimulatorMapInverse:=   (λ (s1, s2) w e (t1, (te,t2)). if S1.Relation s1 w then
                                                                     (S1.SimulatorMapInverse s1 w (e-te) t1, (e, t2))
                                                                   else
                                                                     ((S1.SimulatorMapInverse s2 w e t2), (e,t1));
                     |> 
End
     


          

(* Same as above for 4 OR theorems*)
        
        

(*Correctness property: Correct Prover get accepted by Verifier*)
Definition Correct_SP_def:
  Correct_SP sp ⇔
    ∀s w r e. s ∈ sp.Statements ∧ w ∈ sp.Witnesses ∧ r ∈ sp.RandomCoins ∧ e ∈ sp.Challenges
                ∧ sp.Relation s w ⇒
                              let c =  sp.Prover_0 s w r in 
                                sp.HonestVerifier(s, c, e, sp.Prover_1 s w r c e)
                                        
End  

(*Special soundness: Prover has the knowledge,
i.e. there exist an extracrot s.t. it can get knowledge form prover*)
Definition SpecialSoundness_SP_def:
  SpecialSoundness_SP sp ⇔
  ∀s c e1 e2 t1 t2.
     s ∈ sp.Statements ∧
     c ∈ sp.Commitments ∧
     t1 ∈ sp.Responses ∧
     t2 ∈ sp.Responses ∧
     e1 ∈ sp.Challenges ∧
     e2 ∈ sp.Challenges ∧
     (DISJOINT (to_set e1) (to_set e2)) ∧ 
     sp.HonestVerifier(s, c, e1, t1) ∧
     sp.HonestVerifier(s, c, e2, t2) ⇒
                    sp.Relation s (sp.Extractor t1 t2 e1 e2)
End


Definition SimulatorCorrectness_SP_def:
  SimulatorCorrectness_SP sp ⇔
  ∀s t e.
     s ∈ sp.Statements ∧
     t ∈ sp.Responses ∧
     e ∈ sp.Challenges ⇒
     sp.HonestVerifier(sp.Simulator s t e)
End

Definition HonestVerifierZeroKnowledge_SP_def:
   HonestVerifierZeroKnowledge_SP sp ⇔
  ∀s w r e t.
     s ∈ sp.Statements ∧
     w ∈ sp.Witnesses ∧
     r ∈ sp.RandomCoins ∧
     e ∈ sp.Challenges ∧
     t ∈ sp.Responses ∧
     sp.Relation s w ⇒
     let c =  sp.Prover_0 s w r;
         spm = sp.SimulatorMap s w e;
         spmi = sp.SimulatorMapInverse s w e;
     in
       (s, c, e, sp.Prover_1 s w r c e) = sp.Simulator s (spm r) e ∧
       spmi(spm r) = r ∧
       spm(spmi t) = t
End
        

Definition Schnorr_SP_def:
  Schnorr_SP gr q =  <|Statements:= gr.carrier × gr.carrier;
                      Witnesses:= count q;
                      Relation:= (λ (s1, s2) w. monoid_exp gr s1 w = s2); (* How does Relation know the group operation? *)
                      RandomCoins:= count q;
                      Commitments:= gr.carrier;
                      Challenges:= count q;
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

        
(*Define special soundness property for general protocol*)
Theorem schnorr_correctness_thm: 
  prime q ∧ cyclic g ∧ FINITE g.carrier ∧ (order g (cyclic_gen g) = q) ⇒ 
  Correct_SP (Schnorr_SP g q)
Proof
  simp[Schnorr_SP_def, Correct_SP_def, pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
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
  ‘LHS = RHS’ by rw[]
QED


        

Theorem schnorr_special_soundness_thm: 
  prime q ∧ cyclic g ∧ FINITE g.carrier ∧ (order g (cyclic_gen g) = q) ⇒ 
  SpecialSoundness_SP (Schnorr_SP g q)
Proof
   simp[Schnorr_SP_def,  SpecialSoundness_SP_def, pairTheory.FORALL_PROD] >>
   rpt strip_tac >>
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
   ‘LHS1 = p_2’by rw[] 
QED



        
        
Theorem schnorr_simulator_correctness_thm:
  ∀q. prime q ⇒ ∀g: 'a group. cyclic g ∧ FINITE G ∧ (ord (cyclic_gen g) = q) ⇒ 
  SimulatorCorrectness_SP (Schnorr_SP g q)
Proof
  simp[Schnorr_SP_def, SimulatorCorrectness_SP_def, pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
  ‘Group g’ by gs[cyclic_def] >>
  qabbrev_tac‘a = g.exp p_2 e’>>
  qabbrev_tac‘b = g.exp p_1 t’>>
  ‘a ∈ g.carrier ∧ b ∈ g.carrier’ by metis_tac[group_exp_element]>>
  rw[group_rinv_assoc]
QED


        
Theorem schnorr_honest_verifier_zk_thm:
  ∀q. prime q ⇒ ∀g: 'a group. cyclic g ∧ FINITE G ∧ (ord (cyclic_gen g) = q) ⇒ 
  HonestVerifierZeroKnowledge_SP (Schnorr_SP g q)
Proof
  simp[Schnorr_SP_def, HonestVerifierZeroKnowledge_SP_def, pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
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
  ‘g.op a c = b’by rw[]>>
        
  qabbrev_tac‘ew =  (e ⊗ w)’ >>
  ‘ew ∈ (GF q).carrier’ by metis_tac[field_mult_element]>>
  ‘((GF q).sum.inv ew) ∈ (GF q).carrier’by metis_tac[field_neg_element]>>     
  ‘ r ⊕ ew ⊕ (GF q).sum.inv ew =  r ⊕ (ew ⊕ (GF q).sum.inv ew)’by metis_tac[field_add_assoc]>>
  ‘ew ⊕ (GF q).sum.inv ew = (GF q).sum.id’by metis_tac[field_add_rneg]>>
  ‘ r ⊕ _0_ = r’ by metis_tac[field_add_rzero]>>
  ‘ r ⊕ ew ⊕ (GF q).sum.inv ew = r’ by rw[]>>

  qabbrev_tac‘ew =  (e ⊗ w)’ >>
  ‘ew ∈ (GF q).carrier’ by metis_tac[field_mult_element]>>
  ‘((GF q).sum.inv ew) ∈ (GF q).carrier’by metis_tac[field_neg_element]>>     
  ‘ t ⊕ (GF q).sum.inv ew ⊕ ew =  t ⊕ ( ((GF q).sum.inv ew) ⊕ ew )’by metis_tac[field_add_assoc]>>
  ‘ ( ((GF q).sum.inv ew) ⊕ ew ) = (GF q).sum.id’by metis_tac[field_add_lneg]>>
  ‘ t ⊕ _0_ = t’ by metis_tac[field_add_rzero]>>
  ‘t ⊕ (GF q).sum.inv ew ⊕ ew = t’ by rw[]                                             
QED








(* Do I need to prove this for Shcnorr protocol ? *)
Theorem Correct_SP_and_thm:
  Correct_SP sp1 ∧ Correct_SP sp2 ⇒ Correct_SP (SP_and sp1 sp2)
Proof
   simp[Correct_SP_def, SP_and_def, pairTheory.FORALL_PROD]
QED


Theorem  SpecialSoundness_SP_and_thm:
  SpecialSoundness_SP sp1 ∧ SpecialSoundness_SP sp2
                      ⇒ SpecialSoundness_SP (SP_and sp1 sp2)
Proof
  simp[SpecialSoundness_SP_def, SP_and_def,  pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
  qabbrev_tac‘s1 = p_1’>> qabbrev_tac‘s2 = p_2’>>   qabbrev_tac‘c1 = p_1'’>> qabbrev_tac‘c2 = p_2'’>>
  qabbrev_tac‘t11 =  p_1'⁴'’>> qabbrev_tac‘t12 =   p_2'⁴'’>>   qabbrev_tac‘t21 = p_1'⁵'’>> qabbrev_tac‘t22 = p_2'⁵'’>>
  qabbrev_tac‘e11 =  p_1''’>> qabbrev_tac‘e12 =   p_2''’>>   qabbrev_tac‘e21 = p_1'³'’>> qabbrev_tac‘e22 = p_2'³'’>>

                  
  (*TODO ...*)
QED


Theorem SimulatorCorrectness_SP_and_thm:
    SimulatorCorrectness_SP sp1 ∧
    SimulatorCorrectness_SP sp2
    ⇒ SimulatorCorrectness_SP (SP_and sp1 sp2)
Proof
  qabbrev_tac‘spand = SP_and sp1 sp2’>> 
  simp[SimulatorCorrectness_SP_def, SP_and_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac >>
      
  qabbrev_tac‘x1 = sp1.Simulator p_1 p_1' p_1''’>>
  qabbrev_tac‘x2 = sp2.Simulator p_2 p_2' p_2''’>>
  ‘(s1,c1,e1,t1) = x1 ∧ (s2,c2,e2,t2) = x2’ by cheat>>
  qabbrev_tac‘x = ((s1,s2),(c1,c2),(e1,e2),(t1,t2))’>>
  ‘sp1.HonestVerifier(s1,c1,e1,t1) ∧ sp2.HonestVerifier(s2,c2,e2,t2)’ by cheat>>  metis_tac[]>> (* does not work *)
  qabbrev_tac‘y = spand.Simulator (p_1,p_2) (p_1',p_2') (p_1'',p_2'')’>>
  ‘x = y’ by cheat >> metis_tac[SP_and_def, pairTheory.FORALL_PROD]>>
  ‘spand.HonestVerifier((s1,s2),(c1,c2),(e1,e2),(t1,t2)) =
   ((sp1.HonestVerifier (s1,c1,e1,t1)) ∧ (sp2.HonestVerifier (s2,c2,e2,t2)))’
                        by cheat >>  metis_tac[SP_and_def]>>
  rw[]>>
  metis_tac[]>>
QED


Theorem HonestVerifierZeroKnowledge_SP_and_thm:
  HonestVerifierZeroKnowledge_SP sp1 ∧ HonestVerifierZeroKnowledge_SP sp2 ⇒ HonestVerifierZeroKnowledge_SP (SP_and sp1 sp2)
Proof
  simp[HonestVerifierZeroKnowledge_SP_def, SP_and_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac >>

      (* rename ['((a,b),(sp1.Prover_0 a c d, sp2.Prover_0 _ _ _ ), _)']  *)
      
  qabbrev_tac‘s1 = p_1’>> qabbrev_tac‘s2 = p_2’>>   qabbrev_tac‘w1 = p_1' ’>> qabbrev_tac‘w2 = p_2' ’>>
  qabbrev_tac‘r1 = p_1'' ’>> qabbrev_tac‘r2 = p_2'' ’>>   qabbrev_tac‘e1 = p_1'³'’>> qabbrev_tac‘e2 = p_2'³'’>>             
  qabbrev_tac‘t1 =  p_1'⁴'’>> qabbrev_tac‘t2 =   p_2'⁴'’>>

                 
‘sp1.SimulatorMapInverse s1 w1 e1 (sp1.SimulatorMap s1 w1 e1 r1) = r1 ∧
 sp1.SimulatorMap s1 w1 e1 (sp1.SimulatorMapInverse s1 w1 e1 t1) = t1 ∧
 sp2.SimulatorMapInverse s2 w2 e2 (sp2.SimulatorMap s2 w2 e2 r2) = r2 ∧
 sp2.SimulatorMap s2 w2 e2 (sp2.SimulatorMapInverse s2 w2 e2 t2) = t2’by metis_tac[]>>

  (*
  ‘sp2.SimulatorMapInverse p_2 p_2' p_2'³' (sp2.SimulatorMap p_2 p_2' p_2'³' p_2'') = p_2'' ∧
   sp2.SimulatorMap p_2 p_2' p_2'³' (sp2.SimulatorMapInverse p_2 p_2' p_2'³' p_2'⁴') = p_2'⁴'’ by metis_tac[HonestVerifierZeroKnowledge_SP_def, SP_and_def]>>
   
   
  (* it says 1 subgoal instead of 5, so its good? *)
  qabbrev_tac‘s1 = p_1’>> qabbrev_tac‘s2 = p_2’>>   qabbrev_tac‘w1 = p_1' ’>> qabbrev_tac‘w2 = p_2' ’>>
  qabbrev_tac‘r1 = p_1'' ’>> qabbrev_tac‘r2 = p_2'' ’>>   qabbrev_tac‘e1 = p_1'³'’>> qabbrev_tac‘e2 = p_2'³'’>>             
  qabbrev_tac‘t1 =  p_1'⁴'’>> qabbrev_tac‘t2 =   p_2'⁴'’>>
  *)

  qabbrev_tac‘c1 = sp1.Prover_0 s1 w1 r1’>> qabbrev_tac‘c2 = sp2.Prover_0 s2 w2 r2’>>
  qabbrev_tac‘t11 = sp1.Prover_1 s1 w1 r1 c1 e1’>>
  qabbrev_tac‘t22 = sp2.Prover_1 s2 w2 r2 c2 e2’>>
  qabbrev_tac‘t222 = sp2.SimulatorMap s2 w2 e2 r2’>>
  qabbrev_tac‘t111 = sp1.SimulatorMap s1 w1 e1 r1’>>
  qabbrev_tac‘x1 = sp1.Simulator s1 t111 e1’>>
  qabbrev_tac‘x2 = sp2.Simulator s2 t222 e2’>>


  ‘t11 ∈ sp1.Responses’by simp[pairTheory.FORALL_PROD]>>
                 
                 
  ‘t11 ∈ sp1.Responses ∧ t111 ∈ sp1.Responses ∧ t22 ∈ sp2.Responses ∧ t222 ∈ sp2.Responses’by cheat>>
       
  ‘sp1.Simulator s1 t111 e1 =  sp1.Simulator s1 (sp1.SimulatorMap s1 w1 e1 r1) e1’by rw[]>>
  ‘sp1.Simulator s1 (sp1.SimulatorMap s1 w1 e1 r1) e1 = (s1,sp1.Prover_0 s1 w1 r1, e1, sp1.Prover_1 s1 w1 r1 (sp1.Prover_0 s1 w1 r1) e1)’ by metis_tac[]>>
  ‘(s1,sp1.Prover_0 s1 w1 r1, e1, sp1.Prover_1 s1 w1 r1 (sp1.Prover_0 s1 w1 r1) e1) = (s1, c1, e1, t11)’by metis_tac[]>>
  ‘x1 =  (s1, c1, e1, t11)’by metis_tac[]>>

  ‘sp2.Simulator s2 t222 e2 =  sp2.Simulator s2 (sp2.SimulatorMap s2 w2 e2 r2) e2’by rw[]>>
  ‘sp2.Simulator s2 (sp2.SimulatorMap s2 w2 e2 r2) e2 = (s2,sp2.Prover_0 s2 w2 r2, e2, sp2.Prover_1 s2 w2 r2 (sp2.Prover_0 s2 w2 r2) e2)’ by metis_tac[]>>
  ‘(s2,sp2.Prover_0 s2 w2 r2, e2, sp2.Prover_1 s2 w2 r2 (sp2.Prover_0 s2 w2 r2) e2) = (s2, c2, e2, t22)’by metis_tac[]>>
  ‘x2 =  (s2, c2, e2, t22)’by metis_tac[]>>
  ‘(λ(s1',c1',e1',t1').(λ(s2',c2',e2',t2'). ((s1',s2'),(c1',c2'),(e1',e2'),t1',t2'))  (s2, c2, e2, t22)) (s1, c1, e1, t11) =  ((s1,s2),(c1,c2),(e1,e2),(t11,t22))’by rw[]>>
   ‘ ((s1,s2),(c1,c2),(e1,e2),t11,t22) =
        (λ(s1',c1',e1',t1').
             (λ(s2',c2',e2',t2'). ((s1',s2'),(c1',c2'),(e1',e2'),t1',t2')) x2)
          x1’by metis_tac[]>>

  (* 4 subgoals left *)
     
  qabbrev_tac‘s1 = p_1’>> qabbrev_tac‘s2 = p_2’>>   qabbrev_tac‘w1 = p_1' ’>> qabbrev_tac‘w2 = p_2' ’>>
  qabbrev_tac‘r1 = p_1'' ’>> qabbrev_tac‘r2 = p_2'' ’>>   qabbrev_tac‘e1 = p_1'³'’>> qabbrev_tac‘e2 = p_2'³'’>>             
  qabbrev_tac‘t1 =  p_1'⁴'’>> qabbrev_tac‘t2 =   p_2'⁴'’>>
  ‘ sp1.SimulatorMapInverse s1 w1 e1 (sp1.SimulatorMap s1 w1 e1 r1) = r1’by metis_tac[]>>


  qabbrev_tac‘s1 = p_1’>> qabbrev_tac‘s2 = p_2’>>   qabbrev_tac‘w1 = p_1' ’>> qabbrev_tac‘w2 = p_2' ’>>
  qabbrev_tac‘r1 = p_1'' ’>> qabbrev_tac‘r2 = p_2'' ’>>   qabbrev_tac‘e1 = p_1'³'’>> qabbrev_tac‘e2 = p_2'³'’>>             
  qabbrev_tac‘t1 =  p_1'⁴'’>> qabbrev_tac‘t2 =   p_2'⁴'’>>
  ‘sp2.SimulatorMapInverse s2 w2 e2 (sp2.SimulatorMap s2 w2 e2 r2) = r2’ by metis_tac[]>>


      qabbrev_tac‘s1 = p_1’>> qabbrev_tac‘s2 = p_2’>>   qabbrev_tac‘w1 = p_1' ’>> qabbrev_tac‘w2 = p_2' ’>>
  qabbrev_tac‘r1 = p_1'' ’>> qabbrev_tac‘r2 = p_2'' ’>>   qabbrev_tac‘e1 = p_1'³'’>> qabbrev_tac‘e2 = p_2'³'’>>             
  qabbrev_tac‘t1 =  p_1'⁴'’>> qabbrev_tac‘t2 =   p_2'⁴'’>>                       
‘ sp1.SimulatorMap s1 w1 e1 (sp1.SimulatorMapInverse s1 w1 e1 t1) = t1’by metis_tac[]>>


      qabbrev_tac‘s1 = p_1’>> qabbrev_tac‘s2 = p_2’>>   qabbrev_tac‘w1 = p_1' ’>> qabbrev_tac‘w2 = p_2' ’>>
  qabbrev_tac‘r1 = p_1'' ’>> qabbrev_tac‘r2 = p_2'' ’>>   qabbrev_tac‘e1 = p_1'³'’>> qabbrev_tac‘e2 = p_2'³'’>>             
  qabbrev_tac‘t1 =  p_1'⁴'’>> qabbrev_tac‘t2 =   p_2'⁴'’>>     

‘sp2.SimulatorMap s2 w2 e2 (sp2.SimulatorMapInverse s2 w2 e2 t2) = t2’ by metis_tac[]>>
     


      
                 

  ‘(s1,sp1.Prover_0 s1 w1 r1, e1, sp1.Prover_1 s1 w1 r1 (sp1.Prover_0 s1 w1 r1) e1) = sp1.Simulator s1 (sp1.SimulatorMap s1 w1 e1 r1) e1’ rw[]>>
       
  metis_tac[]>>







       
 ∧ r11 ∈ sp1.RandomCoins ∧ r22 ∈ sp2.RandomCoins 

   

  HonestVerifierZeroKnowledge_SP_def
  > # val it =
   ⊢ ∀sp.
       HonestVerifierZeroKnowledge_SP sp ⇔
       ∀s w r e t.
         s ∈ sp.Statements ∧ w ∈ sp.Witnesses ∧ r ∈ sp.RandomCoins ∧
         e ∈ sp.Challenges ∧ t ∈ sp.Responses ∧ sp.Relation s w ⇒
         (let
            c = sp.Prover_0 s w r;
            spm = sp.SimulatorMap s w e;
            spmi = sp.SimulatorMapInverse s w e
          in
            (s,c,e,sp.Prover_1 s w r c e) = sp.Simulator s (spm r) e ∧
            spmi (spm r) = r ∧ spm (spmi t) = t): thm
> 


      
  (*TODO ... *)
QED


Theorem Correct_SP_or_thm:
  Correct_SP sp1 ⇒ Correct_SP (SP_or sp1)
Proof
   simp[Correct_SP_def, SP_or_def, pairTheory.FORALL_PROD]
QED


Theorem  SpecialSoundness_SP_or_thm:
  SpecialSoundness_SP sp1 ⇒ SpecialSoundness_SP (SP_or sp1)
Proof
  simp[SpecialSoundness_SP_def, SP_or_def, pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
  (*TODO ...*)
QED


Theorem SimulatorCorrectness_SP_or_thm:
  SimulatorCorrectness_SP sp1 ⇒ SimulatorCorrectness_SP (SP_or sp1)
Proof
  simp[SimulatorCorrectness_SP_def, SP_or_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac >>
  (*TODO ... *)
QED


Theorem HonestVerifierZeroKnowledge_SP_or_thm:
  HonestVerifierZeroKnowledge_SP sp1 ⇒ HonestVerifierZeroKnowledge_SP (SP_or sp1)
Proof
  simp[HonestVerifierZeroKnowledge_SP_def, SP_or_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac >>
  (*TODO ... *)
QED






        

val _ = export_theory();

