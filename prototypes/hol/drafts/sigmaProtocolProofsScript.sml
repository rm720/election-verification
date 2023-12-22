
(* ------------------------------------------------------------------------- *)
(* -- Sigma Protocol Proofs-- *)
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
val _ = new_theory "sigmaProtocolProofs";

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

   (*
Definition HOL_Fuction_def:
  
END
 *)       


Definition Gcross_def:
  Gcross g1 g2 = <| carrier:= g1.carrier × g2.carrier;
                    id:= (g1.id, g2.id);
                    op:= λ (a,b) (c,d). (g1.op a c, g2.op b d);
                 |>
End


Theorem Gcross_group_thm:
 Group g1 ∧ Group g2 ⇒ Group (Gcross g1 g2)
Proof
  rw[]>>
  simp[  group_def_alt, Group_def, Gcross_def, pairTheory.FORALL_PROD]>>
  simp[group_def_alt, pairTheory.FORALL_PROD]>>
  rpt strip_tac >-
   (
   ‘ g1.op (g1.op p_1 p_1') p_1'' = g1.op p_1 (g1.op p_1' p_1'')’by metis_tac[group_assoc]
   )>-
   (
   ‘g2.op (g2.op p_2 p_2') p_2'' = g2.op p_2 (g2.op p_2' p_2'')’by metis_tac[group_assoc]
   )>-
   (
   ‘∀x. x ∈ g1.carrier ⇒ ∃y. y ∈ g1.carrier ∧ g1.op y x = g1.id’by metis_tac[group_def_alt]>>
   ‘∃y1. y1 ∈ g1.carrier ∧  g1.op y1 p_1 = g1.id ∧
         ∃y2. y2 ∈ g2.carrier ∧  g2.op y2 p_2 = g2.id’by metis_tac[group_def_alt]>>
   qabbrev_tac‘y = (y1, y2)’>>
   ‘(λ(a,b) (c,d). (g1.op a c,g2.op b d)) (y1, y2) (p_1,p_2) = ((g1.op y1 p_1) , (g2.op y2 p_2))’by rw[]>>
   ‘((g1.op y1 p_1) , (g2.op y2 p_2)) = (g1.id,g2.id)’ by metis_tac[FST, SND, CROSS_DEF]>>              
   ‘FST y ∈ g1.carrier ∧ SND y ∈ g2.carrier’ by metis_tac[FST, SND, CROSS_DEF]>>
   metis_tac[]
   )
QED
        

               

Datatype: SigmaProtocol = <| 
                             Statements: 's set;
                             Witnesses: 'w set;
                             Relation: 's -> 'w -> bool;
                             RandomCoins: 'r set;
                             Commitments: 'c set;
                             Challenges:  'e group;
                             Disjoint: 'e -> 'e -> bool;
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

Definition SP_csub_def:
  SP_csub sp a b = sp.Challenges.op a (sp.Challenges.inv b)
End

  (*SP_or sp = let D x y = (x ≠ y) in*)
(* according to the paper *)
Definition SP_or_def:
  SP_or sp = <|Statements:= sp.Statements × sp.Statements;
                Witnesses:= sp.Witnesses;
                Relation:= (λ (s1, s2) w. sp.Relation s1 w ∨ sp.Relation s2 w);
                RandomCoins:= ((sp.RandomCoins × sp.Responses) × sp.Challenges.carrier);
                Commitments:= (sp.Commitments × sp.Commitments);
                Challenges:= sp.Challenges;        
                Disjoint:= (λ e1 e2. e1 ≠ e2);
                Responses:= ((sp.Responses × sp.Challenges.carrier) × sp.Responses);
                Prover_0:= (λ (s1, s2) w ((r, t),e).
                              if sp.Relation s1 w then
                                let c1 = sp.Prover_0 s1 w r;
                                    (s2', c2', e2', t2') = sp.Simulator s2 t e;
                                in (c1, c2')
                              else
                                let (s1', c1', e1', t1') = sp.Simulator s1 t e;
                                    c2 = sp.Prover_0 s2 w r;
                                in (c1',c2));
                Prover_1:= (λ (s1, s2) w ((r,t1),e2) (c1, c2) e1.
                              let   e3 = SP_csub sp e1 e2
                              in
                                if sp.Relation s1 w then
                                  let (s2', c2', e2', t2') = sp.Simulator s2 t1 e2;
                                      t2 = sp.Prover_1 s1 w r c1 e3;
                                  in ((t2, e3), t2')
                                else
                                  let  (s1', c1', e1', t1') = sp.Simulator s1 t1 e2;
                                       t2 = sp.Prover_1 s2 w r c2 e3;
                                  in ((t1', e2), t2));
                HonestVerifier:= (λ ((s1, s2), (c1, c2), e1, ((t1,e2),t2)).
                                    let e3 = SP_csub sp e1 e2
                                    in sp.HonestVerifier (s1, c1, e2, t1) ∧ sp.HonestVerifier (s2, c2, e3, t2));
                Extractor:= (λ ((t1,e1),t2) ((t3,e3),t4) e5 e6.     
                               if e1 ≠ e3 then 
                                  sp.Extractor t1 t3 e1 e3
                               else
                                 let e2 = SP_csub sp e5 e1;
                                     e4 = SP_csub sp e6 e3;
                                 in sp.Extractor t2 t4 e2 e4);
                Simulator:= (λ (s1, s2) ((t1,e1),t2) e2.
                               let (s1', c1', e1', t1') = sp.Simulator s1 t1 e1;
                                   e3 = SP_csub sp e2 e1;
                                   (s2', c2', e2', t2') = sp.Simulator s2 t2 e3;
                               in  ((s1, s2),(c1', c2'),e2,((t1',e1), t2')));
                SimulatorMap:= (λ (s1, s2) w e1 ((r,t),e2).
                                  let e3 = SP_csub sp e1 e2;
                                  in
                                  if sp.Relation s1 w then
                                    let t1 = sp.SimulatorMap s1 w e3 r;
                                    in ((t1, e3), t)
                                  else
                                    let t2 = sp.SimulatorMap s2 w e3 r;
                                    in ((t, e2), t2));
                SimulatorMapInverse:= (λ (s1, s2) w e1 ((t1,e2),t2).
                                         let e3 = SP_csub sp e1 e2;
                                         in
                                           if sp.Relation s1 w then
                                             let r = sp.SimulatorMapInverse s1 w e2 t1;
                                             in ((r,t2),e3)
                                           else
                                             let r = sp.SimulatorMapInverse s2 w e3 t2;
                                             in  ((r,t1),e2));
              |> 
End
     
Definition SP_and_def:
  SP_and S1 S2 =  <|Statements:= S1.Statements × S2.Statements;
                      Witnesses:= S1.Witnesses × S2.Witnesses;
                      Relation:= (λ (s1, s2) (w1, w2). S1.Relation s1 w1 ∧ S2.Relation s2 w2);
                      RandomCoins:= (S1.RandomCoins × S2.RandomCoins);
                      Commitments:= (S1.Commitments × S2.Commitments);
                      Challenges:= Gcross S1.Challenges S2.Challenges; (*product group*)
                      Disjoint:= λ (a,b) (c,d). S1.Disjoint a c ∧ S2.Disjoint b d;
                      Responses:= (S1.Responses × S2.Responses);
                      Prover_0:= (λ (s1, s2) (w1, w2) (r1, r2). (S1.Prover_0 s1 w1 r1, S2.Prover_0 s2 w2 r2));
                      Prover_1:= (λ (s1, s2) (w1, w2) (r1, r2) (c1, c2) (e1, e2).
                                         (S1.Prover_1 s1 w1 r1 c1 e1, S2.Prover_1 s2 w2 r2 c2 e2));
                      HonestVerifier:= (λ ((s1, s2), (c1, c2), (e1, e2), (t1, t2)).
                                                S1.HonestVerifier (s1, c1, e1, t1) ∧ S2.HonestVerifier (s2, c2, e2, t2));
                      Extractor:= (λ (t1a, t1b) (t2a, t2b) (e1a, e1b) (e2a, e2b).
                                           (S1.Extractor t1a t2a e1a e2a, S2.Extractor t1b t2b e1b e2b));
                      Simulator:= (λ (s1, s2) (t1, t2) (e1, e2). let (s1', c1', e1', t1') = S1.Simulator s1 t1 e1;
                                                                     (s2', c2', e2', t2') = S2.Simulator s2 t2 e2
                                                                 in
                                                                   ((s1', s2'),(c1', c2'),(e1', e2'),(t1', t2')));
                                                                                                                        
                      SimulatorMap:= (λ (s1, s2) (w1, w2) (e1, e2) (r1, r2).
                                             (S1.SimulatorMap s1 w1 e1 r1, S2.SimulatorMap s2 w2 e2 r2));
                      SimulatorMapInverse:=   (λ (s1, s2) (w1, w2) (e1, e2) (t1, t2).
                                                      (S1.SimulatorMapInverse s1 w1 e1 t1, S2.SimulatorMapInverse s2 w2 e2 t2));
                     |> 
End



Definition SP_or'_def:
  SP_or' S1 S2 =  <|Statements:= S1.Statements × S2.Statements;

           
                      Witnesses:= S1.Witnesses;
                      Relation:= (λ (s1, s2) w. S1.Relation s1 w ∨ S2.Relation s2 w);
                      RandomCoins:= (S1.RandomCoins × (S1.Challenges.carrier × S2.Responses));
                      Commitments:= (S1.Commitments × S2.Commitments);
                      Challenges:= S1.Challenges;
                      Disjoint:= S1.Disjoint;
                      Responses:= (S1.Responses × (S1.Challenges.carrier × S2.Responses));
                                  
                      Prover_0:= (λ (s1, s2) w (r, (e, t)).
                                         if S1.Relation s1 w then
                                           let (s2', c2', e2', t2') = S2.Simulator s2 t e;
                                           in (S1.Prover_0 s1 w r, c2')
                                         else
                                           let (s1', c1', e1', t1') = S1.Simulator s1 t e;
                                           in (c1', S2.Prover_0 s2 w r));
                                                                
                      Prover_1:= (λ (s1, s2) w (rr,(re,rt)) (c1, c2) e.
                                    let   ere = SP_csub S1 e re
                                    in  if S1.Relation s1 w then
                                          let (s2', c2', e2', t2') = S1.Simulator s2 rt re;
                                          in (S1.Prover_1 s1 w rr c1 (ere), (re,t2'))
                                        else
                                          let  (s1', c1', e1', t1') = S1.Simulator s1 rt re;
                                          in (t1', (ere, S1.Prover_1 s2 w rr c2 ere)));
                                  
                                  
                      HonestVerifier:= (λ ((s1, s2), (c1, c2), e, (t1, (te,t2))).
                                          let ete = SP_csub S1 e te
                                          in S1.HonestVerifier (s1, c1, ete, t1) ∧ S1.HonestVerifier (s2, c2, te, t2));
                                                   
                      Extractor:= (λ (t1a, (t1e,t1b)) (t2a, (t2e,t2b)) e1 e2. if S1.Disjoint t1e t2e then
                                                                                    S1.Extractor t1b t2b t1e t2e
                                                                              else
                                                                                      
                                                                                    S1.Extractor t1a t2a (SP_csub S1 e1 t1e) (SP_csub S1 e2 t2e));
                                  
                      Simulator:= (λ (s1, s2) (t1, (te,t2)) e.
                                     let (s1', c1', e1', t1') = S1.Simulator s1 t1 (SP_csub S1 e te);
                                         (s2', c2', e2', t2') = S1.Simulator s2 t2 te
                                     in
                                       ((s1', s2'),(c1', c2'),e,(t1', (te, t2'))));
                                                                                                                        
                      SimulatorMap:= (λ (s1, s2) w e (rr,(re,rt)). if S1.Relation s1 w then
                                                                     (S1.SimulatorMap s1 w (SP_csub S1 e re) rr, (e, rt))
                                                                   else
                                                                     (rt, (e, S1.SimulatorMap s2 w e rr)));
                                     
                      SimulatorMapInverse:=   (λ (s1, s2) w e (t1, (te,t2)). if S1.Relation s1 w then
                                                                     (S1.SimulatorMapInverse s1 w (SP_csub S1 e te) t1, (e, t2))
                                                                   else
                                                                     ((S1.SimulatorMapInverse s2 w e t2), (e,t1)));
                     |> 
End
     


Definition SP_eq_def:
  SP_eq S1  =  <|Statements:= S1.Statements × S1.Statements;
                      Witnesses:= S1.Witnesses;
                      Relation:= (λ (s1, s2) w. S1.Relation s1 w ∧ S1.Relation s2 w);
                      RandomCoins:= S1.RandomCoins;
                      Commitments:= (S1.Commitments × S1.Commitments);
                      Challenges:= S1.Challenges;
                      Disjoint:= S1.Disjoint;
                      Responses:= S1.Responses;
                      Prover_0:= (λ (s1, s2) w r. (S1.Prover_0 s1 w r, S1.Prover_0 s2 w r));
                      Prover_1:= (λ (s1, s2) w r (c1, c2) e.
                                         (S1.Prover_1 s1 w r c1 e));
                      HonestVerifier:= (λ ((s1, s2), (c1, c2), e, t).
                                                S1.HonestVerifier (s1, c1, e, t) ∧ S1.HonestVerifier (s2, c2, e, t));
                      Extractor:= S1.Extractor;
                      Simulator:= (λ (s1, s2) t e. let (s1', c1', e1', t1') = S1.Simulator s1 t e;
                                                       (s2', c2', e2', t2') = S1.Simulator s2 t e
                                                   in
                                                     ((s1', s2'),(c1', c2'),e1', t1'));
                                                                                                                        
                      SimulatorMap:= (λ (s1, s2) w e r.
                                             (S1.SimulatorMap s1 w e r));
                      SimulatorMapInverse:=   (λ (s1, s2) w e t.
                                                      (S1.SimulatorMapInverse s1 w e t));
                     |> 
End






     
         

Definition WellFormed_SP_def:
  WellFormed_SP sp ⇔
    (
    (Group sp.Challenges) ∧
           
    (∀e1 e2. e1 ∈ sp.Challenges.carrier ∧  e2 ∈ sp.Challenges.carrier ⇒ (sp.Disjoint e1 e2 ⇒ (e1 ≠ e2))) ∧
         
    (∀s w r. s ∈ sp.Statements ∧ w ∈ sp.Witnesses ∧ r ∈ sp.RandomCoins ⇒
               sp.Prover_0 s w r ∈ sp.Commitments) ∧
               
    (∀s w r c e. s ∈ sp.Statements ∧ w ∈ sp.Witnesses ∧ r ∈ sp.RandomCoins ∧ c ∈ sp.Commitments ∧ e ∈ sp.Challenges.carrier  ⇒
                 sp.Prover_1 s w r c e ∈ sp.Responses) ∧
                 
    (∀t1 t2 e1 e2. t1 ∈ sp.Responses ∧ t2 ∈ sp.Responses ∧ e1 ∈ sp.Challenges.carrier ∧  e2 ∈ sp.Challenges.carrier ⇒
                   sp.Extractor t1 t2 e1 e2 ∈ sp.Witnesses) ∧
                   
    (∀s t e s' c' e' t'.
        s ∈ sp.Statements ∧ t ∈ sp.Responses ∧ e ∈ sp.Challenges.carrier ∧
                         sp.Simulator s t e = (s', c', e', t') ⇒
                         s' = s ∧
                         e' = e ∧
                         t' = t ∧
                         c' ∈ sp.Commitments) ∧               
         
    (∀s w r e. s ∈ sp.Statements ∧ w ∈ sp.Witnesses ∧ r ∈ sp.RandomCoins ∧ e ∈ sp.Challenges.carrier  ⇒
               sp.SimulatorMap s w e r  ∈ sp.Responses) ∧
               
    (∀s w t e. s ∈ sp.Statements ∧ w ∈ sp.Witnesses ∧ t ∈ sp.Responses ∧ e ∈ sp.Challenges.carrier  ⇒
               sp.SimulatorMapInverse s w e t  ∈ sp.RandomCoins)


    Only for EQ combiner
         need That SImMap ignores statements, same for mimmapinverse
               )
End


        

        
(*Correctness property: Correct Prover get accepted by Verifier*)
Definition Correct_SP_def:
  Correct_SP sp ⇔
    (∀s w r e. s ∈ sp.Statements ∧ w ∈ sp.Witnesses ∧ r ∈ sp.RandomCoins ∧ e ∈ sp.Challenges.carrier
                ∧ sp.Relation s w ⇒
                              let c =  sp.Prover_0 s w r in 
                                sp.HonestVerifier(s, c, e, sp.Prover_1 s w r c e))
                                        
End  


Definition SpecialSoundness_SP_def:
  SpecialSoundness_SP sp ⇔
  ∀s c e1 e2 t1 t2.
     s ∈ sp.Statements ∧
     c ∈ sp.Commitments ∧
     t1 ∈ sp.Responses ∧
     t2 ∈ sp.Responses ∧
     e1 ∈ sp.Challenges.carrier ∧
     e2 ∈ sp.Challenges.carrier ∧
     sp.Disjoint e1 e2 ∧ 
     sp.HonestVerifier(s, c, e1, t1) ∧
     sp.HonestVerifier(s, c, e2, t2) ⇒
                    sp.Relation s (sp.Extractor t1 t2 e1 e2) 
End


Definition SimulatorCorrectness_SP_def:
  SimulatorCorrectness_SP sp ⇔
  ∀s t e.
     s ∈ sp.Statements ∧
     t ∈ sp.Responses ∧
     e ∈ sp.Challenges.carrier ⇒
     sp.HonestVerifier(sp.Simulator s t e) 
End

Definition HonestVerifierZeroKnowledge_SP_def:
   HonestVerifierZeroKnowledge_SP sp ⇔
  ∀s w r e t.
     s ∈ sp.Statements ∧
     w ∈ sp.Witnesses ∧
     r ∈ sp.RandomCoins ∧
     e ∈ sp.Challenges.carrier ∧
     t ∈ sp.Responses ∧
     sp.Relation s w ⇒
     let c =  sp.Prover_0 s w r;
         spm = sp.SimulatorMap s w e;
         spmi = sp.SimulatorMapInverse s w e;
     in
       sp.Simulator s (spm r) e = (s, c, e, sp.Prover_1 s w r c e) ∧
       spmi(spm r) = r ∧
       spm(spmi t) = t
End

        


Theorem WellFormed_SP_and_thm:
 WellFormed_SP sp1 ∧ WellFormed_SP sp2 ⇒ WellFormed_SP (SP_and sp1 sp2)
Proof

        
  simp[WellFormed_SP_def, SP_and_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac >-

 (
 ‘Group (Gcross sp1.Challenges sp2.Challenges)’by metis_tac[Gcross_group_thm]
 )>>

 (

          rpt (pairarg_tac>>
               gvs[])>>
          fs[Gcross_def,FST, SND, CROSS_DEF]>>
          gs[WellFormed_SP_def, FST, SND, CROSS_DEF]>>
          metis_tac[FST, SND, CROSS_DEF]
  
 )
QED
 

Theorem Correct_SP_and_thm:
  Correct_SP sp1 ∧ Correct_SP sp2 ⇒ Correct_SP (SP_and sp1 sp2)
Proof
  simp[Correct_SP_def, SP_and_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac >-

   (
   gs[]>>
   ‘p_1'³' ∈ sp1.Challenges.carrier’ by fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[]
   )>-
   (
   ‘p_2'³' ∈ sp2.Challenges.carrier’ by fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[]
   )     
QED


Theorem  SpecialSoundness_SP_and_thm:
  SpecialSoundness_SP sp1 ∧ SpecialSoundness_SP sp2
                      ⇒ SpecialSoundness_SP (SP_and sp1 sp2)
Proof
  simp[SpecialSoundness_SP_def, SP_and_def,  pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
  ‘ p_1'' ∈ sp1.Challenges.carrier ∧ p_1'³' ∈ sp1.Challenges.carrier’ by fs[Gcross_def,FST, SND, CROSS_DEF]>>
  ‘sp1.Relation p_1 (sp1.Extractor p_1'⁴' p_1'⁵' p_1'' p_1'³')’ by metis_tac[]>>
  ‘ p_2'' ∈ sp2.Challenges.carrier ∧ p_2'³' ∈ sp2.Challenges.carrier’ by fs[Gcross_def,FST, SND, CROSS_DEF]>>
  ‘sp2.Relation p_2 (sp2.Extractor p_2'⁴' p_2'⁵' p_2'' p_2'³')’ by metis_tac[]
QED


Theorem SimulatorCorrectness_SP_and_thm:
    SimulatorCorrectness_SP sp1 ∧ SimulatorCorrectness_SP sp2
    ⇒ SimulatorCorrectness_SP (SP_and sp1 sp2)
Proof                    
  simp[SimulatorCorrectness_SP_def, SP_and_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac >>
  ‘ p_1'' ∈ sp1.Challenges.carrier ∧ p_2'' ∈ sp2.Challenges.carrier’ by fs[Gcross_def,FST, SND, CROSS_DEF]>>
  pairarg_tac>> 
  gvs[]>>
  pairarg_tac>> 
  gvs[]>>
  pairarg_tac>> 
  gvs[]>>
metis_tac[]       
QED


Theorem HonestVerifierZeroKnowledge_SP_and_thm:
  HonestVerifierZeroKnowledge_SP sp1 ∧ HonestVerifierZeroKnowledge_SP sp2 ∧
  WellFormed_SP sp1 ∧ WellFormed_SP sp2 ⇒ HonestVerifierZeroKnowledge_SP (SP_and sp1 sp2)
Proof
  simp[HonestVerifierZeroKnowledge_SP_def, SP_and_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac >-
      
   (
   qabbrev_tac‘s1 = p_1’>> qabbrev_tac‘s2 = p_2’>>   qabbrev_tac‘w1 = p_1' ’>> qabbrev_tac‘w2 = p_2' ’>>
   qabbrev_tac‘r1 = p_1'' ’>> qabbrev_tac‘r2 = p_2'' ’>>   qabbrev_tac‘e1 = p_1'³'’>> qabbrev_tac‘e2 = p_2'³'’>>             
   qabbrev_tac‘t1 =  p_1'⁴'’>> qabbrev_tac‘t2 =   p_2'⁴'’>>
                  
   ‘ e1 ∈ sp1.Challenges.carrier ∧ e2 ∈ sp2.Challenges.carrier’ by fs[Gcross_def,FST, SND, CROSS_DEF]>>
   ‘sp1.SimulatorMapInverse s1 w1 e1 (sp1.SimulatorMap s1 w1 e1 r1) = r1 ∧
    sp1.SimulatorMap s1 w1 e1 (sp1.SimulatorMapInverse s1 w1 e1 t1) = t1 ∧
    sp2.SimulatorMapInverse s2 w2 e2 (sp2.SimulatorMap s2 w2 e2 r2) = r2 ∧
    sp2.SimulatorMap s2 w2 e2 (sp2.SimulatorMapInverse s2 w2 e2 t2) = t2’by metis_tac[]>>
   ‘WellFormed_SP (SP_and sp1 sp2)’by metis_tac[WellFormed_SP_and_thm]>>
   ‘sp1.Prover_0 s1 w1 r1 ∈ sp1.Commitments ∧ sp2.Prover_0 s2 w2 r2 ∈ sp2.Commitments’by metis_tac[WellFormed_SP_def]>>
                 
   qabbrev_tac‘c1 = sp1.Prover_0 s1 w1 r1’>> qabbrev_tac‘c2 = sp2.Prover_0 s2 w2 r2’>>
   qabbrev_tac‘t11 = sp1.Prover_1 s1 w1 r1 c1 e1’>>
   qabbrev_tac‘t22 = sp2.Prover_1 s2 w2 r2 c2 e2’>>
   qabbrev_tac‘t222 = sp2.SimulatorMap s2 w2 e2 r2’>>
   qabbrev_tac‘t111 = sp1.SimulatorMap s1 w1 e1 r1’>>
   qabbrev_tac‘x1 = sp1.Simulator s1 t111 e1’>>
   qabbrev_tac‘x2 = sp2.Simulator s2 t222 e2’>>
                  
   ‘(sp1.Prover_1 s1 w1 r1 c1 e1) ∈ sp1.Responses’by metis_tac[WellFormed_SP_def] >> 
   ‘t11 ∈ sp1.Responses’by metis_tac[]>>
   ‘t11 ∈ sp1.Responses ∧ t111 ∈ sp1.Responses ∧ t22 ∈ sp2.Responses ∧ t222 ∈ sp2.Responses’by metis_tac[WellFormed_SP_def] >> 
   ‘sp1.Simulator s1 t111 e1 =  sp1.Simulator s1 (sp1.SimulatorMap s1 w1 e1 r1) e1’by rw[]>>
   ‘sp1.Simulator s1 (sp1.SimulatorMap s1 w1 e1 r1) e1 =
    (s1,sp1.Prover_0 s1 w1 r1, e1, sp1.Prover_1 s1 w1 r1 (sp1.Prover_0 s1 w1 r1) e1)’ by metis_tac[]>>
   ‘(s1,sp1.Prover_0 s1 w1 r1, e1, sp1.Prover_1 s1 w1 r1 (sp1.Prover_0 s1 w1 r1) e1) = (s1, c1, e1, t11)’by metis_tac[]>>
   ‘x1 =  (s1, c1, e1, t11)’by gs[]>>
       
   ‘sp2.Simulator s2 t222 e2 =
    sp2.Simulator s2 (sp2.SimulatorMap s2 w2 e2 r2) e2’by rw[]>>
   ‘sp2.Simulator s2 (sp2.SimulatorMap s2 w2 e2 r2) e2 =
    (s2,sp2.Prover_0 s2 w2 r2, e2, sp2.Prover_1 s2 w2 r2 (sp2.Prover_0 s2 w2 r2) e2)’ by metis_tac[]>>
   ‘(s2,sp2.Prover_0 s2 w2 r2, e2, sp2.Prover_1 s2 w2 r2 (sp2.Prover_0 s2 w2 r2) e2) = (s2, c2, e2, t22)’by metis_tac[]>>
   ‘x2 =  (s2, c2, e2, t22)’by metis_tac[]>>
   ‘(λ(s1',c1',e1',t1').(λ(s2',c2',e2',t2'). ((s1',s2'),(c1',c2'),(e1',e2'),t1',t2'))  (s2, c2, e2, t22)) (s1, c1, e1, t11) =
    ((s1,s2),(c1,c2),(e1,e2),(t11,t22))’by rw[]>>
   ‘ ((s1,s2),(c1,c2),(e1,e2),t11,t22) =
     (λ(s1',c1',e1',t1').
        (λ(s2',c2',e2',t2'). ((s1',s2'),(c1',c2'),(e1',e2'),t1',t2')) x2)
     x1’by metis_tac[]>>
     metis_tac[]
     )>-
     
   (
   gs[Gcross_def,FST, SND, CROSS_DEF]>>
    ‘sp1.SimulatorMapInverse p_1 p_1' p_1'³' (sp1.SimulatorMap p_1 p_1' p_1'³' p_1'') = p_1''’by metis_tac[]
    )>-
    
   (gs[Gcross_def,FST, SND, CROSS_DEF]>>
    ‘sp2.SimulatorMapInverse p_2 p_2' p_2'³'
     (sp2.SimulatorMap p_2 p_2' p_2'³' p_2'') =
     p_2''’by metis_tac[])>-
     
   (gs[Gcross_def,FST, SND, CROSS_DEF]>>
    ‘sp1.SimulatorMap p_1 p_1' p_1'³'
     (sp1.SimulatorMapInverse p_1 p_1' p_1'³' p_1'⁴') =
     p_1'⁴'’by metis_tac[])>-
     
   (gs[Gcross_def,FST, SND, CROSS_DEF]>>
    ‘  sp2.SimulatorMap p_2 p_2' p_2'³'
       (sp2.SimulatorMapInverse p_2 p_2' p_2'³' p_2'⁴') =
       p_2'⁴'’by metis_tac[])
   
QED

 
Theorem WellFormed_SP_or_thm:
 WellFormed_SP sp1  ⇒ WellFormed_SP (SP_or sp1)
Proof   
  rw[]>>
  simp[WellFormed_SP_def, SP_or_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac >-                   

(
   rpt 3 times
        ( 
          rpt (pairarg_tac>>
               gvs[])>>
          fs[Gcross_def,FST, SND, CROSS_DEF]>>
          gs[WellFormed_SP_def, FST, SND, CROSS_DEF]>>
          metis_tac[FST, SND, CROSS_DEF]
        )
)
qabbrev_tac‘e1 = SP_csub sp1 e p_2''’>>
  ‘e1 ∈ sp1.Challenges.carrier’by metis_tac[SP_csub_Lemma]>>
  qabbrev_tac‘t1 = sp1.Prover_1 p_1 w p_1' p_1'' e1’>>
  ‘t1 ∈ sp1.Responses’by metis_tac[WellFormed_SP_def]>>
      qabbrev_tac‘t2 = sp1.Prover_1 p_2 w p_1' p_2'³' e1’>>
  ‘t2 ∈ sp1.Responses’by metis_tac[WellFormed_SP_def]>>
  Cases_on ‘sp1.Relation p_1 w’ >| [
    fs[]>>
          qabbrev_tac‘sa = FST (sp1.Simulator p_2 p_2' p_2'')’>>
  qabbrev_tac‘ca = FST (SND (sp1.Simulator p_2 p_2' p_2''))’>>
  qabbrev_tac‘ea = FST (SND (SND (sp1.Simulator p_2 p_2' p_2'')))’>>
  qabbrev_tac‘ta = SND (SND (SND (sp1.Simulator p_2 p_2' p_2'')))’>>
                 
    ‘sp1.Simulator p_2 p_2' p_2'' = (sa, ca, ea, ta)’ by rw[pairTheory.PAIR, Abbr‘sa’, Abbr‘ca’, Abbr‘ea’, Abbr‘ta’ ] >>
    fs[]
        ,
    fs[]>>
                  qabbrev_tac‘sa = FST (sp1.Simulator p_1 p_2' p_2'')’>>
  qabbrev_tac‘ca = FST (SND (sp1.Simulator p_1 p_2' p_2''))’>>
  qabbrev_tac‘ea = FST (SND (SND (sp1.Simulator p_1 p_2' p_2'')))’>>
  qabbrev_tac‘ta = SND (SND (SND (sp1.Simulator p_1 p_2' p_2'')))’>>
                 
    ‘sp1.Simulator p_1 p_2' p_2'' = (sa, ca, ea, ta)’ by rw[pairTheory.PAIR, Abbr‘sa’, Abbr‘ca’, Abbr‘ea’, Abbr‘ta’ ] >>
    rw[]>>
         ‘p_2' = ta’by metis_tac[WellFormed_SP_def]>>         
    fs[]
        ]
        
)>-
        Cases_on ‘sp1.Relation p_1 w’ >| [
    fs[]>>
qabbrev_tac‘e1 = SP_csub sp1 e p_2''’>>
    ‘e1 ∈ sp1.Challenges.carrier’by metis_tac[SP_csub_Lemma, WellFormed_SP_def]>>
  qabbrev_tac‘t1 = sp1.Prover_1 p_1 w p_1' p_1'' e1’>>
    ‘t1 ∈ sp1.Responses’by metis_tac[WellFormed_SP_def]>>
    fs[]>>
                  qabbrev_tac‘sa = FST (sp1.Simulator p_2 p_2' p_2'')’>>
  qabbrev_tac‘ca = FST (SND (sp1.Simulator p_2 p_2' p_2''))’>>
  qabbrev_tac‘ea = FST (SND (SND (sp1.Simulator p_2 p_2' p_2'')))’>>
  qabbrev_tac‘ta = SND (SND (SND (sp1.Simulator p_2 p_2' p_2'')))’>>
                 
    ‘sp1.Simulator p_2 p_2' p_2'' = (sa, ca, ea, ta)’ by rw[pairTheory.PAIR, Abbr‘sa’, Abbr‘ca’, Abbr‘ea’, Abbr‘ta’ ] >>
    fs[]
        ,
    fs[]>>
                          qabbrev_tac‘sa = FST (sp1.Simulator p_1 p_2' p_2'')’>>
  qabbrev_tac‘ca = FST (SND (sp1.Simulator p_1 p_2' p_2''))’>>
  qabbrev_tac‘ea = FST (SND (SND (sp1.Simulator p_1 p_2' p_2'')))’>>
  qabbrev_tac‘ta = SND (SND (SND (sp1.Simulator p_1 p_2' p_2'')))’>>
                 
    ‘sp1.Simulator p_1 p_2' p_2'' = (sa, ca, ea, ta)’ by rw[pairTheory.PAIR, Abbr‘sa’, Abbr‘ca’, Abbr‘ea’, Abbr‘ta’ ] >>
    fs[]
  ]
                                                

        Cases_on ‘sp1.Relation p_1 w’ >| [
    fs[]>>
    qabbrev_tac‘e1 = SP_csub sp1 e p_2''’>>
    ‘e1 ∈ sp1.Challenges.carrier’by metis_tac[SP_csub_Lemma, WellFormed_SP_def]>>
    qabbrev_tac‘t1 = sp1.Prover_1 p_1 w p_1' p_1'' e1’>>
    ‘t1 ∈ sp1.Responses’by metis_tac[WellFormed_SP_def]>>
    fs[]>>
    qabbrev_tac‘sa = FST (sp1.Simulator p_2 p_2' p_2'')’>>
    qabbrev_tac‘ca = FST (SND (sp1.Simulator p_2 p_2' p_2''))’>>
    qabbrev_tac‘ea = FST (SND (SND (sp1.Simulator p_2 p_2' p_2'')))’>>
    qabbrev_tac‘ta = SND (SND (SND (sp1.Simulator p_2 p_2' p_2'')))’>>
    ‘sp1.Simulator p_2 p_2' p_2'' = (sa, ca, ea, ta)’ by rw[pairTheory.PAIR, Abbr‘sa’, Abbr‘ca’, Abbr‘ea’, Abbr‘ta’ ] >>
    fs[]>>
    ‘p_2' = ta’by metis_tac[WellFormed_SP_def]>>
    fs[]
        ,
    fs[]>>
qabbrev_tac‘e1 = SP_csub sp1 e p_2''’>>
    ‘e1 ∈ sp1.Challenges.carrier’by metis_tac[SP_csub_Lemma, WellFormed_SP_def]>>
  qabbrev_tac‘t1 = sp1.Prover_1 p_2 w p_1' p_2''' e1’>>
    ‘t1 ∈ sp1.Responses’by metis_tac[WellFormed_SP_def]>>
    fs[]>>
    qabbrev_tac‘sa = FST (sp1.Simulator p_1 p_2' p_2'')’>>
  qabbrev_tac‘ca = FST (SND (sp1.Simulator p_1 p_2' p_2''))’>>
  qabbrev_tac‘ea = FST (SND (SND (sp1.Simulator p_1 p_2' p_2'')))’>>
  qabbrev_tac‘ta = SND (SND (SND (sp1.Simulator p_1 p_2' p_2'')))’>>      
    ‘sp1.Simulator p_1 p_2' p_2'' = (sa, ca, ea, ta)’ by rw[pairTheory.PAIR, Abbr‘sa’, Abbr‘ca’, Abbr‘ea’, Abbr‘ta’ ] >>
    fs[]
  ]

                                         
    Cases_on ‘p_2 ≠ p_2'' ’ >| [       
    fs[]>>
    metis_tac[WellFormed_SP_def, SP_or_def]
                                 ,
    fs[]>>
    metis_tac[WellFormed_SP_def, SP_or_def, SP_csub_Lemma]
  ]

          rpt (pairarg_tac>>
               gvs[])>-
               
  rpt (pairarg_tac>>
       gvs[])>-


      rpt (pairarg_tac>>
           gvs[])>-

  rpt (pairarg_tac>>
       gvs[])>>
 metis_tac[WellFormed_SP_def]

          rpt (pairarg_tac>>
               gvs[])>-

          rpt (pairarg_tac>>
               gvs[])>>
 metis_tac[WellFormed_SP_def, SP_or_def, SP_csub_Lemma]

    rpt (pairarg_tac>>
       gvs[])>>                  
 metis_tac[WellFormed_SP_def]

           rpt (pairarg_tac>>
               gvs[])>>
 metis_tac[WellFormed_SP_def, SP_or_def, SP_csub_Lemma]

          Cases_on ‘sp1.Relation p_1 w’ >| [
    fs[]>>
qabbrev_tac‘e1 = SP_csub sp1 e p_2''’>>
    ‘e1 ∈ sp1.Challenges.carrier’by metis_tac[SP_csub_Lemma]>>
    ‘e1 ∈ sp1.Challenges.carrier’by metis_tac[SP_csub_Lemma, WellFormed_SP_def]>>
    metis_tac[WellFormed_SP_def, SP_or_def, SP_csub_Lemma]
  ]
                                                )>-
        

 fs[]>-
 fs[]>>
                                                 Cases_on ‘sp1.Relation p_1 w’ >| [
                                                          fs[]>>
                
                                                          metis_tac[SP_csub_Lemma]>>
                                                          ,
                                                          fs[]]
                                                                                        
                                                                                  Cases_on ‘sp1.Relation p_1 w’ >| [
                                                    fs[]
                                                        ,
                                                        fs[]>>
                                                        metis_tac[WellFormed_SP_def, SP_or_def, SP_csub_Lemma]    
                                                  ]
            fs[]>>  
                                                 Cases_on ‘sp1.Relation p_1 w’ >|[
                                                    fs[]>>
                                                    metis_tac[WellFormed_SP_def, SP_or_def]
                                                    ,
                                                    fs[]>>
                                                         metis_tac[WellFormed_SP_def, SP_or_def, SP_csub_Lemma]
                                                  ]

                                                                                 Cases_on ‘sp1.Relation p_1 w’ >|[
                                                    fs[]>>
                                                    metis_tac[WellFormed_SP_def, SP_or_def]
                                                    ,
                                                    fs[]>>
                                                         metis_tac[WellFormed_SP_def, SP_or_def, SP_csub_Lemma]
                                                  ]

                                                                                                                 Cases_on ‘sp1.Relation p_1 w’ >|[
                                                    fs[]>>
                                                    metis_tac[WellFormed_SP_def, SP_or_def, SP_csub_Lemma]
                                                    ,
                                                        fs[]>>

                                                                                        
QED









        

Theorem SP_csub_Lemma:
  ∀sp x y.
  WellFormed_SP sp ∧
       x ∈ sp.Challenges.carrier ∧
           y ∈ sp.Challenges.carrier ⇒
             SP_csub sp x y ∈ sp.Challenges.carrier
Proof
  simp[SP_csub_def, SP_or_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac >>  
  qabbrev_tac‘y1 = sp.Challenges.inv y’>>
  qabbrev_tac‘Gr = sp.Challenges’>>
  ‘Group Gr’by metis_tac[WellFormed_SP_def]>>
  ‘y1 ∈ Gr.carrier’ by metis_tac[group_inv_element]>>
  ‘Gr.op x y1 ∈ Gr.carrier’ by metis_tac[group_op_element]
QED



Theorem SimulatorCorrectness_SP_or_thm:
  SimulatorCorrectness_SP sp1 ∧ WellFormed_SP sp1 ⇒ SimulatorCorrectness_SP (SP_or sp1)
Proof
  simp[SimulatorCorrectness_SP_def, SP_or_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac >>
  
  qabbrev_tac‘s1 = p_1’>> qabbrev_tac‘s2 = p_2’>>   qabbrev_tac‘t1 = p_1' ’>>
  qabbrev_tac‘e1 = p_2' ’>>  qabbrev_tac‘t2 = p_2'' ’>>
                 
  qabbrev_tac‘e2 = (SP_csub sp1 e e1)’>> qabbrev_tac‘c1 = sp1.Prover_0 s1 w r1’>>
  ‘e2  ∈ sp1.Challenges.carrier’by metis_tac[SP_csub_Lemma]>>
   qabbrev_tac‘t3 = sp1.Prover_1 s1 w r1 c1 e2’>>

  qabbrev_tac‘sa = FST (sp1.Simulator s1 t1 e1)’>>
  qabbrev_tac‘ca = FST (SND (sp1.Simulator s1 t1 e1))’>>
  qabbrev_tac‘ea = FST (SND (SND (sp1.Simulator s1 t1 e1)))’>>
  qabbrev_tac‘ta = SND (SND (SND (sp1.Simulator s1 t1 e1)))’>>
                 
  ‘sp1.Simulator s1 t1 e1 = (sa, ca, ea, ta)’ by rw[pairTheory.PAIR, Abbr‘sa’, Abbr‘ca’, Abbr‘ea’, Abbr‘ta’ ] >>
                 
  qabbrev_tac‘sb = FST (sp1.Simulator s2 t2 e2)’>>
  qabbrev_tac‘cb = FST (SND (sp1.Simulator s2 t2 e2))’>>
  qabbrev_tac‘eb = FST (SND (SND (sp1.Simulator s2 t2 e2)))’>>
  qabbrev_tac‘tb = SND (SND (SND (sp1.Simulator s2 t2 e2)))’>>
                 
  ‘sp1.Simulator s2 t2 e2 = (sb, cb, eb, tb)’ by rw[pairTheory.PAIR, Abbr‘sb’, Abbr‘cb’, Abbr‘eb’, Abbr‘tb’ ] >>

  gs[]>>
  metis_tac[WellFormed_SP_def] 
QED       
        
(* e1 - (e-e') = e-e+e' = e' *)
Theorem SP_csub_Lemma2:
  ∀sp x y z.
  WellFormed_SP sp ∧
  x ∈ sp.Challenges.carrier ∧
  y ∈ sp.Challenges.carrier ⇒
             SP_csub sp x (SP_csub sp x y) = y
Proof
  simp[SP_csub_def, SP_or_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac >>  
  qabbrev_tac‘Gr = sp.Challenges’>>
  ‘Group Gr’by metis_tac[WellFormed_SP_def]>>
  ‘Gr.inv y ∈ Gr.carrier’by metis_tac[group_inv_element]>>
  ‘Gr.op x (Gr.inv y) ∈ Gr.carrier’ by metis_tac[group_op_element]>>
  qabbrev_tac‘z = Gr.inv (Gr.op x (Gr.inv y))’>>
  qabbrev_tac‘s = Gr.inv y’>>    
  ‘Gr.inv (Gr.op x s) = Gr.op (Gr.inv s) (Gr.inv x)’by metis_tac[group_inv_op]>>

          
  ‘Gr.inv s = y’by metis_tac[group_inv_inv]>>
  ‘z = Gr.op (Gr.inv x) y’by metis_tac[]>>
  ‘ Gr.op x z =  Gr.op x (Gr.op (Gr.inv x) y)’ by metis_tac[]>>
  ‘Gr.op x (Gr.op (Gr.inv x) y) = y’ by metis_tac[group_linv_assoc]>>
  fs[]
QED


Theorem SP_csub_Lemma3:
  ∀sp e1 e2 e3 e4.
  WellFormed_SP sp ∧
  e1 ∈ sp.Challenges.carrier ∧
  e2 ∈ sp.Challenges.carrier ∧
  e3 ∈ sp.Challenges.carrier ∧
  e4 ∈ sp.Challenges.carrier ∧
  e1 ≠ e2 ∧ e3 = e4
  ⇒ (SP_csub sp e1 e3) ≠ (SP_csub sp e2 e4) 
           
Proof
cheat
QED
        

Theorem Correct_SP_or_thm:
  Correct_SP sp1 ∧ SimulatorCorrectness_SP sp1 ∧ WellFormed_SP sp1 ⇒ Correct_SP (SP_or sp1)
Proof
  rw[]>>
  simp[Correct_SP_def, SP_or_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac >-
   (
   rpt (pairarg_tac>>
        gvs[])>>
   qabbrev_tac‘s1 = p_1’>> qabbrev_tac‘s2 = p_2’>>
   qabbrev_tac‘r1 = p_1' ’>>
   qabbrev_tac‘t1 = p_2' ’>>
   qabbrev_tac‘e1 = p_2'' ’>>
   qabbrev_tac‘e2 = (SP_csub sp1 e e1)’>> qabbrev_tac‘c1 = sp1.Prover_0 s1 w r1’>>
   qabbrev_tac‘t3 = sp1.Prover_1 s1 w r1 c1 e2’>>         
   ‘e2 ∈ sp1.Challenges.carrier’ by metis_tac[SP_csub_Lemma]>>
         drule_then assume_tac (cj 1 (iffLR Correct_SP_def))>>         
         first_assum$ qspecl_then [‘s1’, ‘w’, ‘r1’, ‘e2’] mp_tac>>
   ‘sp1.HonestVerifier (s1,c1,e2,t3)’by metis_tac[]>>
   fs[]>>
   ‘s2 = s2' ∧ e1 = e2'’ by metis_tac[WellFormed_SP_def]>> 
   ‘sp1.Simulator s2 t1 e1 = (s2,c2,e1,t2)’by rw[]>>
   ‘SP_csub sp1 e e2 = e1’by metis_tac[SP_csub_Lemma2]>>  
   metis_tac[SimulatorCorrectness_SP_def]
   )>-  
   (
   rpt (pairarg_tac>>
        gvs[])>>
   qabbrev_tac‘s1 = p_1’>> qabbrev_tac‘s2 = p_2’>>
   qabbrev_tac‘r1 = p_1' ’>>
   qabbrev_tac‘t1 = p_2' ’>>
   qabbrev_tac‘e1 = p_2'' ’>>
   Cases_on ‘sp1.Relation s1 w’ >| [
       ‘((sp1.Prover_1 s1 w r1 c1 (SP_csub sp1 e e1),SP_csub sp1 e e1),t2') =   ((t1,e2),t2)’by metis_tac[]>>
       ‘(sp1.Prover_0 s1 w r1,c2') = (c1, c2)’by metis_tac[]>>
       ‘c1 = sp1.Prover_0 s1 w r1’ by metis_tac[Gcross_def,FST, SND, CROSS_DEF]>>
       ‘e2 = SP_csub sp1 e e1’by metis_tac[Gcross_def,FST, SND, CROSS_DEF]>>
       ‘e2 ∈ sp1.Challenges.carrier’ by metis_tac[SP_csub_Lemma]>>
       ‘t1 = sp1.Prover_1 s1 w r1 c1 e2’by metis_tac[Gcross_def,FST, SND, CROSS_DEF]>>
       ‘sp1.HonestVerifier (s1,c1,e2,t1)’by metis_tac[Correct_SP_def]>>

       ‘SP_csub sp1 e e2 = e1’by metis_tac[SP_csub_Lemma2]>>
       ‘s2 = s2' ∧ e1 = e2'’ by metis_tac[WellFormed_SP_def]>> (* Simulator does not change s and e *)
       ‘t2 = t2' ∧ c2 = c2'’by  metis_tac[Gcross_def,FST, SND, CROSS_DEF]>>
       ‘ sp1.HonestVerifier (s2,c2,SP_csub sp1 e e2,t2)’by metis_tac[SimulatorCorrectness_SP_def]>>
       fs[],
        
       ‘(c1',sp1.Prover_0 s2 w r1) = (c1,c2)’by metis_tac[]>>              
       ‘((t1',e1),sp1.Prover_1 s2 w r1 c2 (SP_csub sp1 e e1)) = ((t1,e2),t2)’by metis_tac[]>>
       ‘c1' = c1 ∧ c2 = sp1.Prover_0 s2 w r1 ∧ t1' = t1 ∧ e1 = e2 ∧ sp1.Prover_1 s2 w r1 c2 (SP_csub sp1 e e1) = t2’
         by  metis_tac[Gcross_def,FST, SND, CROSS_DEF]>>
       ‘s1 = s1' ∧ s2 = s2'∧ e1 = e1' ∧ e1 = e2'’ by metis_tac[WellFormed_SP_def]>> 
       ‘sp1.HonestVerifier (s1,c1,e2,t1)’by metis_tac[SimulatorCorrectness_SP_def]>>
                          
       qabbrev_tac‘e3 = SP_csub sp1 e e1 ’>>
       ‘e3 = SP_csub sp1 e e2’by rw[]>>
       ‘e3 ∈ sp1.Challenges.carrier’ by metis_tac[SP_csub_Lemma]>>
       ‘sp1.HonestVerifier (s2,c2,e3,t2)’by metis_tac[Correct_SP_def]>>
       gs[]  
     ]
   )
QED



(*TODO try to exhaus the cases without assumption (Disj ⇔ not Eq) *)
Theorem  SpecialSoundness_SP_or_thm:
  ∀sp. WellFormed_SP sp1 ∧
       SpecialSoundness_SP sp1 ∧
       (∀e1 e2. e1 ∈ sp1.Challenges.carrier ∧
                e2 ∈ sp1.Challenges.carrier ⇒
                (sp1.Disjoint e1 e2 ⇔ e1 ≠ e2))
       ⇒ SpecialSoundness_SP (SP_or sp1)
Proof
  rw[]>>
  simp[SpecialSoundness_SP_def, SP_or_def, pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
        
  qabbrev_tac‘s1 = p_1’>> qabbrev_tac‘s2 = p_2’>>
  qabbrev_tac‘c1 = p_1' ’>> qabbrev_tac‘c2 = p_2' ’>>
  qabbrev_tac‘t1 = p_1'' ’>> qabbrev_tac‘t2 = p_2'³'’>>   qabbrev_tac‘t3 = p_1'³'’>>  qabbrev_tac‘t4 = p_2'⁵'’>>
  qabbrev_tac‘e3 = p_2'' ’>>  qabbrev_tac‘e4 = p_2'''' ’>>
  qabbrev_tac‘e5 = SP_csub sp1 e1 e3 ’>> qabbrev_tac‘e6 = SP_csub sp1 e2 e4 ’>>

  ‘e5 ∈ sp1.Challenges.carrier ∧ e6 ∈ sp1.Challenges.carrier’ by metis_tac[SP_csub_Lemma]>>

  Cases_on ‘e3 ≠ e4’ THENL [
    qabbrev_tac‘w =  (if e3 ≠ e4 then sp1.Extractor t1 t3 e3 e4
                      else sp1.Extractor t2 t4 e5 e6)’>>
    ‘w = sp1.Extractor t1 t3 e3 e4’ by metis_tac[]>>
    ‘sp1.Relation s1 w’by metis_tac[SpecialSoundness_SP_def]>>
    fs[]>>
    rw[] ,

    qabbrev_tac ‘w = (if sp1.Disjoint e3 e4 then sp1.Extractor t1 t3 e3 e4
                      else sp1.Extractor t2 t4 e5 e6)’>>
    ‘w = sp1.Extractor t2 t4 e5 e6’ by metis_tac[]>>
    ‘e3 = e4’ by metis_tac[]>>
    ‘e5 ≠ e6’ by metis_tac[ SP_csub_Lemma3]>>
    ‘sp1.Disjoint e5 e6’ by metis_tac[]>> 
    ‘sp1.Relation s2 w’by metis_tac[SpecialSoundness_SP_def]>>
    rw[]
    ] 
QED




Theorem HonestVerifierZeroKnowledge_SP_or_thm:
  HonestVerifierZeroKnowledge_SP sp ∧ WellFormed_SP sp ⇒ HonestVerifierZeroKnowledge_SP (SP_or sp)
Proof
  rw[]>>
  simp[HonestVerifierZeroKnowledge_SP_def, SP_or_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac >-
   (
   rpt (pairarg_tac>>
           gvs[])>>
      qabbrev_tac‘s1 = p_1’>> qabbrev_tac‘s2 = p_2’>>
      qabbrev_tac‘r = p_1' ’>> qabbrev_tac‘t1 = p_2' ’>>
      qabbrev_tac‘e1 = p_2'' ’>>              
      qabbrev_tac‘t2 = p_1'' ’>>
      qabbrev_tac‘e2 = p_2'³'’>>
      qabbrev_tac‘t3 = p_2'''' ’>>
      qabbrev_tac‘e3 = SP_csub sp e e1’>>
      ‘e3 ∈ sp.Challenges.carrier’by metis_tac[SP_csub_Lemma]>>
      qabbrev_tac‘t4 = sp.SimulatorMap s1 w e3 r’>>
      ‘ t4 ∈ sp.Responses’by metis_tac[WellFormed_SP_def]>>
      ‘SP_csub sp e e3 = e1’by metis_tac[SP_csub_Lemma2]>>
      ‘ sp.Simulator s2 t1 e1 = (s2',c2',e2',t2')’by metis_tac[]>>
      ‘s1 = s1' ∧  t4 = t1' ∧  e3 = e1'’by metis_tac[WellFormed_SP_def]>>
      ‘ s2 = s2'' ∧ t1 = t2'' ∧  e1 = e2''’by metis_tac[WellFormed_SP_def]>>
      ‘ s2 = s2' ∧ t1 = t2' ∧  e1 = e2'’by metis_tac[WellFormed_SP_def]>>
      drule_then assume_tac (iffLR HonestVerifierZeroKnowledge_SP_def)>>
      first_assum$ qspecl_then [‘s1’, ‘w’, ‘r’, ‘e3’, ‘t4’] mp_tac>>
      fs[])>-
      
   (fs[]>>
    qabbrev_tac‘e3 = SP_csub sp e p_2''’>>
    ‘e3 ∈ sp.Challenges.carrier’by metis_tac[SP_csub_Lemma]>>
    ‘p_2'' = SP_csub sp e e3’by metis_tac[SP_csub_Lemma2]>>
    qabbrev_tac‘t4 = sp.SimulatorMap p_1 w e3 p_1'’>>
    ‘ t4 ∈ sp.Responses’by metis_tac[WellFormed_SP_def]>>
    drule_then assume_tac (iffLR HonestVerifierZeroKnowledge_SP_def)>>
    first_assum$ qspecl_then [‘p_1’, ‘w’, ‘p_1'’, ‘e3’, ‘t4’] mp_tac>>
    fs[])>-
    
   (
   fs[]>>
   qabbrev_tac‘e3 = SP_csub sp e p_2'³'’>>
   ‘e3 ∈ sp.Challenges.carrier’by metis_tac[SP_csub_Lemma]>>
   ‘SP_csub sp e e3 = p_2'³'’by metis_tac[SP_csub_Lemma2]>>
   qabbrev_tac‘r = sp.SimulatorMapInverse p_1 w p_2'³' p_1''’>>
   ‘ r ∈  sp.RandomCoins’by metis_tac[WellFormed_SP_def]>>       
   drule_then assume_tac (iffLR HonestVerifierZeroKnowledge_SP_def)>>
   first_assum$ qspecl_then [‘p_1’, ‘w’, ‘r’, ‘p_2'³'’, ‘ p_1''’] mp_tac>>
   fs[]
   )>-

   (
   rpt (pairarg_tac>>
        gvs[])>>
   qabbrev_tac‘s1 = p_1’>> qabbrev_tac‘s2 = p_2’>>
   qabbrev_tac‘r = p_1' ’>>
                 
                 qabbrev_tac‘t3 = p_2' ’>>
      qabbrev_tac‘e3 = p_2'' ’>>              
      qabbrev_tac‘t4 = p_1'' ’>>
      qabbrev_tac‘e4 = p_2'³'’>>
      qabbrev_tac‘t5 = p_2'''' ’>>
   qabbrev_tac‘e5 = SP_csub sp e e1’>>
   qabbrev_tac‘e6 = SP_csub sp e e3’>>
   Cases_on ‘sp.Relation s1 w’ THENL [    
       ‘((sp.SimulatorMap s1 w e6 r,e6),t3) = ((t1,e1),t2) ∧  (sp.Prover_0 s1 w r,c2'') = (c1,c2)’by metis_tac[]>>
       ‘ t1 = sp.SimulatorMap s1 w e6 r ∧ e6 = e1 ∧ t3 = t2 ∧ sp.Prover_0 s1 w r = c1 ∧ c2'' = c2’by metis_tac[FST, SND, CROSS_DEF]>>                
       ‘e5 ∈ sp.Challenges.carrier ∧ e6 ∈ sp.Challenges.carrier’by metis_tac[SP_csub_Lemma, WellFormed_SP_def]>>
       ‘e5 = e3’ by metis_tac[SP_csub_Lemma2]>>
       ‘s1 = s1' ∧ t1 = t1' ∧ e1 = e1'’by metis_tac[WellFormed_SP_def]>>
       ‘s2 = s2' ∧ t2 = t2' ∧  e5 = e2'’by metis_tac[WellFormed_SP_def]>>
       ‘s2 = s2'' ∧ t3 = t2'' ∧ e3 = e2''’by metis_tac[WellFormed_SP_def]>>
       ‘s1 = s1'' ∧ t3 = t1'' ∧  e3 = e1''’by metis_tac[WellFormed_SP_def]>>
       fs[]>>
       gvs[]>>
          qabbrev_tac‘c = sp.Prover_0 p_1 w p_1'’>>
        ‘ c ∈ sp.Commitments’by metis_tac[WellFormed_SP_def]>>
       qabbrev_tac‘t = sp.Prover_1 p_1 w p_1' c e1’>>
       ‘t ∈ sp.Responses’by metis_tac[WellFormed_SP_def]>>   
       drule_then assume_tac (iffLR HonestVerifierZeroKnowledge_SP_def)>>
       first_assum$ qspecl_then [‘p_1’, ‘w’, ‘p_1'’, ‘e1’, ‘t’] mp_tac>>
       fs[]           
   )>-

    (
    ‘(c1'',sp.Prover_0 s2 w r) = (c1,c2)’by metis_tac[]>>
    ‘c1'' = c1 ∧ c2 = sp.Prover_0 s2 w r’by metis_tac[WellFormed_SP_def, FST, SND, CROSS_DEF]>>
    ‘((t3,e3),sp.SimulatorMap s2 w e6 r) = ((t1,e1),t2)’by metis_tac[]>>                     
    ‘t3 = t1 ∧ e3 = e1 ∧ t2 = sp.SimulatorMap s2 w e6 r’by metis_tac[FST, SND]>>
    qabbrev_tac‘t6 = sp.Prover_1 s2 w r c2 e6’>>
    ‘e6 ∈ sp.Challenges.carrier’ by metis_tac[SP_csub_Lemma]>>
    ‘ c2 ∈ sp.Commitments’by metis_tac[WellFormed_SP_def]>>
    ‘t6 ∈ sp.Responses’by metis_tac[WellFormed_SP_def]>>
    ‘e5 = e6’ by metis_tac[]>>
    ‘sp.Simulator s1 t1 e1  =  sp.Simulator s1 t3 e3’by metis_tac[]>>
    ‘(s1',c1',e1',t1') = (s1'',c1'',e1'',t1'')’by metis_tac[]>>
    ‘c1' = c1’by rw[]>>
    ‘s1'' = s1' ∧ s1 = s1' ∧ t1 = t1' ∧ t1' = t1'' ∧ e1 = e1' ∧ e1'' = e1'’by metis_tac[FST, SND, WellFormed_SP_def]>>
    ‘t2' ∈ sp.Responses’by metis_tac[WellFormed_SP_def]>>

    drule_then assume_tac (iffLR HonestVerifierZeroKnowledge_SP_def)>>
    ‘sp.Simulator s2 t2 e6 = (s2, c2, e6, t6)’by metis_tac[]>>
    ‘c2 = c2'’by metis_tac[FST, SND, WellFormed_SP_def]>>
    ‘t6 = t2' ’by metis_tac[FST, SND, WellFormed_SP_def]>>
    rw[]
    )>-
    (
    rpt (pairarg_tac>>
         gvs[])>>
    qabbrev_tac‘s1 = p_1’>> qabbrev_tac‘s2 = p_2’>>
    qabbrev_tac‘r = p_1' ’>> qabbrev_tac‘t3 = p_2' ’>>
    qabbrev_tac‘e1 = p_2'' ’>>              
    qabbrev_tac‘t4 = p_1'' ’>>
    qabbrev_tac‘e3 = p_2'³'’>>
    qabbrev_tac‘t5 = p_2'''' ’>>
    qabbrev_tac‘e4 = SP_csub sp e e1’>>
    qabbrev_tac‘e5 = SP_csub sp e e2’>>
    ‘e4 ∈ sp.Challenges.carrier’ by metis_tac[SP_csub_Lemma]>>
    Cases_on ‘sp.Relation s1 w’ THENL [
        ‘((sp.SimulatorMap s1 w e4 r,e4),t3) = ((t1,e2),t2)’by metis_tac[]>>
        ‘t1 = sp.SimulatorMap s1 w e4 r ∧ e2 = e4 ∧ t3 = t2’ by metis_tac[FST, SND]>>
        ‘e5 = e1’by metis_tac[SP_csub_Lemma2]>>
        ‘e2 ∈  sp.Challenges.carrier ∧ t1 ∈ sp.Responses’by metis_tac[WellFormed_SP_def]>>
        drule_then assume_tac (iffLR HonestVerifierZeroKnowledge_SP_def)>>
        ‘sp.SimulatorMapInverse s1 w e2 t1 = r’ by metis_tac[]>>
        fs[],
        
        ‘((t3,e1),sp.SimulatorMap s2 w e4 r) = ((t1,e2),t2)’by metis_tac[]>>
        metis_tac[FST, SND, HonestVerifierZeroKnowledge_SP_def]>>
      ] 
    )>-
    
    (
    rpt (pairarg_tac>>
         gvs[])>>
    Cases_on ‘sp.Relation p_1 w’ THENL [
        metis_tac[FST, SND, HonestVerifierZeroKnowledge_SP_def, SP_csub_Lemma, SP_csub_Lemma2, WellFormed_SP_def]
        ,
        qabbrev_tac‘s1 = p_1’>> qabbrev_tac‘s2 = p_2’>>
        qabbrev_tac‘r1 = p_1' ’>> qabbrev_tac‘t3 = p_2' ’>>
        qabbrev_tac‘e1 = p_2'' ’>>              
        qabbrev_tac‘t4 = p_1'' ’>>
        qabbrev_tac‘e3 = p_2'³'’>>
        qabbrev_tac‘t5 = p_2'''' ’>>
        qabbrev_tac‘e4 = SP_csub sp e e3’>>
        qabbrev_tac‘e5 = SP_csub sp e e2’>>
        ‘e4 ∈ sp.Challenges.carrier’ by metis_tac[SP_csub_Lemma]>>
        ‘((sp.SimulatorMapInverse s2 w e4 t5,t4),e3) = ((r,t),e2)’by metis_tac[]>>
        ‘r = sp.SimulatorMapInverse s2 w e4 t5 ∧ t = t4 ∧ e2 = e3’ by metis_tac[FST, SND]>>
        ‘e4 = e5’by metis_tac[]>>
        ‘e5 ∈  sp.Challenges.carrier ∧ t5 ∈ sp.Responses’by metis_tac[WellFormed_SP_def]>>
        ‘sp.SimulatorMap s2 w e5 r  = t5’by metis_tac[HonestVerifierZeroKnowledge_SP_def]>>
        rw[]
      ]
    )>-
    
QED

 
Theorem WellFormed_SP_eq_thm:
 WellFormed_SP sp  ⇒ WellFormed_SP (SP_eq sp)
Proof   
  rw[]>>
  simp[WellFormed_SP_def, SP_eq_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac >-
      
   metis_tac[WellFormed_SP_def,  SP_eq_def]>>
      metis_tac[WellFormed_SP_def,  SP_eq_def]>>
  metis_tac[WellFormed_SP_def,  SP_eq_def]>>
  metis_tac[WellFormed_SP_def,  SP_eq_def]>>
  metis_tac[WellFormed_SP_def,  SP_eq_def]>>
  metis_tac[WellFormed_SP_def,  SP_eq_def]>>
  metis_tac[WellFormed_SP_def,  SP_eq_def, FST, SND, CROSS_DEF]>>
      



        

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
                      Extractor:= (λ t1 t2 e1 e2. if e1 = e2 then 0 else ((t1 ⊖ t2) ⊘ (e1 ⊖ e2)));
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
   
   (  (* proving Group (Zadd q) *)
   ‘0 < q’ by metis_tac[NOT_PRIME_0, NOT_ZERO] >>
   ‘Group (Zadd q)’by metis_tac[Zadd_group]
   )>-
   
   (  (* proiving  r ⊕ e ⊗ w < q *)
   ‘Field (GF q)’by metis_tac[GF_field]>>
   ‘r ∈ (GF q).carrier ∧ e ∈ (GF q).carrier ∧ w ∈ (GF q).carrier’by metis_tac[GF_element]>>
   ‘r ⊕ e ⊗ w < q’by metis_tac[field_mult_element, field_add_element, GF_element]
   )>-
   
   (  (*proving  (t1 ⊕ (GF q).sum.inv t2) ⊗ Inv (GF q) (e1 ⊕ (GF q).sum.inv e2) < q *)
   ‘Field (GF q)’by metis_tac[GF_field]>>
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
   ‘x < q’ by metis_tac[GF_element]
   )>-

   (  (*proving  p_1 ** t * |/ (p_2 ** e) ∈ G*)
   ‘Group g’ by gs[cyclic_def] >>
   qabbrev_tac ‘p1 = g.exp p_1 t’ >>
   qabbrev_tac ‘p2 = g.exp p_2 e’ >>
   ‘p1 ∈ g.carrier ∧ p2 ∈ g.carrier’ by metis_tac[group_exp_element] >>
   ‘g.inv p2 ∈ g.carrier’ by metis_tac[group_inv_element] >>
   ‘(g.op p1 (g.inv p2)) ∈ g.carrier’ by metis_tac[group_op_element]
   )>-


   (  (* proving  r ⊕ e ⊗ w < q *)
   ‘Field (GF q)’by metis_tac[GF_field]>>
  ‘r ∈ (GF q).carrier ∧ e ∈ (GF q).carrier ∧ w ∈ (GF q).carrier’by metis_tac[GF_element]>>
   ‘r ⊕ e ⊗ w < q’by metis_tac[field_mult_element, field_add_element, GF_element]
   )>-


   (  (* proving  t ⊕ (GF q).sum.inv (e ⊗ w) < q  *)
   ‘Field (GF q)’by metis_tac[GF_field]>>
   ‘t ⊕ (GF q).sum.inv (e ⊗ w) < q’by metis_tac[field_mult_element, field_add_element, GF_element, field_neg_element, field_sub_element]
   )    
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
          (* use _ = .... *)
   ‘kmodq = ((n MOD q) * (x MOD q) MOD q) MOD q’ by metis_tac[MOD_TIMES2] >>
   ‘kmodq = ((n MOD q) * (x MOD q)) MOD q’ by metis_tac[MOD_MOD] >>
   ‘kmodq = (n * x)  MOD q’ by metis_tac[MOD_TIMES2] >>
   ‘LHS = g.exp g' ((n*x)MOD q)’ by rw[] >>
   ‘LHS = g.exp g' (n*x)’ by metis_tac[group_exp_mod] >>
   ‘RHS = g.exp (g.exp g' n) x’ by rw[] >>
   ‘RHS = g.exp g' (n * x)’ by metis_tac[GSYM group_exp_mult, Excl "monoid_exp_mult"] >>
   ‘LHS = RHS’ by rw[]
   )
QED
        
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
       ‘LHS1 = p_2’by rw[]                
    )
QED
        
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
   rw[group_rinv_assoc])
QED

  >-
           (
   ‘WellFormed_SP (Schnorr_SP g q)’ suffices_by rw[Schnorr_SP_def]>>
   ‘WellFormed_SP (Schnorr_SP g q)’by metis_tac[schnorr_wellformed_thm, Schnorr_SP_def, pairTheory.FORALL_PROD]
   )
QED

(*
  prime q ∧ cyclic g ∧ FINITE g.carrier ∧ (order g (cyclic_gen g) = q) ⇒ 
   WellFormed_SP (Schnorr_SP g q)

  ∀q. prime q ⇒ ∀g: 'a group. cyclic g ∧ FINITE G ∧ (ord (cyclic_gen g) = q)  ⇒ 
 HonestVerifierZeroKnowledge_SP (Schnorr_SP g q)
*)
        
(* error *)
Theorem schnorr_honest_verifier_zk_thm:
  ∀q. prime q ⇒ ∀g: 'a group. cyclic g ∧ FINITE G ∧ (ord (cyclic_gen g) = q) ∧ WellFormed_SP (Schnorr_SP g q)  ⇒ 
  HonestVerifierZeroKnowledge_SP (Schnorr_SP g q)
Proof
  rw[]>>
  qabbrev_tac‘q = (ord (cyclic_gen g))’ >>
  simp[Schnorr_SP_def, HonestVerifierZeroKnowledge_SP_def, pairTheory.FORALL_PROD] >>
                       
 (* ‘WellFormed_SP (Schnorr_SP g q)’by metis_tac[schnorr_wellformed_thm, Schnorr_SP_def]>> *)
                 
  rpt strip_tac >-
  
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
   ‘g.op a c = b’by rw[]
   )>-
(* one goal prooved *)

   (
   qabbrev_tac‘ew = (e ⊗ w)’ >>
 ‘Field (GF q)’ by rw[GF_field] >>
  ‘ew ∈ (GF q).carrier’ by metis_tac[GF_element, field_mult_element]>>
  ‘((GF q).sum.inv ew) ∈ (GF q).carrier’by metis_tac[field_neg_element]>>
  ‘ r ⊕ ew ⊕ (GF q).sum.inv ew =  r ⊕ (ew ⊕ (GF q).sum.inv ew)’by metis_tac[GF_element, field_add_assoc]>>
  ‘ew ⊕ (GF q).sum.inv ew = (GF q).sum.id’by metis_tac[field_add_rneg]>>
  ‘ r ⊕ _0_ = r’ by metis_tac[GF_element, field_add_rzero]>>
   ‘ r ⊕ ew ⊕ (GF q).sum.inv ew = r’ by rw[]
     )>-
  (* one goal prooved *) 

    
   (
   qabbrev_tac‘ew =  (e ⊗ w)’ >>
  ‘Field (GF q)’ by rw[GF_field] >>
  ‘ew ∈ (GF q).carrier’ by metis_tac[GF_element, field_mult_element]>>
  ‘((GF q).sum.inv ew) ∈ (GF q).carrier’by metis_tac[field_neg_element]>>

  ‘ t ⊕ (GF q).sum.inv ew ⊕ ew =  t ⊕ ( ((GF q).sum.inv ew) ⊕ ew )’by metis_tac[GF_element, field_add_assoc]>>
  ‘ ( ((GF q).sum.inv ew) ⊕ ew ) = (GF q).sum.id’by metis_tac[field_add_lneg]>>
  ‘ t ⊕ _0_ = t’ by metis_tac[GF_element, field_add_rzero]>>
   ‘t ⊕ (GF q).sum.inv ew ⊕ ew = t’ by rw[]
   )
QED
  >-
         (
   ‘WellFormed_SP (Schnorr_SP g q)’ suffices_by rw[Schnorr_SP_def]>>
   ‘WellFormed_SP (Schnorr_SP g q)’by metis_tac[schnorr_wellformed_thm, Schnorr_SP_def, pairTheory.FORALL_PROD]
   )
QED

Datatype:
  Commitment = <|A: num;
                 B: num;
               |>
End
     
   
Datatype:
Proof = <|Challenge: 'e group;
          Commitment: 'Commitment;
          Response: num;                   
         |>
End

        
Datatype:
  Choice = <|Alpha: num;
             Beta: num;
           |>
End
                       

Datatype:
  PyblicKey = <|g: num;
                 p: num;
                 q: num;
                 y: num;
               |>
End


Datatype:
  VoterAnswer = <|Choice: 'Choice;
                  Individual_proof: 'Proof × 'Proof;
                  Overal_proof: ('Proof × 'Proof) or Null;
                    |>
End

Datatype:
  TrusteeDecryption = <|Decryption_factor: num list;
                        Decryprtion_proof: 'Proof;
                        Pok: 'Proof;
                      |>
End                 
                   

Datatype:
  Question = <|Answer: 'VoterAnswer;
               Decryption: TrusteeDecryption;
               Public_key: 'PublicKey;
               Result: num;
             |>
End
             

Datatype:
  IACR2022Election = <|Question1: 'Question list; (* 6 items *)
                       Question2to5: 'Question list (* 4 items *)
                       Question6: 'Question list (* 2 items *)                       
                       |>
End
        
Datatype:
  IACR2022Election = <|Questions: Question list; (* 12 items*)|>
End
       

       
Definition Hash_def:
  Hach SHA2 = c Have in HOL, need to translate to cakeML
End

(*

Hardcode datatype to the specific Election             

Datatype: Result = 
        
Prove Election properties same as in Thomas paper:
          
*)

                                
Definition Voter_SP_or_def:
  Voter_SP_or gr q = SP_or (Voter_SP gr q) 
End

        
Definition Single_Vote_def:
  Single_Vote gr q = SP_or (SP_eq  (Schnorr_SP gr q))
End

Definition Single_Decryption_def:
  Single_Decryption gr q = SP_eq  (Schnorr_SP gr q)
End

        
TODO: Proove Theorem All the properties for both Protocols

Definition Election_verification_def:
  Election_verificaion E
End
        
          

Definition SP_eq_def:
  SP_eq S1  =  <|Statements:= (gr.carrier × gr.carrier) × (gr.carrier × gr.carrier);
                      Witnesses:= count q;
                      Relation:= (λ (s1, s2) w. S1.Relation s1 w ∧ S1.Relation s2 w);
                      RandomCoins:= S1.RandomCoins;
                      Commitments:= (S1.Commitments × S1.Commitments);
                      Challenges:= S1.Challenges;
                      Disjoint:= S1.Disjoint;
                      Responses:= S1.Responses;
                      Prover_0:= (λ (s1, s2) w r. (S1.Prover_0 s1 w r, S1.Prover_0 s2 w r));
                      Prover_1:= (λ (s1, s2) w r (c1, c2) e.
                                         (S1.Prover_1 s1 w r c1 e));
                      HonestVerifier:= (λ ((s1, s2), (c1, c2), e, t).
                                                S1.HonestVerifier (s1, c1, e, t) ∧ S1.HonestVerifier (s2, c2, e, t));
                      Extractor:= S1.Extractor;
                      Simulator:= (λ (s1, s2) t e. let (s1', c1', e1', t1') = S1.Simulator s1 t e;
                                                       (s2', c2', e2', t2') = S1.Simulator s2 t e
                                                   in
                                                     ((s1', s2'),(c1', c2'),e1', t1'));
                                                                                                                        
                      SimulatorMap:= (λ (s1, s2) w e r.
                                             (S1.SimulatorMap s1 w e r));
                      SimulatorMapInverse:=   (λ (s1, s2) w e t.
                                                      (S1.SimulatorMapInverse s1 w e t));
                     |> 
End



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
                      Extractor:= (λ t1 t2 e1 e2. if e1 = e2 then 0 else ((t1 ⊖ t2) ⊘ (e1 ⊖ e2)));
                      Simulator:= (λ (s1, s2) t e. ((s1, s2), gr.op (monoid_exp gr s1 t) (gr.inv (monoid_exp gr s2 e)), e ,t));
                      SimulatorMap:= (λ (s1, s2) w e r.  r ⊕ e ⊗ w);
                      SimulatorMapInverse:=  (λ (s1, s2) w e t.  t ⊖ e ⊗ w); 
                     |> 
End
        


            
(*

Q1. 6 candidates:
Voter can vote 1/0 for each of 6 candidates.
6 SP_or protocols with binary witness.
for each vote


Global setup
prime p, q
election private key x = ∑xi
election pyblic key  y = g^x
public_key = (y,g,p,q)

Trustee 
generate private key xi
compute public key yi = g^xi
Schnorr proof of xi

Next step
Commitment. Prover0 send (xi,yi)
where is Challenge, Prove1, Verifier?
receive cph = (Alpha, Beta)
Proof of equality. That I correctly apply private key. ELGAMAL.decryption. 
compute di = Alpha^xi
send di

Isnt it supposed to be non-interactive? 
     
Voter
Receives y = g^x
pick votes for candidates m ∈ {0,1}^n 
RandomCoins r, w
plaintext = g^m (where does SP disjunction come in?)
Choises:  Alpha = g^r; Beta = y^r * g^m
Ciphertext cph = (Alpha, Beta) 
A = g^w, B = y^w
Commitment c = (A,B)
Challenge e = Hash(cph, A,B)
Prover0:= λ _ _ _ . (A,B)
Response t = w + r * e
Prover1:= λ _ _ _ . (e,c,t,cph)
Verifier:= λ _ _ _ .
                     # commitment is not changed
                     g^t = c.A * cph.Alpha^e
                     g^(w+re) = (g^w) * (g^r)^e 

                     # vote is valid 0/1
                     # used disjunctive combiner
                     y^t = c.B * (cph.Beta/g^m)^e
                     y^t = c.B * (cph.Beta/g^0)^e or (y^t = c.B * (cph.Beta/g^1)^e)
                     
                      where does it get g^m from? Can we send plaintext?  ∧
                     g^(x*(w+re)) = y^w * ((y^r * g^m)/(g^m))^e
                     g^(x*(w+re)) = g^xw * (y^r)^e
                     g^(x*(w+re)) = g^xw * (g^xr)^e
                     g^(x*(w+re)) = g^(xw+xre)
                     g^(x*(w+re)) = g^(x*(w+xe))

                     # not checked, check each one is 0 or 1 , only for the last one need to check sum
                     ∏g^mi = g
                     g^∑mi = g^1
                     ∑mi = #

Helios Server
denote r = ∑ri
c1 = ∏Alphai = ∏g^ri = g^∑ri = g^r
c2 = ∏Betai = ∏(y^ri * g^mi) = ∏((g^x)^ri * g^mi) = g^(x∑ri) * g^∑mi =  g^xr * g^∑mi
Send (Alpha, Beta) = (c1,c2) to Trustees
Receive di from Trustees
d = ∏di = ∏c1^xi = c1^∑xi  = c1^x = g^rx
result = c2/d = g^xr * g^∑mi / g^xr = g^∑mi
Have to solve deiscrete log to obtain actiual result ∑mi    
*)
(* s1.Prover1 is not related to statemet, ignores c*)

   
Definition SP_eq_def:
  SP_eq S1  =  <|Statements:= S1.Statements × S1.Statements;
                      Witnesses:= S1.Witnesses;
                      Relation:= (λ (s1, s2) w. S1.Relation s1 w ∧ S1.Relation s2 w);
                      RandomCoins:= S1.RandomCoins;
                      Commitments:= (S1.Commitments × S1.Commitments);
                      Challenges:= S1.Challenges;
                      Disjoint:= S1.Disjoint;
                      Responses:= S1.Responses;
                      Prover_0:= (λ (s1, s2) w r. (S1.Prover_0 s1 w r, S1.Prover_0 s2 w r));
                      Prover_1:= (λ (s1, s2) w r (c1, c2) e.
                                         (S1.Prover_1 s1 w r c1 e));
                      HonestVerifier:= (λ ((s1, s2), (c1, c2), e, t).
                                                S1.HonestVerifier (s1, c1, e, t) ∧ S1.HonestVerifier (s2, c2, e, t));
                      Extractor:= S1.Extractor;
                      Simulator:= (λ (s1, s2) t e. let (s1', c1', e1', t1') = S1.Simulator s1 t e;
                                                       (s2', c2', e2', t2') = S1.Simulator s2 t e
                                                   in
                                                     ((s1', s2'),(c1', c2'),e1', t1'));
                                                                                                                        
                      SimulatorMap:= (λ (s1, s2) w e r.
                                             (S1.SimulatorMap s1 w e r));
                      SimulatorMapInverse:=   (λ (s1, s2) w e t.
                                                      (S1.SimulatorMapInverse s1 w e t));
                     |> 
End
               
type_of “Single_Vote”


                    
        
*)  
                
val _ = export_theory();

