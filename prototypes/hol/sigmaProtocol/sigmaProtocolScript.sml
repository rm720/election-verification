
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
val _ = new_theory "sigmaProtocol";

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
open computeBasicTheory;


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


    

Definition Gcross_def:
  Gcross g1 g2 = <| carrier:= g1.carrier × g2.carrier;
                    id:= (g1.id, g2.id);
                    op:= λ (a,b) (c,d). (g1.op a c, g2.op b d);
                 |>
End



        


Theorem Gcross_group_thm:
 AbelianGroup g1 ∧ AbelianGroup g2 ⇒ AbelianGroup (Gcross g1 g2)
Proof
  rw[]>>
  simp[AbelianGroup_def, group_def_alt, Group_def, Gcross_def, Gcross_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac >-
   (
   metis_tac[AbelianGroup_def, group_op_element]
   )>-
   (
   metis_tac[AbelianGroup_def, group_op_element]
   )>-   
   (
   metis_tac[AbelianGroup_def, group_assoc]
   )>-
   (
   metis_tac[AbelianGroup_def, group_assoc]
   )>-
   (
   metis_tac[AbelianGroup_def, group_id_element]
   )>-
   (
   metis_tac[AbelianGroup_def, group_id_element]
   )>-
   (
   metis_tac[AbelianGroup_def,  group_lid]
   )>-
   (
   metis_tac[AbelianGroup_def,  group_lid]
   )>-   
   (
   ‘(∀x1. x1 ∈ g1.carrier ⇒ ∃y1. y1 ∈ g1.carrier ∧ g1.op y1 x1 = g1.id) ∧ 
    (∀x2. x2 ∈ g2.carrier ⇒ ∃y2. y2 ∈ g2.carrier ∧ g2.op y2 x2 = g2.id)’by metis_tac[AbelianGroup_def, group_def_alt]>>   
   ‘(∃y1. y1 ∈ g1.carrier ∧  g1.op y1 p_1 = g1.id) ∧
    (∃y2. y2 ∈ g2.carrier ∧  g2.op y2 p_2 = g2.id)’by metis_tac[AbelianGroup_def, group_def_alt]>>
   qabbrev_tac‘y = (y1, y2)’>>
   ‘(λ(a,b) (c,d). (g1.op a c,g2.op b d)) (y1, y2) (p_1,p_2) = ((g1.op y1 p_1) , (g2.op y2 p_2))’by rw[]>>
   ‘((g1.op y1 p_1) , (g2.op y2 p_2)) = (g1.id,g2.id)’ by metis_tac[FST, SND, CROSS_DEF]>>              
   ‘FST y ∈ g1.carrier ∧ SND y ∈ g2.carrier’ by metis_tac[FST, SND, CROSS_DEF]>>
   metis_tac[]
   )>-
   (
   metis_tac[AbelianGroup_def]
   )>-
   (
   metis_tac[AbelianGroup_def]
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



Theorem sp_eq_dis_thm[simp]: (SP_eq sp).Disjoint = sp.Disjoint
Proof
  simp [SP_eq_def]
QED
        
                                                       
         
(*
Wellformines for
Only for EQ combiner
need That SImMap ignores statements, same for mimmapinverse
*)

Definition WellFormed_SP_def:
  WellFormed_SP sp ⇔
    (
    (AbelianGroup sp.Challenges) ∧ 
           
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
               )
End




        

Definition Or_WellFormed_SP_def:
  Or_WellFormed_SP sp ⇔
    (
    (AbelianGroup sp.Challenges) ∧ 
           
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
               sp.SimulatorMapInverse s w e t  ∈ sp.RandomCoins) ∧

    (∀e1 e2. e1 ∈ sp.Challenges.carrier ∧ e2 ∈ sp.Challenges.carrier ⇒
          (sp.Disjoint e1 e2 ⇔ e1 ≠ e2))
               )
End



(*define only additional*)

        
Definition Eq_WellFormed_SP_def:
  Eq_WellFormed_SP sp ⇔ 
    (
    
    WellFormed_SP sp ∧ 
    
    (∀s1 s2 w r c1 c2 e. s1 ∈ sp.Statements ∧
                         s2 ∈ sp.Statements ∧
                         w ∈ sp.Witnesses ∧
                         r ∈ sp.RandomCoins ∧
                         c1 ∈ sp.Commitments ∧
                         c2 ∈ sp.Commitments ∧
                         e ∈ sp.Challenges.carrier  ⇒
                         sp.Prover_1 s1 w r c1 e ∈ sp.Responses ∧
                         sp.Prover_1 s1 w r c1 e = sp.Prover_1 s2 w r c2 e) ∧        
    
    (∀s1 s2 w r e. s1 ∈ sp.Statements ∧
                   s2 ∈ sp.Statements ∧
                   w ∈ sp.Witnesses ∧
                   r ∈ sp.RandomCoins ∧
                   e ∈ sp.Challenges.carrier  ⇒
                   sp.SimulatorMap s1 w e r  ∈ sp.Responses ∧
                   sp.SimulatorMap s2 w e r  ∈ sp.Responses ∧
                   sp.SimulatorMap s1 w e r  =  sp.SimulatorMap s2 w e r ) ∧
               
    (∀s1 s2 w t e. s1 ∈ sp.Statements ∧
                   s2 ∈ sp.Statements ∧
                   w ∈ sp.Witnesses ∧
                   t ∈ sp.Responses ∧
                   e ∈ sp.Challenges.carrier  ⇒
                   sp.SimulatorMapInverse s1 w e t  ∈ sp.RandomCoins ∧
                   sp.SimulatorMapInverse s2 w e t  ∈ sp.RandomCoins ∧
                   sp.SimulatorMapInverse s1 w e t = sp.SimulatorMapInverse s2 w e t)
               )
End


        
(*this should be called "complete" *)
Definition Complete_SP_def:
  Complete_SP sp ⇔
    (∀s w r e. s ∈ sp.Statements ∧ w ∈ sp.Witnesses ∧ r ∈ sp.RandomCoins ∧ e ∈ sp.Challenges.carrier
                ∧ sp.Relation s w ⇒
                              let c =  sp.Prover_0 s w r in 
                                sp.HonestVerifier(s, c, e, sp.Prover_1 s w r c e))
                                        
End

(*
Definition Complete_SP_def:
  Complete_SP sp ⇔
    (∀s1 s2 w r e c1 c2.
      s1 ∈ sp.Statements ∧
      s2 ∈ sp.Statements ∧
      w ∈ sp.Witnesses ∧
      r ∈ sp.RandomCoins ∧
      e ∈ sp.Challenges.carrier ∧
      c2 ∈ sp.Commitments ∧
      sp.Relation s1 w ⇒
      let c1 =  sp.Prover_0 s1 w r;
          in 
        sp.HonestVerifier(s1, c1, e, (sp.Prover_1 s2 w r c2 e)))                                  
End  
*)
        


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
 ‘AbelianGroup (Gcross sp1.Challenges sp2.Challenges)’by metis_tac[Gcross_group_thm]
 )>>

 (

          rpt (pairarg_tac>>
               gvs[])>>
          fs[Gcross_def,FST, SND, CROSS_DEF]>>
          gs[WellFormed_SP_def, FST, SND, CROSS_DEF]>>
          metis_tac[FST, SND, CROSS_DEF]
  
 )
QED
 

Theorem Complete_SP_and_thm:
  Complete_SP sp1 ∧ Complete_SP sp2 ⇒ Complete_SP (SP_and sp1 sp2)
Proof
  simp[Complete_SP_def, SP_and_def, pairTheory.FORALL_PROD]>>
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

(*
  qabbrev_tac‘s1 = p_1’>> qabbrev_tac‘s2 = p_2’>>
  
        *)


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
  ‘Group Gr’by metis_tac[AbelianGroup_def, WellFormed_SP_def]>>
  ‘y1 ∈ Gr.carrier’ by metis_tac[group_inv_element]>>
  ‘Gr.op x y1 ∈ Gr.carrier’ by metis_tac[group_op_element]
QED



(*-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------*)

        
 
Theorem WellFormed_SP_or_thm:
 WellFormed_SP sp1  ⇒ WellFormed_SP (SP_or sp1)
Proof   
  rw[]>>
  simp[WellFormed_SP_def, SP_or_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac>-
   
   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[WellFormed_SP_def, FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]
                  
   )>-
        
   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[WellFormed_SP_def, FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]
            
   )>-
   
   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[WellFormed_SP_def, FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]
            
   )>-
   
   (
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
   
   (
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
                                    
   )>-
   
   (
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
                                    
   )>-
             
   (
   Cases_on ‘p_2 ≠ p_2'' ’ >| [       
       fs[]>>
       metis_tac[WellFormed_SP_def, SP_or_def]
       ,
       fs[]>>
       metis_tac[WellFormed_SP_def, SP_or_def, SP_csub_Lemma]
     ]
                              
   )>-
   
   (
   rpt (pairarg_tac>>
        gvs[])
        
   )>-
   
   (              
   rpt (pairarg_tac>>
        gvs[])
        
   )>-
   
   (
   rpt (pairarg_tac>>
        gvs[])
   
   )>-
   
   (
   rpt (pairarg_tac>>
        gvs[])>>
   metis_tac[WellFormed_SP_def]
   )>-
   
   (
   rpt (pairarg_tac>>
        gvs[])
   
   )>-
   
   (
   rpt (pairarg_tac>>
        gvs[])>>
   metis_tac[WellFormed_SP_def, SP_or_def, SP_csub_Lemma]
            
   )>-
   
   (
   rpt (pairarg_tac>>
        gvs[])>>                  
   metis_tac[WellFormed_SP_def]
            
   )>-
   
   (
   rpt (pairarg_tac>>
        gvs[])>>
   metis_tac[WellFormed_SP_def, SP_or_def, SP_csub_Lemma]
            
   )>-
   
   (
   Cases_on ‘sp1.Relation p_1 w’ >| [
       fs[]>>
       qabbrev_tac‘e1 = SP_csub sp1 e p_2''’>>
       ‘e1 ∈ sp1.Challenges.carrier’by metis_tac[SP_csub_Lemma]>>
       ‘e1 ∈ sp1.Challenges.carrier’by metis_tac[SP_csub_Lemma, WellFormed_SP_def]>>
       metis_tac[WellFormed_SP_def, SP_or_def, SP_csub_Lemma]
       ,
       fs[]]
                                    
   ) >-
   
   (
   fs[]>>
   Cases_on ‘sp1.Relation p_1 w’ >| [
       fs[]>>
       metis_tac[SP_csub_Lemma]
       ,
       fs[]
     ]
   )>-
   
   (
   Cases_on ‘sp1.Relation p_1 w’ >| [
       fs[]
       ,
       fs[]>>
       metis_tac[WellFormed_SP_def, SP_or_def, SP_csub_Lemma]    
     ]
                                    
   )>-
   
   (
   fs[]>>  
   Cases_on ‘sp1.Relation p_1 w’ >|[
       fs[]>>
       metis_tac[WellFormed_SP_def, SP_or_def]
       ,
       fs[]>>
       metis_tac[WellFormed_SP_def, SP_or_def, SP_csub_Lemma]
     ]
   )>-
   
   (
   Cases_on ‘sp1.Relation p_1 w’ >|[
       fs[]>>
       metis_tac[WellFormed_SP_def, SP_or_def]
       ,
       fs[]>>
       metis_tac[WellFormed_SP_def, SP_or_def, SP_csub_Lemma]
     ]
   )>-
   
   (
   Cases_on ‘sp1.Relation p_1 w’ >|[
       fs[]>>
       metis_tac[WellFormed_SP_def, SP_or_def, SP_csub_Lemma]
       ,
       fs[]
     ]
   )
   
   
QED




(*-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------*)









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
        
(* e1 - (e1-e2) = e1-e1+e2 = e2 *)
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
  ‘AbelianGroup Gr’by metis_tac[WellFormed_SP_def]>>
  ‘Group Gr’by metis_tac[AbelianGroup_def]>>      
  ‘Gr.inv y ∈ Gr.carrier’by metis_tac[group_inv_element]>>
  ‘Gr.op x (Gr.inv y) ∈ Gr.carrier’ by metis_tac[group_op_element]>>
  qabbrev_tac‘z = Gr.inv (Gr.op x (Gr.inv y))’>>
  qabbrev_tac‘s = Gr.inv y’>>
  ‘Gr.inv s = y’by metis_tac[group_inv_inv]>>
  ‘Gr.op x s = Gr.op s x’by metis_tac[AbelianGroup_def]>>
  ‘z = Gr.inv (Gr.op s x)’by metis_tac[]>>
  ‘Gr.op Gr.id y = y’by metis_tac[group_lid]>>
  ‘Gr.op x (Gr.inv x) = Gr.id’ by metis_tac[group_rinv]>>
  ‘Gr.op (Gr.op x (Gr.inv x))  y = y’by metis_tac[]>>
  ‘Gr.inv x ∈ Gr.carrier’ by metis_tac[group_inv_element]>>
  ‘Gr.op x (Gr.op (Gr.inv x) y) = y’by metis_tac[group_linv_assoc]>>
  ‘Gr.op x (Gr.op (Gr.inv x) (Gr.inv s)) = y’by metis_tac[]>>
  ‘Gr.inv (Gr.op s x) = Gr.op (Gr.inv x) (Gr.inv s)’by metis_tac[group_inv_op]>>
  ‘Gr.op x (Gr.inv (Gr.op s x)) = y’by metis_tac[]>>
  ‘Gr.op x z = y’by metis_tac[Abbr‘z’]
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
  rw[]>>
  simp[WellFormed_SP_def, SP_csub_def, SP_or_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac >>
  qabbrev_tac‘Gr = sp.Challenges’>>
  ‘AbelianGroup Gr’by metis_tac[WellFormed_SP_def]>>
  ‘Group Gr’by metis_tac[AbelianGroup_def]>>
  ‘e1 = Gr.op (Gr.op e2 (Gr.inv e3)) (Gr.inv (Gr.inv e3))’by metis_tac[group_lsolve, group_op_element, group_inv_element]>>
  ‘e1 = Gr.op (Gr.op e2 (Gr.inv e3)) e3’by metis_tac[group_inv_inv]>>
  ‘e1 = Gr.op e2 (Gr.op (Gr.inv e3) e3)’by metis_tac[group_assoc, group_op_element, group_inv_element]>>
  ‘e1 = Gr.op e2 Gr.id’by metis_tac[group_linv, group_op_element, group_inv_element]>>
  ‘e1 = e2 ’by metis_tac[ group_rid, group_op_element, group_inv_element]
QED
        

Theorem Complete_SP_or_thm:
  Complete_SP sp1 ∧ SimulatorCorrectness_SP sp1 ∧ WellFormed_SP sp1 ⇒ Complete_SP (SP_or sp1)
Proof
  rw[]>>
  simp[Complete_SP_def, SP_or_def, pairTheory.FORALL_PROD]>>
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
         drule_then assume_tac (cj 1 (iffLR Complete_SP_def))>>         
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
       ‘sp1.HonestVerifier (s1,c1,e2,t1)’by metis_tac[Complete_SP_def]>>

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
       ‘sp1.HonestVerifier (s2,c2,e3,t2)’by metis_tac[Complete_SP_def]>>
       gs[]  
     ]
   )
QED

(*
Theorem  SpecialSoundness_SP_or_thm:
  ∀sp. WellFormed_SP sp1 ∧
       SpecialSoundness_SP sp1 ∧
       (sp1.Disjoint a b ⇔ a ≠ b)
       ⇒ SpecialSoundness_SP (SP_or sp1)
Proof
    rw[]>>
    simp[SpecialSoundness_SP_def, SP_or_def, pairTheory.FORALL_PROD] >>
    rpt strip_tac >>

    qabbrev_tac‘s1 = p_1’>> qabbrev_tac‘s2 = p_2’>>
    qabbrev_tac‘c1 = p_1' ’>> qabbrev_tac‘c2 = p_2' ’>>            
    qabbrev_tac‘t1 = p_1'' ’>> qabbrev_tac‘t2 = p_2'³'’>>

    qabbrev_tac‘t3 = p_1'³'’>>  qabbrev_tac‘t4 = p_2'⁵'’>>
    qabbrev_tac‘e3 = p_2'' ’>>  qabbrev_tac‘e4 = p_2'''' ’>>
                   
    qabbrev_tac‘e5 = SP_csub sp1 e1 e3 ’>> qabbrev_tac‘e6 = SP_csub sp1 e2 e4 ’>>

        
    Cases_on ‘e3 ≠ e4’ THENL [
    qabbrev_tac‘w =  (if e3 ≠ e4 then sp1.Extractor t1 t3 e3 e4
                      else sp1.Extractor t2 t4 e5 e6)’>>
    ‘w = sp1.Extractor t1 t3 e3 e4’ by metis_tac[]>>
    ‘ sp1.Disjoint e3 e4 ⇔ e3 ≠ e4’by metis_tac[]>>
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
*)
        
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
(* 3 goals left*)
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
     ,

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
     ]
                                        
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
        fs[]
                ,
        
        ‘((t3,e1),sp.SimulatorMap s2 w e4 r) = ((t1,e2),t2)’by metis_tac[]>>
        metis_tac[FST, SND, HonestVerifierZeroKnowledge_SP_def]
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
    )
    
QED

 
Theorem WellFormed_SP_eq_thm:
 WellFormed_SP sp  ⇒ WellFormed_SP (SP_eq sp)
Proof   
  rw[]>>
  simp[WellFormed_SP_def, SP_eq_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac >-

   (
   metis_tac[WellFormed_SP_def,  SP_eq_def]
   )>-
        
   (
   metis_tac[WellFormed_SP_def,  SP_eq_def]
   )>-

   (
   metis_tac[WellFormed_SP_def,  SP_eq_def]
   )>-

   (
   metis_tac[WellFormed_SP_def,  SP_eq_def]
   )>-

   (
   metis_tac[WellFormed_SP_def,  SP_eq_def]
   )>-

   (
   metis_tac[WellFormed_SP_def,  SP_eq_def]
   )>-

   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[WellFormed_SP_def, FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]
            
   )>-

   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[WellFormed_SP_def, FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]
            
   )>-
        
   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[WellFormed_SP_def, FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]
            
   )>-

   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[WellFormed_SP_def, FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]
            
   )>-

   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[WellFormed_SP_def, FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]
            
   )>-


   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[WellFormed_SP_def, FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]
            
   )>-


   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[WellFormed_SP_def, FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]
            
   )>-


   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[WellFormed_SP_def, FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]
            
   )

QED     


        (*
Theorem Eq_WellFormed_SP_eq_thm:
 Eq_WellFormed_SP sp  ⇒ Eq_WellFormed_SP (SP_eq sp)
Proof   
  rw[]>>
  simp[Eq_WellFormed_SP_def, SP_eq_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac >>

   rpt(
   metis_tac[Eq_WellFormed_SP_def,  SP_eq_def]
     )>>

   rpt(
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[Eq_WellFormed_SP_def, FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]      
     )
QED
  *)   


 
Theorem Eq_WellFormed_SP_eq_thm:
 Eq_WellFormed_SP sp  ⇒ Eq_WellFormed_SP (SP_eq sp)
Proof   
  rw[]>>
  simp[Eq_WellFormed_SP_def,WellFormed_SP_def,  SP_eq_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac >-

            
   (
   metis_tac[Eq_WellFormed_SP_def,  WellFormed_SP_def, SP_eq_def]
   )>-

   (
   metis_tac[Eq_WellFormed_SP_def,  WellFormed_SP_def, SP_eq_def]
   )>-

   (
   metis_tac[Eq_WellFormed_SP_def,  WellFormed_SP_def, SP_eq_def]
   )>-

   (
   metis_tac[Eq_WellFormed_SP_def,  WellFormed_SP_def, SP_eq_def]
   )>-

   (
   metis_tac[Eq_WellFormed_SP_def,  WellFormed_SP_def, SP_eq_def]
   )>-

   (
   metis_tac[Eq_WellFormed_SP_def,  WellFormed_SP_def, SP_eq_def]
   )>-
    
   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[Eq_WellFormed_SP_def,WellFormed_SP_def,  FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]      
   )>-

   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[Eq_WellFormed_SP_def, WellFormed_SP_def, FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]      
   )>-

   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[Eq_WellFormed_SP_def, WellFormed_SP_def, FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]      
   )>-

   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[Eq_WellFormed_SP_def, WellFormed_SP_def, FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]      
   )>-

   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[Eq_WellFormed_SP_def, WellFormed_SP_def, FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]      
   )>-

   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[Eq_WellFormed_SP_def,WellFormed_SP_def,  FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]      
   )>-

   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[Eq_WellFormed_SP_def, WellFormed_SP_def, FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]      
   )>-

   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[Eq_WellFormed_SP_def, WellFormed_SP_def, FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]      
   )>-

   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[Eq_WellFormed_SP_def, WellFormed_SP_def, FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]      
   )>-

   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[Eq_WellFormed_SP_def, WellFormed_SP_def, FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]      
   )>-

   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[Eq_WellFormed_SP_def, WellFormed_SP_def, FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]      
   )>-

   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[Eq_WellFormed_SP_def, WellFormed_SP_def, FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]      
   )>-

   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[Eq_WellFormed_SP_def, WellFormed_SP_def, FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]      
   )>-

   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[Eq_WellFormed_SP_def, WellFormed_SP_def, FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]      
   )>-

   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[Eq_WellFormed_SP_def, WellFormed_SP_def, FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]      
   )>-

   (
   rpt (pairarg_tac>>
        gvs[])>>
   fs[Gcross_def,FST, SND, CROSS_DEF]>>
   gs[Eq_WellFormed_SP_def, WellFormed_SP_def, FST, SND, CROSS_DEF]>>
   metis_tac[FST, SND, CROSS_DEF]      
   )
QED     


      

Theorem SimulatorCorrectness_SP_eq_thm:
  SimulatorCorrectness_SP sp ∧ Eq_WellFormed_SP sp ⇒ SimulatorCorrectness_SP (SP_eq sp)
Proof
  rw[]>>
  simp[SimulatorCorrectness_SP_def, SP_eq_def, Eq_WellFormed_SP_def, WellFormed_SP_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac >>
  rpt (pairarg_tac>>
       gvs[])>>
  metis_tac[SimulatorCorrectness_SP_def, SP_eq_def, Eq_WellFormed_SP_def, WellFormed_SP_def]
QED
     
 
Theorem Complete_SP_eq_thm:
  Complete_SP sp ∧ Eq_WellFormed_SP sp ⇒ Complete_SP (SP_eq sp)
Proof
  rw[]>>
  simp[Complete_SP_def, SP_eq_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac >-

   (
   metis_tac[Complete_SP_def, SP_eq_def, SimulatorCorrectness_SP_def, Eq_WellFormed_SP_def, WellFormed_SP_def]
   )>-

   (
   ‘WellFormed_SP sp’by metis_tac[Eq_WellFormed_SP_def]>>
   drule_then assume_tac (cj 2 (iffLR Eq_WellFormed_SP_def))>>
   ‘∀s1 s2 w r c1 c2 e.
     s1 ∈ sp.Statements ∧ s2 ∈ sp.Statements ∧ w ∈ sp.Witnesses ∧
     r ∈ sp.RandomCoins ∧ c1 ∈ sp.Commitments ∧ c2 ∈ sp.Commitments ∧
     e ∈ sp.Challenges.carrier ⇒
     sp.Prover_1 s1 w r c1 e = sp.Prover_1 s2 w r c2 e’by  metis_tac[]>>
   qabbrev_tac‘c1 = sp.Prover_0 p_1 w r’>>
   qabbrev_tac‘c2 = sp.Prover_0 p_2 w r’>>
   ‘c1 ∈ sp.Commitments ∧ c2 ∈ sp.Commitments’by metis_tac[Eq_WellFormed_SP_def, WellFormed_SP_def]>>
   qabbrev_tac‘t1 = ‘Prover_1 p_1 w r c1 e’>>
   qabbrev_tac‘t2 = ‘Prover_1 p_2 w r c2 e’>>
  ‘sp.Prover_1 p_1 w r c1 e = sp.Prover_1 p_2 w r c2 e’by metis_tac[Eq_WellFormed_SP_def, WellFormed_SP_def]>>
  metis_tac[Complete_SP_def]
 )    
QED
        


Theorem  SpecialSoundness_SP_eq_thm:
  SpecialSoundness_SP sp ∧ Eq_WellFormed_SP sp ⇒ SpecialSoundness_SP (SP_eq sp)
Proof
  simp[SpecialSoundness_SP_def, SP_eq_def,  pairTheory.FORALL_PROD] >>
  rpt strip_tac >-
      
   (
   metis_tac[SpecialSoundness_SP_def, SP_eq_def, Eq_WellFormed_SP_def]
   )>-

   (
   metis_tac[SpecialSoundness_SP_def, SP_eq_def, Eq_WellFormed_SP_def]
   )
QED



Theorem HonestVerifierZeroKnowledge_SP_eq_thm:
 HonestVerifierZeroKnowledge_SP sp ∧ Eq_WellFormed_SP sp ∧ Complete_SP sp  ⇒ HonestVerifierZeroKnowledge_SP (SP_eq sp)
Proof
  rw[]>>
  simp[HonestVerifierZeroKnowledge_SP_def, SP_eq_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac >>
   rpt (pairarg_tac>>
           gvs[])>>
  rw[]>-

   (
   metis_tac[FST, SND, CROSS_DEF,Eq_WellFormed_SP_def,HonestVerifierZeroKnowledge_SP_def]
   )>-
   (
   metis_tac[FST, SND, CROSS_DEF,Eq_WellFormed_SP_def,HonestVerifierZeroKnowledge_SP_def]
   )>-
   (
   metis_tac[FST, SND, CROSS_DEF,Eq_WellFormed_SP_def,HonestVerifierZeroKnowledge_SP_def]
   )>-
   (
   metis_tac[FST, SND, CROSS_DEF,Eq_WellFormed_SP_def,HonestVerifierZeroKnowledge_SP_def]
   )>-
   (
   metis_tac[FST, SND, CROSS_DEF,Eq_WellFormed_SP_def,HonestVerifierZeroKnowledge_SP_def]
   )>-
   (
   metis_tac[FST, SND, CROSS_DEF,Eq_WellFormed_SP_def,HonestVerifierZeroKnowledge_SP_def]
   )>-
   (
   metis_tac[FST, SND, CROSS_DEF,Eq_WellFormed_SP_def,HonestVerifierZeroKnowledge_SP_def]
   )>-
   (
   metis_tac[FST, SND, CROSS_DEF,Eq_WellFormed_SP_def,HonestVerifierZeroKnowledge_SP_def]
   )
QED
        
     

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


Theorem schnorr_disjoint[simp]: (Schnorr_SP gr q).Disjoint = λ a b. a ≠ b
Proof
  simp [Schnorr_SP_def]
QED
        
(*comment*)

Theorem schnorr_wellformed_thm: 
  prime q ∧ cyclic g ∧ FINITE g.carrier ∧ (order g (cyclic_gen g) = q) ⇒ 
   WellFormed_SP (Schnorr_SP g q)
Proof
  simp[Schnorr_SP_def, WellFormed_SP_def,  pairTheory.FORALL_PROD] >>
  rpt strip_tac >-
                       
                        
   (  (* proving AbelianGroup (Zadd q) *)
   ‘0 < q’ by metis_tac[NOT_PRIME_0, NOT_ZERO] >>
   ‘Group (Zadd q)’by metis_tac[Zadd_group]>>
   ‘FiniteAbelianGroup (Zadd q)’by metis_tac[Zadd_finite_abelian_group]>>
    ‘AbelianGroup (Zadd q)’by metis_tac[FiniteAbelianGroup_def]
   )>-
   
   (  (* proiving  r ⊕ e ⊗ w < q *)
   ‘Field (GF q)’by metis_tac[GF_field]>>
   ‘r ∈ (GF q).carrier ∧ e ∈ (GF q).carrier ∧ w ∈ (GF q).carrier’by metis_tac[GF_element]>>
   ‘r ⊕ e ⊗ w < q’by metis_tac[field_mult_element, field_add_element, GF_element]
   )>-

   (
   Cases_on ‘e1 = e2’ THENL [
       rw[]
       ,
    (*proving  (t1 ⊕ (GF q).sum.inv t2) ⊗ Inv (GF q) (e1 ⊕ (GF q).sum.inv e2) < q *)
   ‘Field (GF q)’by metis_tac[GF_field]>>
   ‘t1 ∈ (GF q).carrier ∧ t2 ∈ (GF q).carrier ∧ e1 ∈ (GF q).carrier ∧ e2 ∈ (GF q).carrier’by metis_tac[GF_element]>>  
   qabbrev_tac‘dt = (t1 ⊕ (GF q).sum.inv t2)’>>
   qabbrev_tac‘de = (e1 ⊕ (GF q).sum.inv e2)’>>
   qabbrev_tac‘x =  dt ⊗ Inv (GF q) de’>>
   ‘de = (e1 ⊖ e2)’ by rw[] >>
   ‘de ≠ _0_’  by metis_tac[GF_sub_not_eq_zero]>>
   ‘dt = (t1 ⊖ t2)’ by rw[] >>
   ‘de ∈ (GF q).carrier ∧ dt ∈ (GF q).carrier’ by metis_tac[field_neg_element, field_sub_element] >>
   ‘de ∈ ring_nonzero (GF q)’ by metis_tac[field_nonzero_eq]>>
   ‘(Inv (GF q) de) ∈ (GF q).carrier’by metis_tac[field_inv_element]>>
   ‘(dt ⊗ Inv (GF q) de) ∈ (GF q).carrier’by metis_tac[field_mult_element]>>
   ‘x ∈ (GF q).carrier’by rw[Abbr‘x’]>>
   ‘x < q’ by metis_tac[GF_element]>>
   metis_tac[]
                ]
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






 

Theorem schnorr_eq_wellformed_thm: 
  prime q ∧ cyclic g ∧ FINITE g.carrier ∧ (order g (cyclic_gen g) = q) ⇒ 
   Eq_WellFormed_SP (Schnorr_SP g q)
Proof
  simp[Schnorr_SP_def, WellFormed_SP_def, Eq_WellFormed_SP_def,  pairTheory.FORALL_PROD] >>
  rpt strip_tac >-
                       
                        
   (  (* proving AbelianGroup (Zadd q) *)
   ‘0 < q’ by metis_tac[NOT_PRIME_0, NOT_ZERO] >>
   ‘Group (Zadd q)’by metis_tac[Zadd_group]>>
   ‘FiniteAbelianGroup (Zadd q)’by metis_tac[Zadd_finite_abelian_group]>>
    ‘AbelianGroup (Zadd q)’by metis_tac[FiniteAbelianGroup_def]
   )>-
   
   (  (* proiving  r ⊕ e ⊗ w < q *)
   ‘Field (GF q)’by metis_tac[GF_field]>>
   ‘r ∈ (GF q).carrier ∧ e ∈ (GF q).carrier ∧ w ∈ (GF q).carrier’by metis_tac[GF_element]>>
   ‘r ⊕ e ⊗ w < q’by metis_tac[field_mult_element, field_add_element, GF_element]
   )>-

   (
   Cases_on ‘e1 = e2’ THENL [
       rw[]
       ,
    (*proving  (t1 ⊕ (GF q).sum.inv t2) ⊗ Inv (GF q) (e1 ⊕ (GF q).sum.inv e2) < q *)
   ‘Field (GF q)’by metis_tac[GF_field]>>
   ‘t1 ∈ (GF q).carrier ∧ t2 ∈ (GF q).carrier ∧ e1 ∈ (GF q).carrier ∧ e2 ∈ (GF q).carrier’by metis_tac[GF_element]>>  
   qabbrev_tac‘dt = (t1 ⊕ (GF q).sum.inv t2)’>>
   qabbrev_tac‘de = (e1 ⊕ (GF q).sum.inv e2)’>>
   qabbrev_tac‘x =  dt ⊗ Inv (GF q) de’>>
   ‘de = (e1 ⊖ e2)’ by rw[] >>
   ‘de ≠ _0_’  by metis_tac[GF_sub_not_eq_zero]>>
   ‘dt = (t1 ⊖ t2)’ by rw[] >>
   ‘de ∈ (GF q).carrier ∧ dt ∈ (GF q).carrier’ by metis_tac[field_neg_element, field_sub_element] >>
   ‘de ∈ ring_nonzero (GF q)’ by metis_tac[field_nonzero_eq]>>
   ‘(Inv (GF q) de) ∈ (GF q).carrier’by metis_tac[field_inv_element]>>
   ‘(dt ⊗ Inv (GF q) de) ∈ (GF q).carrier’by metis_tac[field_mult_element]>>
   ‘x ∈ (GF q).carrier’by rw[Abbr‘x’]>>
   ‘x < q’ by metis_tac[GF_element]>>
   metis_tac[]
                ]
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
   )>-
   (  (* proiving  r ⊕ e ⊗ w < q *)
   ‘Field (GF q)’by metis_tac[GF_field]>>
   ‘r ∈ (GF q).carrier ∧ e ∈ (GF q).carrier ∧ w ∈ (GF q).carrier’by metis_tac[GF_element]>>
   ‘r ⊕ e ⊗ w < q’by metis_tac[field_mult_element, field_add_element, GF_element]
   )>-

   (  (* proiving  r ⊕ e ⊗ w < q *)
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
Theorem schnorr_Completeness_thm: 
  prime q ∧ cyclic g ∧ FINITE g.carrier ∧ (order g (cyclic_gen g) = q) ⇒ 
  Complete_SP (Schnorr_SP g q)
Proof
  simp[Schnorr_SP_def, Complete_SP_def, pairTheory.FORALL_PROD] >>
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
        

        
Theorem schnorr_simulator_Completeness_thm:
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



(*
  prime q ∧ cyclic g ∧ FINITE g.carrier ∧ (order g (cyclic_gen g) = q) ⇒ 
   WellFormed_SP (Schnorr_SP g q)

  ∀q. prime q ⇒ ∀g: 'a group. cyclic g ∧ FINITE G ∧ (ord (cyclic_gen g) = q)  ⇒ 
 HonestVerifierZeroKnowledge_SP (Schnorr_SP g q)
*)
        

Theorem schnorr_honest_verifier_zk_thm:
  ∀q. prime q ⇒ ∀g: 'a group. cyclic g ∧ FINITE G ∧ (ord (cyclic_gen g) = q)  ⇒ 
  HonestVerifierZeroKnowledge_SP (Schnorr_SP g q)
Proof
  rw[]>>
  qabbrev_tac‘q = (ord (cyclic_gen g))’ >>
  simp[Schnorr_SP_def, HonestVerifierZeroKnowledge_SP_def, pairTheory.FORALL_PROD] >>
  ‘Eq_WellFormed_SP (Schnorr_SP g q)’by metis_tac[schnorr_eq_wellformed_thm]>>
                       
 (* ‘WellFormed_SP (Schnorr_SP g q)’by metis_tac[schnorr_wellformed_thm, Schnorr_SP_def]>> *)
                 
    rpt strip_tac >-
        
  (* prooving p_1 ** (r ⊕ e ⊗ w) * |/ ((p_1 ** w) ** e) = p_1 ** r*)
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


     (*    r ⊕ e ⊗ w ⊕ (GF q).sum.inv (e ⊗ w) = r *)
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


     (*   t ⊕ (GF q).sum.inv (e ⊗ w) ⊕ e ⊗ w = t *)
    
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



Theorem eq_schnorr_eq_wellformed_thm: 
  prime q ∧ cyclic g ∧ FINITE g.carrier ∧ (order g (cyclic_gen g) = q) ⇒ 
  Eq_WellFormed_SP (SP_eq(Schnorr_SP g q))
Proof
  simp[pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
  ‘Eq_WellFormed_SP (Schnorr_SP g q)’ by metis_tac[schnorr_eq_wellformed_thm]>>
  metis_tac[Eq_WellFormed_SP_eq_thm]
QED


Theorem eq_schnorr_Completeness_thm: 
  prime q ∧ cyclic g ∧ FINITE g.carrier ∧ (order g (cyclic_gen g) = q) ⇒ 
  Complete_SP (SP_eq(Schnorr_SP g q))
Proof
  simp[pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
  ‘Complete_SP (Schnorr_SP g q)’ by metis_tac[schnorr_Completeness_thm]>>
  ‘Eq_WellFormed_SP (Schnorr_SP g q)’by metis_tac[schnorr_eq_wellformed_thm]>>
  metis_tac[Complete_SP_eq_thm]
QED
        

Theorem eq_schnorr_simulator_Completeness_thm: 
  prime q ∧ cyclic g ∧ FINITE g.carrier ∧ (order g (cyclic_gen g) = q) ⇒ 
  SimulatorCorrectness_SP (SP_eq(Schnorr_SP g q))
Proof
  simp[pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
  ‘SimulatorCorrectness_SP (Schnorr_SP g q)’ by metis_tac[schnorr_simulator_Completeness_thm]>>
  ‘Eq_WellFormed_SP (Schnorr_SP g q)’by metis_tac[schnorr_eq_wellformed_thm]>>
  metis_tac[SimulatorCorrectness_SP_eq_thm]
QED


Theorem eq_schnorr_special_soundness_thm: 
  prime q ∧ cyclic g ∧ FINITE g.carrier ∧ (order g (cyclic_gen g) = q) ⇒ 
  SpecialSoundness_SP (SP_eq(Schnorr_SP g q))
Proof
   simp[pairTheory.FORALL_PROD] >>
   rpt strip_tac >>
   ‘Eq_WellFormed_SP (Schnorr_SP g q)’by metis_tac[schnorr_eq_wellformed_thm]>>
   ‘SpecialSoundness_SP (Schnorr_SP g q)’ by metis_tac[schnorr_special_soundness_thm]>>
   metis_tac[SpecialSoundness_SP_eq_thm]
QED
        
        
Theorem eq_schnorr_honest_verifier_zk_thm:
  ∀q. prime q ⇒ ∀g: 'a group. cyclic g ∧ FINITE G ∧ (ord (cyclic_gen g) = q)  ⇒ 
  HonestVerifierZeroKnowledge_SP (SP_eq(Schnorr_SP g q))
Proof
  rw[]>>
  qabbrev_tac‘q = (ord (cyclic_gen g))’ >>
  simp[pairTheory.FORALL_PROD] >>
  ‘Eq_WellFormed_SP (Schnorr_SP g q)’by metis_tac[schnorr_eq_wellformed_thm]>>
  ‘Complete_SP (Schnorr_SP g q)’ by metis_tac[schnorr_Completeness_thm]>>
  ‘HonestVerifierZeroKnowledge_SP (Schnorr_SP g q)’by metis_tac[schnorr_honest_verifier_zk_thm]>>
  metis_tac[HonestVerifierZeroKnowledge_SP_eq_thm]
QED


(*----------------------------------------------
 DisjunctionSP(EqualitySP(SchnorrSP(p,q))) *)

Theorem eq_schnorr_wellformed_sp_thm:
  prime q ∧ cyclic g ∧ FINITE g.carrier ∧ (order g (cyclic_gen g) = q) ⇒ 
  WellFormed_SP (SP_eq(Schnorr_SP g q))
Proof
  rw[]>>
  qabbrev_tac‘q = (ord (cyclic_gen g))’ >>
  simp[WellFormed_SP_def, SP_eq_def, Schnorr_SP_def, pairTheory.FORALL_PROD] >>         
  rpt strip_tac >-
         
                        
   (  (* proving AbelianGroup (Zadd q) *)
   ‘0 < q’ by metis_tac[NOT_PRIME_0, NOT_ZERO] >>
   ‘Group (Zadd q)’by metis_tac[Zadd_group]>>
   ‘FiniteAbelianGroup (Zadd q)’by metis_tac[Zadd_finite_abelian_group]>>
    ‘AbelianGroup (Zadd q)’by metis_tac[FiniteAbelianGroup_def]
   )>-
   
   (  (* proiving  r ⊕ e ⊗ w < q *)
   ‘Field (GF q)’by metis_tac[GF_field]>>
   ‘r ∈ (GF q).carrier ∧ e ∈ (GF q).carrier ∧ w ∈ (GF q).carrier’by metis_tac[GF_element]>>
   ‘r ⊕ e ⊗ w < q’by metis_tac[field_mult_element, field_add_element, GF_element]
   )>-

   (
   Cases_on ‘e1 = e2’ THENL [
       rw[]
       ,
    (*proving  (t1 ⊕ (GF q).sum.inv t2) ⊗ Inv (GF q) (e1 ⊕ (GF q).sum.inv e2) < q *)
   ‘Field (GF q)’by metis_tac[GF_field]>>
   ‘t1 ∈ (GF q).carrier ∧ t2 ∈ (GF q).carrier ∧ e1 ∈ (GF q).carrier ∧ e2 ∈ (GF q).carrier’by metis_tac[GF_element]>>  
   qabbrev_tac‘dt = (t1 ⊕ (GF q).sum.inv t2)’>>
   qabbrev_tac‘de = (e1 ⊕ (GF q).sum.inv e2)’>>
   qabbrev_tac‘x =  dt ⊗ Inv (GF q) de’>>
   ‘de = (e1 ⊖ e2)’ by rw[] >>
   ‘de ≠ _0_’  by metis_tac[GF_sub_not_eq_zero]>>
   ‘dt = (t1 ⊖ t2)’ by rw[] >>
   ‘de ∈ (GF q).carrier ∧ dt ∈ (GF q).carrier’ by metis_tac[field_neg_element, field_sub_element] >>
   ‘de ∈ ring_nonzero (GF q)’ by metis_tac[field_nonzero_eq]>>
   ‘(Inv (GF q) de) ∈ (GF q).carrier’by metis_tac[field_inv_element]>>
   ‘(dt ⊗ Inv (GF q) de) ∈ (GF q).carrier’by metis_tac[field_mult_element]>>
   ‘x ∈ (GF q).carrier’by rw[Abbr‘x’]>>
   ‘x < q’ by metis_tac[GF_element]>>
   metis_tac[]
                ]
   )>-

        
   (  (*proving  p_1 ** t * |/ (p_2 ** e) ∈ G*)
   ‘Group g’ by gs[cyclic_def] >>
   qabbrev_tac ‘p1 = g.exp p_1 t’ >>
   qabbrev_tac ‘p2 = g.exp p_2 e’ >>
   ‘p1 ∈ g.carrier ∧ p2 ∈ g.carrier’ by metis_tac[group_exp_element] >>
   ‘g.inv p2 ∈ g.carrier’ by metis_tac[group_inv_element] >>
   ‘(g.op p1 (g.inv p2)) ∈ g.carrier’ by metis_tac[group_op_element]
   )>-


        
   (  (*proving  p_1 ** t * |/ (p_2 ** e) ∈ G*)
   ‘Group g’ by gs[cyclic_def] >>
   qabbrev_tac ‘p1 = g.exp p_1' t’ >>
   qabbrev_tac ‘p2 = g.exp p_2' e’ >>
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



Theorem or_eq_schnorr_wellformed_thm: 
  prime q ∧ cyclic g ∧ FINITE g.carrier ∧ (order g (cyclic_gen g) = q) ⇒ 
  WellFormed_SP (SP_or(SP_eq(Schnorr_SP g q)))
Proof
  simp[pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
   ‘WellFormed_SP (SP_eq(Schnorr_SP g q))’by metis_tac[eq_schnorr_wellformed_sp_thm]>>
   metis_tac[WellFormed_SP_or_thm]
QED


Theorem or_eq_schnorr_Completeness_thm: 
  prime q ∧ cyclic g ∧ FINITE g.carrier ∧ (order g (cyclic_gen g) = q) ⇒ 
  Complete_SP (SP_or(SP_eq(Schnorr_SP g q)))
Proof
  simp[pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
  ‘Complete_SP (SP_eq(Schnorr_SP g q))’ by metis_tac[eq_schnorr_Completeness_thm]>>
  ‘WellFormed_SP (SP_eq(Schnorr_SP g q))’by metis_tac[eq_schnorr_wellformed_sp_thm]>>
   ‘SimulatorCorrectness_SP (SP_eq(Schnorr_SP g q))’by metis_tac[eq_schnorr_simulator_Completeness_thm]>>              
  metis_tac[Complete_SP_or_thm]
QED

     

Theorem or_eq_schnorr_simulator_Completeness_thm: 
  prime q ∧ cyclic g ∧ FINITE g.carrier ∧ (order g (cyclic_gen g) = q) ⇒ 
  SimulatorCorrectness_SP (SP_or(SP_eq(Schnorr_SP g q)))
Proof
  simp[pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
  ‘SimulatorCorrectness_SP (SP_eq(Schnorr_SP g q))’ by metis_tac[eq_schnorr_simulator_Completeness_thm]>>
  ‘WellFormed_SP (SP_eq(Schnorr_SP g q))’by metis_tac[eq_schnorr_wellformed_sp_thm]>>
  metis_tac[SimulatorCorrectness_SP_or_thm]
QED




(*===============================================*)
  

                        
Theorem or_eq_schnorr_special_soundness_thm: 
  prime q ∧ cyclic g ∧ FINITE g.carrier ∧ (order g (cyclic_gen g) = q) ⇒ 
  SpecialSoundness_SP (SP_or(SP_eq(Schnorr_SP g q)))
Proof

   simp[pairTheory.FORALL_PROD] >>
   rpt strip_tac >>
   ‘WellFormed_SP (SP_eq(Schnorr_SP g q))’by metis_tac[eq_schnorr_wellformed_sp_thm]>>
   ‘SpecialSoundness_SP (SP_eq(Schnorr_SP g q))’ by metis_tac[eq_schnorr_special_soundness_thm]>>
   irule SpecialSoundness_SP_or_thm>>
   simp[]
                
QED
        
        
Theorem or_eq_schnorr_honest_verifier_zk_thm:
  ∀q. prime q ⇒ ∀g: 'a group. cyclic g ∧ FINITE G ∧ (ord (cyclic_gen g) = q)  ⇒ 
  HonestVerifierZeroKnowledge_SP (SP_or(SP_eq(Schnorr_SP g q)))
Proof
  simp[pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
 ‘WellFormed_SP (SP_eq(Schnorr_SP g q))’by metis_tac[eq_schnorr_wellformed_sp_thm]>>
  ‘HonestVerifierZeroKnowledge_SP (SP_eq(Schnorr_SP g q))’ by metis_tac[eq_schnorr_honest_verifier_zk_thm]>>
  metis_tac[HonestVerifierZeroKnowledge_SP_or_thm]
QED




(*----------------------------------------------*)


Datatype:
  PublicKey = <|g: num;
                p: num;
                q: num;
                y: num;
              |>
End

Datatype:
  Choice = <|alpha:  num;
             beta:  num;
           |>
End

Datatype:
  Commitment = <|A: num;
                 B: num;
               |>
End


Datatype:
  Proof = <|challenge: num;
            commitment: Commitment;
            response: num;                   
          |>
End

Datatype:
  TrusteesPublicKeys = <|g: num;
                         p: num;
                         q: num;
                         ys: num list;
                       |>
End


Datatype:
  Answer = <|choice: Choice;
             proofs: (Proof # Proof);
             trustees_public_keys: TrusteesPublicKeys;
           |>
End


Datatype:
  TrusteeData = <|public_key: PublicKey;
                  decryption_proof: Proof;
                  decryption_factor: num;
                  alphas: num list;
                |>
End

Datatype:
  ResultData = <| betas: num list;
                   trustees_public_keys: TrusteesPublicKeys;
                   decryption_factors: num list;
                   result: num;
                |>
End

        
Datatype:
  Question = <|answers_data: Answer list;
               trustees_data: TrusteeData;
               result_data: ResultData;
             |>
End

        

Datatype:
  IACR2022Election = <|Questions: Question list|>
End

(*
def verify_result(result_data):
    p = result_data['trustees_public_keys']['p']
    q = result_data['trustees_public_keys']['q']
    g = result_data['trustees_public_keys']['g']
    question_result = result_data['result']
    betas = result_data['betas']
    decryption_factors = result_data['decryption_factors']

    c = prod(betas) % p
    e = -1
    s1 = g
    s2 = prod(decryption_factors) % p
    s = (s1,s2)
    t = question_result

    sp = SchnorrSP(p,q)
    result = sp.HonestVerifier(s, c, e, t)
    return result
*)


        
Definition verify_result_def:
  verify_result (r: ResultData) =
  let  p = r.trustees_public_keys.p;
       g = r.trustees_public_keys.g;
       Gr = Zstar p;
       q = r.trustees_public_keys.q;
       df = r.decryption_factors;
       sp =  Schnorr_SP Gr q;
       s2 = FOLDR Gr.op Gr.id df;
       c = FOLDR Gr.op Gr.id r.betas; 
  in
    if r.result >= p then F (* check *)
    else
      sp.HonestVerifier ((g, Gr.inv s2), c, 1, r.result)
End


(*can this be a part of the definition of datatype?*)
Definition result_well_formed_def:
  result_well_formed(r:ResultData) ⇔
    (
    (prime r.trustees_public_keys.p ) ∧
    (∀d. MEM d r.decryption_factors ⇒ (0 < d ∧ d < r.trustees_public_keys.p)) ∧
    (∀beta. MEM beta r.betas ⇒ (0 < beta ∧ beta < r.trustees_public_keys.p)) ∧
    (0 < r.trustees_public_keys.g ∧
     r.trustees_public_keys.g <  r.trustees_public_keys.p)
    )                                  
End
        
        
                     

(**)
Definition verify_result_real_def:
  verify_result_real (r: ResultData) =
  let  p = r.trustees_public_keys.p;
       g = r.trustees_public_keys.g;
       df = r.decryption_factors;
       op = λ x y. (x * y) MOD p;
       s2 = FOLDR op 1 df;
       c = FOLDR op 1 r.betas;
       d_inv = (s2 ** (p-2)) MOD p
  in
    if r.result >= p then F
    else
      (c * d_inv) MOD p = exp_mod_binary g r.result  p
End

Theorem fold_r_zstar:
  FOLDR (Zstar p).op a xs = FOLDR (λ x y. (x * y) MOD p) a xs                           
Proof
  Induct_on‘xs’>> simp[Zstar_eval]
QED

   
Overload mmult = “λ p.FOLDR (λ x y. (x * y) MOD p) 1  ”

                    
Theorem mmult_in_range:
  (∀x. MEM x xs ⇒ 0 < x ∧ x < p) ∧ prime p ⇒
  0 < mmult p xs ∧ mmult p xs < p                          
Proof
  strip_tac>>
  ‘0<p’by (drule ONE_LT_PRIME>> simp[])>> 
  Induct_on‘xs’>> simp[Zstar_eval,   ONE_LT_PRIME, DISJ_IMP_THM, FORALL_AND_THM]>>        
  rw[]>>
   CCONTR_TAC >>
  gs[]>>
  gs[MOD_EQ_0_DIVISOR]>>
  ‘p divides (h * mmult p xs)’by metis_tac[divides_def]>>
  qpat_x_assum ‘_ = _’ kall_tac>>
  drule_all helperNumTheory.euclid_prime >>
  strip_tac>>
  drule DIVIDES_LEQ_OR_ZERO>>
  simp[]
QED
        

Theorem verify_result_equivalent_def:
  result_well_formed r  ⇒
  verify_result r = verify_result_real r
Proof
  simp[verify_result_real_def, verify_result_def, Schnorr_SP_def, Zstar_eval,
       EulerTheory.residue_thm, Zstar_exp, fold_r_zstar, result_well_formed_def, exp_mod_binary_eqn]>>
  strip_tac >>
  qabbrev_tac ‘p = r.trustees_public_keys.p’ >>
  qabbrev_tac ‘g = r.trustees_public_keys.g’ >>
  qabbrev_tac ‘ds = r.decryption_factors’ >>
  qabbrev_tac ‘βs = r.betas’ >>
  qabbrev_tac ‘β = mmult p βs’ >>
  qabbrev_tac ‘d = mmult p ds’ >>
  qabbrev_tac ‘res = g ** r.result’>>
  ‘FiniteAbelianGroup (Zstar p)’ by rw_tac std_ss[Zstar_finite_abelian_group] >>
  ‘Group  (Zstar p)’by metis_tac[ FiniteAbelianGroup_def,  AbelianGroup_def]>>
  ‘(Zstar p).inv d ∈ (Zstar p).carrier’by metis_tac[group_inv_element, Zstar_element, mmult_in_range]>>        
  ‘(Zstar p).exp ((Zstar p).inv d) 1 = ((Zstar p).inv d ** 1) MOD p’by metis_tac[Zstar_exp]>>
  ‘((Zstar p).inv d) ** 1 =  (Zstar p).inv d’by metis_tac[EXP_1]>>
  ‘(Zstar p).inv d = d **(p-2) MOD p’by metis_tac[Zstar_inverse, mmult_in_range]>>
  qabbrev_tac ‘din =  d ** (p − 2) MOD p’ >> 
  ‘ (d ** (p − 2) * β) MOD p = (β * din) MOD p’suffices_by rw[MOD_TIMES2]>>
  ‘ (((d ** (p − 2)) MOD p) * (β MOD p)) MOD p = (β * din) MOD p’suffices_by rw[MOD_TIMES2]>>
  ‘(din * (β MOD p)) MOD p = (β * din) MOD p’suffices_by rw[]>>
  ‘β < p’by metis_tac[mmult_in_range]>>
  ‘(din * β MOD p) MOD p = (β * din) MOD p’suffices_by rw[]>>
  simp[]
QED
        

Definition verify_decryption_def:
  verify_decryption (trustee: TrusteeData) =
  let  p = trustee.public_key.p;
       g = trustee.public_key.g;
       Gr = Zstar p;
       q = trustee.public_key.q;
       d = trustee.decryption_factor;
       y = trustee.public_key.y;
       e = trustee.decryption_proof.challenge;
       t = trustee.decryption_proof.response;
       A = trustee.decryption_proof.commitment.A;
       B = trustee.decryption_proof.commitment.B;
       αs = trustee.alphas;
       α = FOLDR Gr.op Gr.id αs;
       sp =  Schnorr_SP Gr q;
       sp_eq = SP_eq sp;
       s = ((g,y),(α,d));
       c = (A,B);
  in
      sp_eq.HonestVerifier (s,c,e,t)
End

(*can this be a part of the definition of datatype?*)
Definition trustee_well_formed_def:
  trustee_well_formed (trustee:TrusteeData) ⇔
    (
    (prime trustee.public_key.p) ∧
    (0 < trustee.decryption_factor ∧ trustee.decryption_factor < trustee.public_key.p) ∧
    (0 < trustee.public_key.y ∧ trustee.public_key.y < trustee.public_key.p) ∧
    (∀alpha. MEM alpha trustee.alphas ⇒ (0 < alpha ∧ alpha < trustee.public_key.p)) ∧
    (0 < trustee.public_key.g ∧
     trustee.public_key.g < trustee.public_key.p)∧
     (0 < trustee.decryption_proof.commitment.A ∧ trustee.decryption_proof.commitment.A < trustee.public_key.p) ∧
     (0 < trustee.decryption_proof.commitment.B ∧ trustee.decryption_proof.commitment.B < trustee.public_key.p)
    )                                  
End
        
        
                     

(**)
Definition verify_decryption_real_def:
  verify_decryption_real (trustee: TrusteeData) =
  let  p = trustee.public_key.p;
       g = trustee.public_key.g;
       Gr = Zstar p;
       q = trustee.public_key.q;
       d = trustee.decryption_factor;
       y = trustee.public_key.y;
       e = trustee.decryption_proof.challenge;
       t = trustee.decryption_proof.response;
       A = trustee.decryption_proof.commitment.A;
       B = trustee.decryption_proof.commitment.B;
       αs = trustee.alphas;
       op = λ x y. (x * y) MOD p;
       α = FOLDR op 1 αs;

  in
    exp_mod_binary g t p = (A * (exp_mod_binary y e p)) MOD p ∧
    exp_mod_binary α t p = (B * (exp_mod_binary d e p)) MOD p            
End

                         

Theorem verify_decryption_equivalent_def:
 trustee_well_formed trustee ⇒
  verify_decryption trustee = verify_decryption_real trustee
Proof
  simp[verify_decryption_real_def, verify_decryption_def, Schnorr_SP_def, SP_eq_def, Zstar_eval,
       EulerTheory.residue_thm, Zstar_exp, fold_r_zstar, trustee_well_formed_def, exp_mod_binary_eqn]>>
  strip_tac >>
  qabbrev_tac ‘p = trustee.public_key.p’ >>
  qabbrev_tac ‘g = trustee.public_key.g’ >>
  qabbrev_tac ‘t = trustee.decryption_proof.response’ >>
  qabbrev_tac ‘y = trustee.public_key.y’ >>
  qabbrev_tac ‘A = trustee.decryption_proof.commitment.A’ >>
  qabbrev_tac ‘B' = trustee.decryption_proof.commitment.B’ >>
  qabbrev_tac ‘e = trustee.decryption_proof.challenge’ >>
  qabbrev_tac ‘d = trustee.decryption_factor’ >>
  qabbrev_tac ‘αs = trustee.alphas’ >>
  qabbrev_tac ‘LHS1 =  g ** t MOD p’ >>
  qabbrev_tac ‘RHS2 = (B' * d ** e) MOD p’ >>
  ‘(A * (Zstar p).exp y e) MOD p = (A * y ** e) MOD p ∧
       (Zstar p).exp (mmult p αs) t = mmult p αs ** t MOD p’suffices_by metis_tac[]>>
  ‘FiniteAbelianGroup (Zstar p)’ by rw_tac std_ss[Zstar_finite_abelian_group] >>
  ‘Group  (Zstar p)’by metis_tac[ FiniteAbelianGroup_def,  AbelianGroup_def]>>
  ‘(Zstar p).exp y e = y ** e MOD p’ by metis_tac[Zstar_element, Zstar_exp]>>
  ‘0 < p’by metis_tac[PRIME_POS]>>   
  ‘A MOD p = A ’by metis_tac[X_MOD_Y_EQ_X]>>
  ‘ (A * (Zstar p).exp y e) MOD p = (A * y ** e) MOD p’by  metis_tac[MOD_TIMES2]>>
    qabbrev_tac‘x= (mmult p αs)’>>
  ‘0 < x ∧ x < p’by metis_tac[ mmult_in_range]>>
  ‘ (Zstar p).exp x t = x ** t MOD p’by metis_tac[Zstar_element, Zstar_exp]>>
    simp[]
QED
        




Definition verify_encryption_def:
  verify_encryption (a: Answer) =
  let  p = a.trustees_public_keys.p;
       g = a.trustees_public_keys.g;
       Gr = Zstar p;
       q = a.trustees_public_keys.q;
       ys = a.trustees_public_keys.ys;
       epk = FOLDR Gr.op Gr.id ys;
       α = a.choice.alpha;
       β = a.choice.beta;

       proof_1 = FST a.proofs;
       proof_2 = SND a.proofs;
       
       e1 = proof_1.challenge;
       e2 = proof_2.challenge;

       t1 = proof_1.response;
       t2 = proof_2.response;

       A1 = proof_1.commitment.A;
       A2 = proof_2.commitment.A;

       B1 = proof_1.commitment.B;
       B2 = proof_2.commitment.B;

       c = ((A1,B1),(A2,B2));
       t = ((t1,e1),t2);
       s7 = Gr.op β (Gr.inv g);

       s = (((g, α),(epk,β)), ((g,α), (epk, s7)));
           
       sp =  Schnorr_SP Gr q;
       sp_eq = SP_eq sp;
       sp_or = SP_or sp_eq;
       e = SP_csub sp e1 (SP_csub sp ( SP_csub sp e1 e2) e1) 
  in
      sp_or.HonestVerifier (s,c,e,t)
End


Definition answer_well_formed_def:
  answer_well_formed (a:Answer) ⇔
    (
    (prime a.trustees_public_keys.p) ∧
    (0 < a.choice.alpha ∧ a.choice.alpha < a.trustees_public_keys.p) ∧
    (0 < a.choice.beta ∧ a.choice.beta < a.trustees_public_keys.p) ∧
    (∀y. MEM y a.trustees_public_keys.ys ⇒ (0 < y ∧ y < a.trustees_public_keys.p)) ∧  
    (0 <  a.trustees_public_keys.g ∧  a.trustees_public_keys.g < a.trustees_public_keys.p)∧
    (0 <(FST a.proofs).commitment.A ∧(FST a.proofs).commitment.A < a.trustees_public_keys.p) ∧ 
     (0 <(SND a.proofs).commitment.A ∧(SND a.proofs).commitment.A < a.trustees_public_keys.p) ∧
     (0 <(FST a.proofs).commitment.B ∧(FST a.proofs).commitment.B < a.trustees_public_keys.p) ∧ 
     (0 <(SND a.proofs).commitment.B ∧(SND a.proofs).commitment.B < a.trustees_public_keys.p)  
    )                                  
End
        
        

(**)
Definition verify_encryption_real_def:
  verify_encryption_real (a: Answer) =
  let  p = a.trustees_public_keys.p;
       g = a.trustees_public_keys.g;
       Gr = Zstar p;
       op = λ x y. (x * y) MOD p;
       q = a.trustees_public_keys.q;
       ys = a.trustees_public_keys.ys;
       epk = FOLDR op 1 ys;
       α = a.choice.alpha;
       β = a.choice.beta;

       proof_1 = FST a.proofs;
       proof_2 = SND a.proofs;
       
       e1 = proof_1.challenge;
       e2 = proof_2.challenge;

       t1 = proof_1.response;
       t2 = proof_2.response;

       A1 = proof_1.commitment.A;
       A2 = proof_2.commitment.A;

       B1 = proof_1.commitment.B;
       B2 = proof_2.commitment.B;

       c = ((A1,B1),(A2,B2));
       t = ((t1,e1),t2);
       s7 = Gr.op β (Gr.inv g);

       s = (((g, α),(epk,β)), ((g,α), (epk, s7)));
  in
    exp_mod_binary g t1 p = (A1 * (exp_mod_binary α e1 p)) MOD p ∧
    exp_mod_binary epk t1 p = (B1 * (exp_mod_binary β e1 p)) MOD p ∧
    exp_mod_binary g t2 p = (A2 * (exp_mod_binary α e2 p)) MOD p ∧
    exp_mod_binary epk t2 p = (B2 * (exp_mod_binary s7 e2 p)) MOD p     
End

           
        
val _ = export_theory();




