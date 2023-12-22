
(* ------------------------------------------------------------------------- *)
(* -- Sigma Protocol Definitions -- *)
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


        
Datatype:
  Commitment = <|A: num;
                 B: num;
               |>
End
     
   
Datatype:
Proof = <|Challenge: num;
          Commitment: Commitment;
          Response: num;                   
         |>
End

        
Datatype:
  Choice = <|Alpha: num;
             Beta: num;
           |>
End
                       

Datatype:
  PublicKey = <|g: num;
                 p: num;
                 q: num;
                 y: num;
               |>
End


Datatype:
  VoterAnswer = <|Choice: Choice;
                  Individual_proof: Proof # Proof;
                  Overall_proof: (Proof # Proof) option;
                    |>
End

Datatype:
  TrusteeDecryption = <|Decryption_factor: num;
                        Decryption_proof: Proof;
           
                      |>
End                 
                   

Datatype:
  Question = <|Answers: VoterAnswer list;
               Decryption: TrusteeDecryption list;
               Result: num;
             |>
End


Type Election = “:Question list”
        
Datatype:
  IACR2022Election = <|Questions: Question list; (* 12 items*)
                       ElectionPK: pk
                       TrusteesPK: pk list|>
End

        
       

       
Definition Hash_def:
  Hach SHA2 = c Have in HOL, need to translate to cakeML
End

(*
Questions:
Do I need another protocol such as Voter_SP as a modified schnorr?
I am struggling to fit vote into schnorr.

Hardcode datatype to the specific Election             

Datatype: Result = 
        
TODO: Prove Election properties same as in Thomas paper:
          
*)

(* TODO: Prove correctness, special coundness, zero-knowledge, simulator-correctness, well-formedness *)                           
Definition Voter_SP_or_def:
  Voter_SP_or gr q = SP_or (Voter_SP gr q) 
End

(* TODO: Prove correctness, special coundness, zero-knowledge, simulator-correctness, well-formedness *)     
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

   
                    
        
*)  
                
val _ = export_theory();

