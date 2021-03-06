(*---------------------------------------------------------------------------
   Models of equational theory
   ---------------------------------------------------------------------------*)
Require Import ssreflect ssrbool ssrfun seq.
Require Import Relations Program.Equality.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import exp.


Section Models.

Variable sig: SIG.
Variable interpPrim: PrimType sig -> Type.

(* Interpretation of sorts and index operations *)
Structure Interpretation := mkInterpretation {
  (* Carrier for each sort *)
  interpSrt : Srt sig -> Type; 

  (* Function for each index operation *)
  interpOp p : Env interpSrt (opArity p).1 -> interpSrt (opArity p).2  
}.

Implicit Arguments interpOp [].

Definition interpVar I D s (v: Var D s) (env: Env (interpSrt I) D) := lookup v env.  

(* Interpret an index expression compositionally *)
Fixpoint interpExp I D s (e: Exp D s) : Env (interpSrt I) D -> interpSrt I s :=
  match e with
  | VarAsExp _ v => fun env => interpVar v env
  | AppCon op es => fun env => interpOp I op (interpExps es env)
  end

with interpExps I D ss (es: Exps D ss) (env: Env (interpSrt I) D)
  : Env (interpSrt I) ss :=
  if es is Cons _ _ ix ixs then (interpExp ix env, interpExps ixs env) else tt.

(* Axioms are interpreted by Leibniz equality in the model; this is fine for ssreflect-style
   but does mean that we don't have a "free" interpretation *)
Definition interpAx I (A: Ax sig) := 
  let: mkAx D s lhs rhs := A in
  forall env: Env (interpSrt I) D, interpExp lhs env = interpExp rhs env.

Fixpoint interpAxs I (As: seq (Ax sig)) :=
  if As is A::As then interpAx I A /\ interpAxs I As else True.

(* A model is an interpretation together with a proof that the axioms are satisfied *)
Structure Model A := mkModel {
  I :> Interpretation;
  soundness: interpAxs I A
}.

Fixpoint apArgs A (M1 M2: Model A) arity (f:forall s, interpSrt M1 s -> interpSrt M2 s) :
  Env (interpSrt M1) arity -> Env (interpSrt M2) arity :=
  if arity is s::ss
  then fun args => (f s args.1, apArgs f args.2) 
  else fun args => tt.

Fixpoint seqAsExps D D' : Env (Exp (sig:=sig) D) D' -> Exps D D' :=
  if D' is s::D' 
  then fun ixs => Cons ixs.1 (seqAsExps ixs.2)
  else fun _ => Nil _.

Definition mkFreeInterpretation D : Interpretation := 
  mkInterpretation (fun p ixs => AppCon (D:=D) p (seqAsExps ixs)).

Lemma interpApSubVar M D :
  (forall s (v : Var D s) D' (S: Sub (sig:=sig) D D') (d: Env (interpSrt M) D'), 
    interpExp (apSub S v) d = interpVar v (interpExps (subAsExps S) d)).
Proof. dependent induction v => //.  
move => D' S d. by rewrite/= -IHv. 
Qed. 

Lemma interpExpApSub M D :
  (forall s (e : Exp D s) D' (S: Sub (sig:=sig) D D') (d: Env (interpSrt M) D'), 
    interpExp (apSub S e) d = interpExp e (interpExps (subAsExps S) d)) /\
  (forall ss (es: Exps D ss) D' (S: Sub (sig:=sig) D D') (d: Env (interpSrt M) D'),
    interpExps (apSubSeq S es) d = interpExps es (interpExps (subAsExps S) d)).
Proof. apply Exp_Exps_ind. 
+ move => s v D' S d. by rewrite interpApSubVar. 
+ move => op e IH D' S d. by rewrite apSubAppCon/= IH. 
+ done. 
+ move => s ss e IH es IH' D' S d. by rewrite apSubSeqCons/= IH IH'. 
Qed. 

Lemma equivInterps D :
   (forall s A (e f: Exp (sig:=sig) D s), 
    equiv A e f ->
    forall (M: Model A) (d: Env (interpSrt M) D),
    interpExp e d = interpExp f d)
/\ (forall ss A (es fs: Exps D ss), 
    equivSeq A es fs -> 
    forall (M: Model A) (d: Env (interpSrt M) D),
    interpExps es d = interpExps fs d).
Proof.
apply equivBoth_ind.
(* EquivRefl *)
+ done. 
(* EquivSym *)
+ done. 
(* EquivTrans *)
+ move => s A e1 e2 e3 H1 IH1 H2 IH2 M d. by rewrite IH1 IH2. 
(* EquivComp *)
+ move => A p es es' H IH M d. simpl. by rewrite IH. 
(* EquivByAxZ *)
+ move => s A D'' S' e e' M d. 
destruct M as [I [ax axs]]. 
simpl in ax. 
rewrite 2!(proj1 (interpExpApSub _ _)). by rewrite ax. 
(* EquivByAxS *)
+ move => s A As e e' E1 E2 M d.
destruct M as [I [ax axs]]. 
fold interpAxs in axs. 
specialize (E2 (mkModel axs)). by rewrite E2. 
(* EquivNil *)
+ done. 
(* EquivCons *)
+ move => A s ss e1 e2 es1 es2 E1 E2 E3 E4 M d. simpl. by rewrite E2 E4. 
Qed. 

Lemma composeInterps 
  M D'' D D' (S: Sub (sig:=sig) D' D) (d : Env (interpSrt M) D)
  (es : Sub D'' D') :
   interpExps (subAsExps (ScS S es)) d =
   interpExps (subAsExps es) (interpExps (subAsExps S) d).
Proof. 
induction D'' => //. specialize (IHD'' (tlSub es)).
simpl. rewrite /hdSub.   
rewrite -IHD''.
replace (tlSub (ScS S es)) with (ScS S (tlSub es)) by done.
by rewrite (proj1 (interpExpApSub _ _)).
Qed.  


(* Pointwise product of models is itself a model *)
Definition interpSrtProd (I1 I2: Interpretation) :=
  fun s => (interpSrt I1 s * interpSrt I2 s)%type. 

Definition fstEnv (I1 I2: Interpretation) arity 
  (env: Env (interpSrtProd I1 I2) arity) := 
  mapEnv (fun s => @fst _ (interpSrt I2 s)) env.

Definition sndEnv (I1 I2: Interpretation) arity 
  (env: Env (interpSrtProd I1 I2) arity) := 
  mapEnv (fun s => @snd (interpSrt I1 s) _) env.

(*
Fixpoint pairEnv (I1 I2: Interpretation) arity (env1: Env (interpSrt I1) arity) (env2: Env (interpSrt I2) arity) : Env (interpSrtProd I1 I2) arity. 
*)
Definition prodInterp (I1 I2: Interpretation) : Interpretation :=
  mkInterpretation
  (fun p env => (interpOp I1 p (fstEnv env),
                 interpOp I2 p (sndEnv env))).

Lemma interpExpFst D (I1 I2: Interpretation) env :
  (forall (s:Srt sig) (e : Exp D s), 
    interpExp e (fstEnv env) = fst (interpExp (I:=prodInterp I1 I2) e env)) /\ 
  (forall ss (es: Exps D ss), 
    interpExps es (fstEnv env) = fstEnv (interpExps (I:=prodInterp I1 I2) es env)).
Proof. 
apply Exp_Exps_ind.
(* Variable *)
move => s v. by rewrite /= /interpVar lookupMapEnv. 
(* AppCon *)
move => op es IH. by rewrite /= IH. 
(* nil *)
done. 
(* cons *)
move => s ss e IH1 es IH2. by rewrite /= IH1 IH2. 
Qed. 

Lemma interpExpSnd D (I1 I2: Interpretation) env :
  (forall (s:Srt sig) (e : Exp D s), 
    interpExp e (sndEnv env) = snd (interpExp (I:=prodInterp I1 I2) e env)) /\ 
  (forall ss (es: Exps D ss), 
    interpExps es (sndEnv env) = sndEnv (interpExps (I:=prodInterp I1 I2) es env)).
Proof. 
apply Exp_Exps_ind.
(* Variable *)
move => s v. by rewrite /= /interpVar lookupMapEnv. 
(* AppCon *)
move => op es IH. by rewrite /= IH. 
(* nil *)
done. 
(* cons *)
move => s ss e IH1 es IH2. by rewrite /= IH1 IH2. 
Qed. 


Lemma interpExpPair D (I1 I2: Interpretation) env s (e: Exp D s):
  interpExp (I:=prodInterp I1 I2) e env = 
  (interpExp e (fstEnv env), interpExp e (sndEnv env)).
Proof. 
induction e. 
(* Variable *)
rewrite /= /interpVar !lookupMapEnv. by elim E: (lookup v env). 
(* AppCon *)
by rewrite /= (proj2 (interpExpFst _)) (proj2 (interpExpSnd _)). 
Qed. 

Program Definition prodModel A (M1 M2: Model A) : Model A := 
  mkModel (I:= prodInterp M1 M2) _.
Next Obligation.
induction A => //.
split.
destruct M1 as [I1 [s1 s1']]. destruct M2 as [I2 [s2 s2']]. 
simpl.
destruct a. move => env. 
simpl in env.  
specialize (s1 (fstEnv env)). specialize (s2 (sndEnv env)). 
clear s1' s2'. move: s1 s2. 
rewrite !(proj1 (interpExpFst _)). 
rewrite !(proj1 (interpExpSnd _)).
rewrite !interpExpPair /=. move ->. move ->. done.

destruct M1 as [I1 [a1 A1]].  
destruct M2 as [I2 [a2 A2]].
apply (IHA (mkModel A1) (mkModel A2)). 
Qed. 

End Models.