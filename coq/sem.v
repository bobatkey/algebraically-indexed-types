Require Import ssreflect ssrbool ssrfun seq.
Require Import Relations Program.Equality Rel.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import exp ty Casts model.

Reserved Notation "| t |" (at level 60).

(*---------------------------------------------------------------------------
   Underlying semantics
   ---------------------------------------------------------------------------*)
Section Sem.

Variable sig: SIG.
Variable interpPrim: PrimType sig -> Type.

(* Index-erasure interpretation of types, parameterized
   on the interpretation of primitive types *)
Fixpoint interpTy D (t: Ty D) : Type :=
  match t with
  | TyUnit       => unit
  | TyProd t1 t2 => |t1| * |t2|
  | TySum  t1 t2 => |t1| + |t2|
  | TyArr  t1 t2 => |t1| -> |t2|
  | TyAll    _ t => |t| 
  | TyExists _ t => |t|
  | TyPrim   p _ => interpPrim p
  end%type
where "| t |" := (interpTy t).

Fixpoint existentialFree D (t: Ty (sig:=sig) D) :=
  match t with
  | TyUnit       => True
  | TyProd t1 t2 => existentialFree t1 /\ existentialFree t2
  | TySum  t1 t2 => existentialFree t1 /\ existentialFree t2
  | TyArr  t1 t2 => existentialFree t1 /\ existentialFree t2
  | TyAll    _ t => existentialFree t
  | TyExists _ t => False
  | TyPrim   p _ => True
  end.

Fixpoint quantifierFree D (t: Ty (sig:=sig) D) :=
  match t with
  | TyUnit       => True
  | TyProd t1 t2 => quantifierFree t1 /\ quantifierFree t2
  | TySum  t1 t2 => quantifierFree t1 /\ quantifierFree t2
  | TyArr  t1 t2 => quantifierFree t1 /\ quantifierFree t2
  | TyAll    _ t => False
  | TyExists _ t => False
  | TyPrim   p _ => True
  end.

Definition interpCtxt D : Ctxt D -> Type := Env (@interpTy _).  

Lemma interpCtxtCons D (g: Ty D) (G: Ctxt D) : interpCtxt (g::G) = (interpTy g * interpCtxt G)%type. 
Proof. done. Qed. 

(* This is lemma 3, part 1 *)
Lemma interpEquiv D (t1 t2: Ty D) A : equivTy A t1 t2 -> |t1| = |t2|.
Proof. move => E. induction E => /=//; congruence. Qed. 

(* This is lemma 3, part 2 *)
Lemma interpSubst D (t: Ty D) : forall D' (S: Sub D D'), |t| = |apSubTy S t|.
Proof. induction t => /=//; congruence. Qed.

Lemma interpTyAll D s (t: Ty (s::D)) e : |TyAll t| = |apSubTy (consSub e (idSub D)) t|.
Proof. by rewrite -interpSubst. Qed.

Lemma interpTyExists D s (t: Ty (s::D)) e : |apSubTy (consSub e (idSub D)) t| = |TyExists t|.
Proof. by rewrite -interpSubst. Qed.

Lemma interpTyPack D s (t: Ty (s::D)) : |TyExists t| = |t|. Proof. done. Qed.

Lemma interpSubCtxt D (G: Ctxt D) : forall D' (S: Sub D D'), interpCtxt G = interpCtxt (apSubCtxt S G). 
Proof. 
induction G. done. move => D' S. by rewrite interpCtxtCons (interpSubst _ S) (IHG _ S). 
Qed. 

Definition interpTmVar D (G: Ctxt D) (t: Ty D) (v: TmVar G t) : interpCtxt G -> (|t|) :=
  lookup v. 

Fixpoint interpTm A D (G: Ctxt D) (t: Ty D) (M: Tm A G t) : interpCtxt G -> (|t|) :=
  match M in Tm _ _ t return interpCtxt G -> |t| with
  | VAR _ v       => fun eta => interpTmVar v eta
  | UNIT          => fun eta => tt
  | TYEQ _ _ pf M => fun eta => interpTm M eta :? interpEquiv pf 
  | PAIR _ _ M N  => fun eta => (interpTm M eta, interpTm N eta)
  | PROJ1 _ _ M   => fun eta => (interpTm M eta).1
  | PROJ2 _ _ M   => fun eta => (interpTm M eta).2
  | INL _ _ M     => fun eta => inl _ (interpTm M eta)
  | INR _ _ M     => fun eta => inr _ (interpTm M eta)
  | CASE _ _ _ M M1 M2 => fun eta => 
    match interpTm M eta with 
    | inl x => interpTm M1 (x,eta) 
    | inr y => interpTm M2 (y,eta) 
    end
  | ABS _ _ M     => fun eta => fun x => interpTm M (x,eta)
  | APP _ _ M N   => fun eta => (interpTm M eta) (interpTm N eta)
  | UNIVABS s t M  => fun eta => interpTm M (eta :? interpSubCtxt G (pi D s))
  | UNIVAPP s t e M => fun eta => interpTm M eta :? interpTyAll t e
  | EXPACK _ e t M => fun eta => interpTm M eta :? interpTyExists t e
  | EXUNPACK s t t' M N => fun eta => 
    interpTm N (interpTm M eta :? interpTyPack t, eta :? interpSubCtxt G (pi D s)) 
      :? sym_equal (interpSubst t' (pi D s))
  end.

(*---------------------------------------------------------------------------
   Relational semantics

   Some problems with logical relations:
   * Existentials mess up proof that difunctional environments => difunctional semantics
   * Would like to prove composition property but function types mess it up
   * Perhaps should attempt to use prelogical relations of some kind
   * Or perhaps we could do perp-perp for existentials
   * Or perhaps just take "difunctional closure"
   ---------------------------------------------------------------------------*)

Structure ModelEnv A := mkModelEnv {
  M:> Model A;
  relInterp X : Env (interpSrt M) (tyArity X) -> relation (interpPrim X)
}.

Definition prodModelEnv A (ME1 ME2: ModelEnv A) : ModelEnv A :=
  mkModelEnv (M:=prodModel ME1 ME2)
  (fun X env => fun x y => @relInterp _ ME1 X (fstEnv env) x y /\
                           @relInterp _ ME2 X (sndEnv env) x y).

(* Relation environments *)
Definition RelEnv A (M:Model A) := Env (interpSrt (sig:=sig) M). 

(* Compose environment with substitution *)
Definition EcS D D' A (M:Model A) (rho: RelEnv M D'): Sub D D' -> RelEnv M D := 
  mapEnv (fun _ e => interpExp e rho). 

Fixpoint semTy A (ME: ModelEnv A) D (rho: RelEnv ME D) (t:Ty D) : relation (|t|) :=
  match t return relation (|t|) with
  | TyUnit       => fun x y => True
  | TyProd t1 t2 => fun x y => semTy rho x.1 y.1 /\ semTy rho x.2 y.2
  | TySum t1 t2  => fun x y => 
    match x, y with inl x1, inl y1 => semTy rho x1 y1
                  | inr x2, inr y2 => semTy rho x2 y2
                  | _, _ => False 
    end
  | TyArr t1 t2  => fun x y => forall x' y', semTy rho x' y' -> semTy rho (x x') (y y')
  | TyPrim p ixs => fun x y => relInterp (interpExps ixs rho) x y
  | TyAll    s t => fun x y => forall k, semTy (D:=s::D) (k,rho) x y
  | TyExists s t => fun x y => exists k, semTy (D:=s::D) (k,rho) x y
  end.

Implicit Arguments semTy [D ME].  

(*Notation "rho |= x == y :> t" := (semTy (t:=t) rho x y) (at level 67, x at level 67, y at level 67).*)

Fixpoint semCtxt A (ME: ModelEnv A) D (rho: RelEnv ME D) (G:Ctxt D) : relation (interpCtxt G) :=
  if G is t::G then fun eta1 eta2 => semTy A rho t eta1.1 eta2.1 /\ semCtxt rho eta1.2 eta2.2
  else fun _ _ => True.

(*---------------------------------------------------------------------------
   Unfortunately we need casts just to state the semSubst and semEquiv lemmas. 
   "up" sends a value from |t| to |apSubTy S t|
   "dn" sends a value from |apSubTy S t| to |t|
   We have various lemmas connecting these.
   ---------------------------------------------------------------------------*)
Section UpDn. 

  Variables D D' : IxCtxt sig.
  Variables S : Sub D D'.
  Variables t t1 t2 : Ty D.
  Variable A: seq (Ax sig). 
  Variables E : equivTy A t1 t2.

  Definition up t x := x :? interpSubst t S.
  Definition dn t x := x :? sym_equal (interpSubst t S).
  Definition rt x := x :? interpEquiv E.

  Lemma dnup (x: |t|) : dn (up x) = x.
  Proof. by rewrite /up/dn cast_coalesce cast_id. Qed. 

  Lemma updn (x: |apSubTy S t|) : up (dn x) = x.
  Proof. by rewrite /up/dn cast_coalesce cast_id. Qed. 
End UpDn.

Section UpDnProps.

  Variables D D' : IxCtxt sig.
  Variables S : Sub D D'.
  Variables t t1 t2 t1' t2' : Ty D.

  Lemma upApp (f: |TyArr t1 t2|) (x: |t1|) : up S (f x) = (up _ f) (up S x). 
  Proof. rewrite /up. apply cast_app. Qed. 

  Lemma upFst (p: |TyProd t1 t2|) : (up _ p).1 = (up S p.1).
  Proof. rewrite /up. apply (cast_fst (interpSubst t1 S) (interpSubst t2 S)). Qed. 

  Lemma upSnd (p: |TyProd t1 t2|) : (up _ p).2 = (up S p.2).
  Proof. rewrite /up. apply (cast_snd (interpSubst t1 S) (interpSubst t2 S)). Qed. 

  Lemma upInl (x: |t1|) : up (t:=TySum t1 t2) S (inl _ x) = inl _ (up (t:=t1) S x).
  Proof.  
  rewrite /up. apply (cast_inl (interpSubst t1 S) (interpSubst t2 S)). 
  Qed. 

  Lemma upInr (x: |t2|) : up (t:=TySum t1 t2) S (inr _ x) = inr _ (up (t:=t2) S x).
  Proof.  
  rewrite /up. apply (cast_inr (interpSubst t1 S) (interpSubst t2 S)). 
  Qed. 

  Lemma upSpec s (ty: Ty (s::D)) (x: | TyAll ty|): up S x = up (liftSub _ S) x.
  Proof. rewrite /up. by apply cast_UIP. Qed. 

  Lemma upInst s (ty: Ty (s::D)) (x: | TyExists ty|): up S x = up (liftSub _ S) x.
  Proof. rewrite /up. by apply cast_UIP. Qed. 

End UpDnProps.


Lemma semTyCast A (ME:ModelEnv A) D1 D2 (t1: Ty D1) (t2: Ty D2) (rho: RelEnv ME _) (v1 v2: |t1|) (p1 p2 p3 p4: (|t1|) = (|t2|) ) : 
  semTy A rho t2 (v1 :? p1) (v2 :? p2) ->
  semTy A rho t2 (v1 :? p3) (v2 :? p4).
Proof.   
move => H.
by rewrite (cast_UIP v1 _ p1) (cast_UIP v2 _ p2). 
Qed. 

(* This is lemma 2, part 1 *)
Lemma semEquiv : forall A (ME: ModelEnv A) D (t1 t2: Ty D) (E: equivTy A t1 t2) 
 (rho: RelEnv ME D) (v v':interpTy t1),
  (semTy A rho t1 v v' <->
  semTy A rho t2 (rt E v) (rt E v')). 
Proof.
move => A ME D t1 t2 E.
(* Not sure why this needs generalizing. But the induction won't go through otherwise. *)
rewrite /rt.
move: (interpEquiv E).
induction E => pf rho v v'. 
(* EquivTyRefl *)
by rewrite 2!cast_id. 
(* EquivTySym *)
rewrite (IHE _ (sym_equal pf)) => //. rewrite cast_coalesce => //. 
by rewrite cast_id cast_coalesce cast_id. 
(* EquivTyTrans *)
rewrite (IHE1 _ (interpEquiv E1)) => //.
rewrite (IHE2 _ (interpEquiv E2)) => //. 
rewrite 2!cast_coalesce.  
split => H. apply (semTyCast _ _ H). apply (semTyCast _ _ H). 
(* EquivTyProd *)
simpl. rewrite !(cast_fst (interpEquiv E1) _). 
rewrite !(cast_snd _ (interpEquiv E2)). 
rewrite -(IHE1 _ (interpEquiv E1)) => //. rewrite -(IHE2 _ (interpEquiv E2)) => //. 
apply (interpEquiv E1). apply (interpEquiv E1). apply (interpEquiv E2). apply (interpEquiv E2). 
(* EquivTySum *)
destruct v. 
destruct v'.
+ simpl. by rewrite !(cast_inl (interpEquiv E1) (interpEquiv E2)) -IHE1. 
+ simpl. by rewrite !(cast_inr (interpEquiv E1) (interpEquiv E2))
        !(cast_inl (interpEquiv E1) (interpEquiv E2)). 
destruct v'. 
+ simpl. by rewrite !(cast_inr (interpEquiv E1) (interpEquiv E2))
        !(cast_inl (interpEquiv E1) (interpEquiv E2)). 
+ simpl. by rewrite !(cast_inr (interpEquiv E1) (interpEquiv E2)) -IHE2. 
(* EquivTyArr *)
have eq1:=interpEquiv E1. have eq2:=interpEquiv E2.
simpl. 
split => H x x' xx'.
+ rewrite 2!cast_appFun. 
  rewrite -IHE2 => //. 
  apply H. 
  rewrite (IHE1 _ eq1) => //. 
  rewrite !cast_coalesce. rewrite !cast_id. apply xx' => //. 
+ rewrite (IHE2 _ eq2) => //. 
  specialize (H (x :? eq1) (x' :? eq1)). 
  rewrite 2!(cast_app eq1 eq2). apply H. 
  rewrite -IHE1 => //. 
(* EquivTyPrim *)
simpl.
rewrite !cast_id.
by rewrite (proj2 (equivInterps _) _ _ es es'). 
(* EquivTyAll *)
simpl. split. 
move => H rho'. rewrite -IHE => //. 
move => H rho'. rewrite IHE => //. 
(* EquivTyExists *)
simpl. 
split. 
move => [rho' H]. exists rho'. rewrite -IHE => //. 
move => [rho' H]. exists rho'. rewrite IHE => //. 
apply H. 
Qed. 

(* If the base relations are difunctional, so is the semantics of types *)
Lemma sem_difunctional A (ME: ModelEnv A) : 
  (forall p (rho: RelEnv ME (tyArity p)), difunctional (relInterp rho)) ->
  forall D (t: Ty D) (psi: RelEnv ME D), existentialFree t -> difunctional (semTy A psi t).
Proof.
  move => DIF. 
  induction t => /= rho EF. 
  
  (* TyUnit *)
  by intuition. 

  (* TyProd *) 
  elim: EF => [EF1 EF2].
  specialize (IHt1 rho EF1). specialize (IHt2 rho EF2). by apply: prod_difunctional.  

  (* TySum *)
  elim: EF => [EF1 EF2].
  specialize (IHt1 rho EF1). specialize (IHt2 rho EF2). by apply: sum_difunctional.

  (* TyArrow *)
  elim: EF => [EF1 EF2].
  specialize (IHt1 rho EF1). specialize (IHt2 rho EF2). by apply: arrow_difunctional. 

  (* TyBase *)
  apply: DIF. 

  (* For all *)
  intros x x' y y' xy x'y' xy' k.
  assert (xy0 := xy k).
  assert (x'y'0 := x'y' k).
  assert (xy'0 := xy' k).
  by apply (IHt (k,rho) EF x x' y y' xy0 x'y'0 xy'0). 

  (* Exists *)
  (* We don't have a nice property regarding composition, can't do existentials *)
  done.   
Qed. 

Lemma EcS_consSub A (ME: ModelEnv A) D D' s (e: Exp D' s) (S: Sub D D') (rho: RelEnv ME D') :
  EcS rho (consSub e S) = (interpExp e rho, EcS rho S). 
Proof. done. Qed.

Lemma RelEnv_extensional A (ME: ModelEnv A) D (rho rho': RelEnv ME D) :
  (forall s (v: Var D s), lookup v rho = lookup v rho') -> rho = rho'.
Proof. apply envExtensional. Qed. 

Lemma interpShVar A (ME: ModelEnv A) D (rho: RelEnv ME D) s' k :
  (forall s (v:Var D s), interpExp (shExp s' v) (k, rho) = interpExp v rho).
Proof. dependent induction v => //. 
by rewrite /= !apRenVarShift apRenVarId. 
Qed. 

Lemma interpShExpAndSeq A (ME: ModelEnv A) D (rho: RelEnv ME D) s' k :
  (forall s (e:Exp D s), interpExp (shExp s' e) (k, rho) = interpExp e rho) /\
  (forall ss (es:Exps D ss), interpExps (shExpSeq s' es) (k, rho) = interpExps es rho).
Proof. apply Exp_Exps_ind => //. 
+ by apply interpShVar.  
+ move => op e IH. by rewrite /= IH.  
+ move => s ss e IH1 es IH2. by rewrite /= IH1 IH2. 
Qed. 

Lemma interpApSubExpAndSeq A (ME: ModelEnv A) D D' (rho: RelEnv ME D') (S: Sub D D') :
  (forall s (e:Exp D s), interpExp (apSub S e) rho = interpExp e (EcS rho S)) /\
  (forall ss (es:Exps D ss), interpExps (apSubSeq S es) rho = interpExps es (EcS rho S)).
Proof. apply Exp_Exps_ind => //. 
+ dependent induction v => //. by rewrite /= IHv. 
+ move => op e IH. by rewrite /= IH.  
+ move => s ss e IH1 es IH2. by rewrite /= IH1 IH2. 
Qed. 


Lemma EcS_shift A (ME: ModelEnv A) D : forall D' s (k:interpSrt (sig:=sig) ME s) (S:Sub D D') (rho: RelEnv ME D'), EcS ((k,rho):RelEnv ME (s::D')) (shiftSub s S) = EcS rho S.
Proof.
induction D => //. 
move => D' s k [e S] rho. rewrite /EcS.  rewrite /EcS in IHD. by rewrite /= IHD (proj1 (interpShExpAndSeq _ _)). 
Qed. 

Lemma EcS_lift A (ME:ModelEnv A) D D' s (k:interpSrt (sig:=sig) ME s) (S:Sub D D') (rho: RelEnv ME D') :
  EcS ((k,rho):RelEnv ME (s::D')) (liftSub s S) = (k, EcS rho S). 
Proof. by rewrite EcS_consSub/= EcS_shift. Qed.

Lemma EcS_id A (ME: ModelEnv A) D (rho: RelEnv ME D) : EcS rho (idSub D) = rho. 
Proof. induction D => //. by destruct rho. 
destruct rho as [g rho]. rewrite EcS_consSub. by rewrite EcS_shift IHD. Qed. 


Lemma EcS_pi A (ME: ModelEnv A) D s k rho :
  EcS ((k, rho):RelEnv ME (s::D)) (pi D s) = rho. 
Proof. by rewrite /pi EcS_shift EcS_id. Qed. 


(* This is lemma 2, part 2 *)
Lemma semSubst A (ME:ModelEnv A) D (t: Ty D) : 
  forall D' (S:Sub D D') (rho: RelEnv ME D') v v',
  semTy A rho (apSubTy S t) (up S v) (up S v')
  <->
  semTy A (EcS rho S) t v v'.
Proof. induction t => /= D' S rho v v'.

(* TyUnit *)
by reflexivity. 

(* TyProd *)
by rewrite -(IHt1 _ S rho) -(IHt2 _ S rho) 2!upFst 2!upSnd. 

(* TySum *)
specialize (IHt1 D' S rho). specialize (IHt2 D' S rho). 
set x := up S _. simpl in x.
case E: x => [x1 | x2]. 
* set x' := up S _. simpl in x'. 
  case E': x' => [x'1 | x'2].
  + case E'': v => [v1 | v2]. 
    - rewrite /x E'' upInl in E. inversion E. clear E. 
      case E''': v' => [v1' | v2']. 
        rewrite -IHt1.
        rewrite /x' E''' upInl in E'. inversion E'. clear E'. 
        by rewrite H0 H1.
        rewrite /x' E''' upInr in E'. inversion E'. 
    - rewrite /x E'' upInr in E. inversion E.
  + case E'': v => [v1 | v2].  
    - rewrite /x E'' upInl in E. inversion E. clear E. 
      case E''': v' => [v1' | v2']. 
      rewrite -IHt1. 
      rewrite /x' E''' upInl in E'. inversion E'. 
      done. 
    - rewrite /x E'' upInr in E. inversion E. 
* set x' := up S _. simpl in x'. 
  case E': x' => [x'1 | x'2].
  + case E'': v => [v1 | v2]. 
    - rewrite /x E'' upInl in E. inversion E. 
    - rewrite /x E'' upInr in E. inversion E. clear E. 
      case E''': v' => [v1' | v2']. 
        done.         
        rewrite -IHt2.
        rewrite /x' E''' upInr in E'. inversion E'. 
  + case E'': v => [v1 | v2]. 
    - rewrite /x E'' upInl in E. inversion E. 
    - rewrite /x E'' upInr in E. inversion E. clear E. rewrite H0. 
      case E''': v' => [v1' | v2']. 
      rewrite /x' E''' upInl in E'. inversion E'. 
      rewrite /x' E''' upInr in E'. inversion E'. clear E'. 
      rewrite -IHt2. by rewrite H0 H1. 

(* TyArr *)
specialize (IHt1 D' S rho). 
specialize (IHt2 D' S rho). 
split. 
+ move => HH x x' xx'. destruct (IHt1 x x') as [_ IHb]. 
  specialize (IHb xx'). 
  specialize (HH _ _ IHb). 
  rewrite -2!upApp in HH.   
  by rewrite ->IHt2 in HH. 
+ move => HH x x' xx'. 
  destruct (IHt1 (dn x) (dn x')) as [IHa _]. 
  rewrite !updn in IHa. 
  specialize (IHa xx'). 
  specialize (HH _ _ IHa). 
  destruct (IHt2 (v (dn x)) (v' (dn x'))) as [_ IHd]. 
  specialize (IHd HH). by rewrite !upApp!updn in IHd. 

(* TyPrim *)
rewrite/up/=.
rewrite cast_UIP cast_id cast_UIP cast_id. 
by rewrite (proj2 (interpApSubExpAndSeq _ _)). 

(* TyAll *)
specialize (IHt _ (liftSub _ S)).
split => HH k.
+ destruct (IHt (k,rho) v v') as [IH1 _].
  rewrite -!upSpec in IH1. 
  specialize (HH k). 
  specialize (IH1 HH). by rewrite EcS_lift in IH1.  

  (* This time we need first closure property of environments,
     together with simple properties of pi and lifting *)
+ specialize (IHt (k,rho) v v'). 
  rewrite -!upSpec in IHt. apply IHt. rewrite EcS_lift. apply HH. 

(* TyExists *)
split. 
+ move => [k H]. exists k. 
  specialize (IHt _ (liftSub s S) (k,rho) v v'). rewrite EcS_lift in IHt. 
  apply IHt. 
  rewrite -2!upInst. apply H. 

+ move => [k H]. exists k. 
  specialize (IHt _ (liftSub s S) (k,rho) v v'). 
  rewrite 2!upInst. 
  rewrite IHt {IHt}.
  by rewrite EcS_lift. 
Qed.

Lemma AbstractionVar A (ME: ModelEnv A) D (G: Ctxt D) (t: Ty D) (v: TmVar G t) (rho: RelEnv ME D) eta1 eta2:
  semCtxt rho eta1 eta2 -> semTy A rho t (interpTmVar v eta1) (interpTmVar v eta2). 
Proof. induction v => /= H. 
+ apply H. + apply IHv. apply H. 
Qed. 

Lemma castConsCtxt D D' (t: Ty D) (G: Ctxt D) (S: Sub D D') (v:|t|) (eta: interpCtxt G) : 
  ((v, eta) :? (interpSubCtxt (t :: G) S)) = 
  (v :? interpSubst t S, eta :? interpSubCtxt G S). 
Proof.
apply (cast_pair (interpSubst t S) (interpSubCtxt G S)).
Qed.


(* This is lemma 4 *)
Lemma semSubstCtxt A (ME: ModelEnv A) D (G: Ctxt D) : 
  forall D' (S:Sub D D') rho eta eta',
  semCtxt (rho: RelEnv ME D') (eta :? interpSubCtxt G S) (eta' :? interpSubCtxt G S)
  <->
  semCtxt (EcS rho S) eta eta'.  
Proof. induction G => //.  
move => D' S rho [v eta] [v' eta']. 
fold interpCtxt in *.
specialize (IHG _ S rho eta eta').
simpl semCtxt.  
rewrite -IHG. 
rewrite !castConsCtxt. simpl. split. 
move => [H1 H2]. 
split => //. 
apply semSubst => //. intuition.
apply semSubst => //. 
Qed.  

(* Theorem 1 *)
Theorem Abstraction A (ME: ModelEnv A) D (G: Ctxt D) (t: Ty D) (M: Tm A G t) (rho: RelEnv ME D) eta1 eta2:
  semCtxt rho eta1 eta2 -> semTy A rho t (interpTm M eta1) (interpTm M eta2). 
Proof. induction M => /= H. 
(* VAR *)
apply AbstractionVar => //. 
(* TYEQ *)
apply semEquiv => //. apply IHM => //.  
(* UNIT *)
done. 
(* PAIR *)
split; [apply IHM1 => // | apply IHM2 => //].
(* PROJ1 *)
apply IHM => //.
(* PROJ2 *)
apply IHM => //. 
(* INL *)
apply IHM => //. 
(* INR *)
apply IHM => //. 
(* CASE *)
simpl in IHM1.
specialize (IHM1 rho eta1 eta2 H). 
case E1: (interpTm M1 eta1) => [a | a]. 
case E2: (interpTm M1 eta2) => [b | b]. 
+ rewrite E1 E2 in IHM1. by apply IHM2 => //. 
+ by rewrite E1 E2 in IHM1. 
case E2: (interpTm M1 eta2) => [b | b]. 
+ by rewrite E1 E2 in IHM1. 
+ rewrite E1 E2 in IHM1. by apply IHM3 => //. 
(* ABS *)
move => x x' xx'. apply IHM => //.   
(* APP *)
apply IHM1 => //. apply IHM2 => //. 
(* UNIVABS *)
move => k.
apply IHM => //. 
apply semSubstCtxt => //. by rewrite EcS_pi. 
(* UNIVAPP *)
specialize (IHM rho _ _ H). simpl in IHM. specialize (IHM (interpExp e rho)).
have SS := proj2 (semSubst (ME:=ME) (consSub e (idSub D)) rho _ _). 
rewrite EcS_consSub EcS_id in SS. 
apply: semTyCast (SS _ _ _ IHM). 
(* EXPACK *)
exists (interpExp e rho). 
have SS := proj1 (semSubst (ME:=ME) (consSub e (idSub D)) rho _ _).  
rewrite EcS_consSub EcS_id in SS.
apply SS. rewrite /up !cast_coalesce !cast_id.
apply IHM => //. 
(* EXUNPACK *)
specialize (IHM1 rho eta1 eta2 H). simpl in IHM1. 
destruct IHM1 as [k IHM1]. 
simpl in IHM2.  
specialize (IHM2 (k,rho) (interpTm M1 eta1, eta1 :? interpSubCtxt G (pi D s))
                      (interpTm M1 eta2, eta2 :? interpSubCtxt G (pi D s))). 
simpl in IHM2. 
have H2: semCtxt ((k,rho):RelEnv ME (s::D)) (eta1 :? interpSubCtxt G (pi D s)) (eta2 :? interpSubCtxt G (pi D s)).
apply semSubstCtxt => //. 
by rewrite EcS_pi. 
rewrite !cast_id. specialize (IHM2 (conj IHM1 H2)). 
have SS := (semSubst (pi D s) (k,rho)). rewrite /up in SS. 
rewrite EcS_pi in SS. apply SS. rewrite !cast_coalesce !cast_id. apply IHM2. 
Qed. 


End Sem.



