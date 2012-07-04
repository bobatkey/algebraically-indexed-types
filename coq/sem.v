Require Import ssreflect ssrbool ssrfun seq.
Require Import Relations Program.Equality.
Require Import FunctionalExtensionality. 
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import syn Casts.

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

Fixpoint interpCtxt D (G: Ctxt D) : Type :=
  if G is t::G then (interpTy t * interpCtxt G)%type else unit.

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
induction G. done. move => D' S. simpl. by rewrite (interpSubst t S) (IHG _ S). 
Qed. 

Fixpoint interpVar D (G: Ctxt D) (t: Ty D) (v: TmVar G t) : interpCtxt G -> (|t|) :=
  match v with
  | TmVarZ _ _ => fun eta => eta.1
  | TmVarS _ _ _ v => fun eta => interpVar v eta.2
  end.

Variable A: seq (Ax sig). 

Fixpoint interpTm D (G: Ctxt D) (t: Ty D) (M: Tm A G t) : interpCtxt G -> (|t|) :=
  match M in Tm _ _ t return interpCtxt G -> |t| with
  | VAR _ v       => fun eta => interpVar v eta
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

(* Relation environments *)
Definition RelEnv D := 
  forall p, Sub (tyArity p) D -> relation (interpPrim p).

Require Import Rel.
Definition invEnv D (R: RelEnv D) : RelEnv D := fun p ixs => fun x y => R p ixs y x.
Definition composeEnv D (R1 R2: RelEnv D) : RelEnv D := 
  fun p ixs => RelComp (R1 p ixs) (R2 p ixs).


(* Relation environments that respect equivalence for a set of axioms A *)
Definition GoodRelEnv D A (rho: RelEnv D) :=
  forall p ixs ixs', equivSeq A ixs ixs' -> rho p (expsAsSub ixs) = rho p (expsAsSub ixs'). 

(* Compose environment with substitution *)
Definition EcS D D' (rho: RelEnv D') (S: Sub D D') : RelEnv D
:= fun p S' => rho p (ScS S S').

(* rho' extends rho on a variable of sort s *)
Definition ext D (rho: RelEnv D) s (rho': RelEnv (s::D)) := EcS rho' (pi _ s) = rho.
Notation "rho' >> rho" := (ext rho rho') (at level 70). 

(* This is \cal E from Section 4.2.2 *)
Definition RelEnvSet := forall D, RelEnv D -> Prop.

Notation "'forall:' x 'in' S ',' P" := (forall x, S x -> P) 
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists:' x 'in' S ',' P" := (exists x, S x /\ P) 
  (at level 200, x ident, right associativity) : type_scope.


(* These are the two conditions on sets of environments specified in 4.2.2 *)
(* We also include the condition that environments respect equivalence *)
Structure ClosedRelEnvSet A (E:RelEnvSet) := {
  goodEnvs : forall D rho, E D rho -> GoodRelEnv A rho;
  closedWrtSubst : forall D D' (S: Sub D' D) rho, E D rho -> E D' (EcS rho S);
  closedWrtInv : forall D rho, E D rho -> E D (invEnv rho);
  closedWrtCompose : forall D rho1 rho2, E D rho1 -> E D rho2 -> E D (composeEnv rho1 rho2);
  closedWrtLift : forall D D' s (S: Sub D' D), 
  forall: rho1 in E (s::D'),
  forall: rho2 in E D,
  rho1 >> EcS rho2 S ->
  exists: rho in E (s::D), 
  EcS rho (liftSub s S) = rho1 /\
  rho >> rho2
}.

Variable ES: RelEnvSet. 

Fixpoint semTy D (rho: RelEnv D) (t:Ty D) : relation (|t|) :=
  match t return relation (|t|) with
  | TyUnit       => fun x y => True
  | TyProd t1 t2 => fun x y => semTy rho x.1 y.1 /\ semTy rho x.2 y.2
  | TySum t1 t2  => fun x y => 
    match x, y with inl x1, inl y1 => semTy rho x1 y1
                  | inr x2, inr y2 => semTy rho x2 y2
                  | _, _ => False 
    end
  | TyArr t1 t2  => fun x y => forall x' y', semTy rho x' y' -> semTy rho (x x') (y y')
  | TyPrim p ixs => rho p (expsAsSub ixs)
  | TyAll    s t => fun x y => forall rho', ES rho' -> rho' >> rho -> semTy rho' x y
  | TyExists s t => fun x y => exists rho', ES rho' /\ rho' >> rho /\ semTy rho' x y
  end.

Notation "rho |= x == y :> t" := (semTy (t:=t) rho x y) (at level 67, x at level 67, y at level 67).


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
  Proof. rewrite /up. rewrite (cast_app (interpSubst t1 S) (interpSubst t2 S)).
  set F1 := f :? arrow_eq _ _. simpl in F1. 
  set F2 := f :? _. simpl (id _) in F2. 
  have: F1 = F2 by apply cast_UIP. by move ->. 
  Qed. 

  Lemma upFst (p: |TyProd t1 t2|) : (up _ p).1 = (up S p.1).
  Proof. 
  rewrite /up -(cast_fst (interpSubst t1 S) (interpSubst t2 S)). 
  set H':= prod_eq _ _. by rewrite cast_UIP. 
  Qed. 

  Lemma upSnd (p: |TyProd t1 t2|) : (up _ p).2 = (up S p.2).
  Proof. 
  rewrite /up -(cast_snd (interpSubst t1 S) (interpSubst t2 S)). 
  set H':= prod_eq _ _. by rewrite cast_UIP. 
  Qed. 

  Lemma upInl (x: |t1|) : up (t:=TySum t1 t2) S (inl _ x) = inl _ (up (t:=t1) S x).
  Proof.  
  rewrite /up -(cast_inl (interpSubst t1 S) (interpSubst t2 S)). 
  set H' := sum_eq _ _. by rewrite cast_UIP. 
  Qed. 

  Lemma upInr (x: |t2|) : up (t:=TySum t1 t2) S (inr _ x) = inr _ (up (t:=t2) S x).
  Proof.  
  rewrite /up -(cast_inr (interpSubst t1 S) (interpSubst t2 S)). 
  set H' := sum_eq _ _. by rewrite cast_UIP. 
  Qed. 

  Lemma upSpec s (ty: Ty (s::D)) (x: | TyAll ty|): up S x = up (liftSub _ S) x.
  Proof. rewrite /up. by apply cast_UIP. Qed. 

  Lemma upInst s (ty: Ty (s::D)) (x: | TyExists ty|): up S x = up (liftSub _ S) x.
  Proof. rewrite /up. by apply cast_UIP. Qed. 

End UpDnProps.


Lemma invEnvK D (R: RelEnv D) : invEnv (invEnv R) = R. 
Proof. 
apply functional_extensionality_dep => p.  
apply functional_extensionality => z.
apply functional_extensionality => z'. 
by apply functional_extensionality. 
Qed. 

Lemma invExt s D (rho': RelEnv (s::D)) (rho: RelEnv D) :
  rho' >> invEnv rho -> invEnv rho' >> rho. 
Proof. rewrite /ext. move => H.  
apply functional_extensionality_dep => p. 
apply functional_extensionality => S. 
apply functional_extensionality => z. 
apply functional_extensionality => z'.
have H': EcS rho' (pi D s) S z' z = invEnv rho S z' z. by rewrite H. 
rewrite /invEnv in H'. by rewrite -H'. 
Qed. 

Variable CLOSED: ClosedRelEnvSet A ES. 


Lemma semInv : forall D (t : Ty D) rho x x', semTy (t:=t) rho x x' -> semTy (t:=t) (invEnv rho) x' x. 
Proof.
  induction t => /= rho x x' xx'. 
  (* TyUnit *)
  done. 

  (* TyProd *)
  split; firstorder. 

  (* TySum *)
  destruct x'; destruct x; firstorder. 

  (* TyArr *)
  move => y y' yy'. specialize (IHt1 _ _ _ yy'). 
  rewrite invEnvK in IHt1. specialize (xx' _ _ IHt1). 
  by apply (IHt2 _ _ _ xx'). 

  (* TyPrim *)
  rewrite /invEnv. apply xx'. 
  
  (* TyAll *)  
  move => rho' ESrho' EXT. 
  specialize (IHt (invEnv rho') x x'). rewrite invEnvK in IHt. apply IHt.
  apply xx'. by apply (closedWrtInv CLOSED). by apply: invExt EXT. 

  (* TyExists *)
  destruct xx' as [rho' [ESrho' [EXT H]]]. 
  exists (invEnv rho'). split. by apply (closedWrtInv CLOSED). 
  split. apply invExt. rewrite invEnvK. apply EXT. apply IHt. apply H. 
Qed. 



(* This is lemma 4, part 1 *)
Lemma semEquiv D (t1 t2: Ty D) (E: equivTy A t1 t2) : forall (rho: RelEnv D) (v v':interpTy t1),
  semTy rho v v' <->
  semTy rho (rt E v) (rt E v'). 
Proof. 
(* Not sure why this needs generalizing. But the induction won't go through otherwise. *)
rewrite /rt. move: (interpEquiv E).
induction E => pf rho v v'.
(* EquivTyRefl *)
by rewrite 2!cast_id. 
(* EquivTySym *)
admit. 
(* EquivTyTrans *)
admit. 
(* EquivTyProd *)
Admitted.


Lemma sem_difunctional : 
  (forall D (psi: RelEnv D) p exps, difunctional (psi p exps)) ->
  forall D (t: Ty D) (psi: RelEnv D), difunctional (semTy (t:=t) psi).
Proof.
  move => DIF. 
  induction t => /= rho. 
  
  (* TyUnit *)
  by intuition. 

  (* TyProd *)
  specialize (IHt1 rho). specialize (IHt2 rho). by apply: prod_difunctional.  

  (* TySum *)
  specialize (IHt1 rho). specialize (IHt2 rho). by apply: sum_difunctional.

  (* TyArrow *)
  specialize (IHt1 rho). specialize (IHt2 rho). by apply: arrow_difunctional. 

  (* TyBase *)
  apply DIF.     

  (* For all *)
  intros x x' y y' xy x'y' xy'.
  intros psi' ESpsi' ext.
  assert (xy0 := xy psi' ESpsi' ext).
  assert (x'y'0 := x'y' psi' ESpsi' ext).
  assert (xy'0 := xy' psi' ESpsi' ext).
  by apply (IHt psi' x x' y y' xy0 x'y'0 xy'0). 

  (* Exists *)
  rewrite /difunctional. 
  intros x x' y y' xy x'y' xy'.
  destruct xy as [rho0 [ESrho0 [EXTrho0 H0]]].
  destruct x'y' as [rho1 [ESrho1 [EXTrho1 H1]]].  
  destruct xy' as [rho2 [ESrho2 [EXTrho2 H2]]].  
  (* Could we do this? *)
  set rho' := composeEnv rho1 (composeEnv (invEnv rho2) rho0).
  exists rho'.   

  (* Answer: no, we don't have a nice property regarding composition *)
  admit. 
Qed. 

  
(* This is lemma 4, part 2 *)
Lemma semSubst D (t: Ty D) : forall D' (S:Sub D D') rho (ESrho: ES rho) v v',
  (rho |= up S v == up S v' :> apSubTy S t
  <->
  EcS rho S |= v == v' :> t).  
Proof. induction t => /= D' S rho ESrho v v'.

(* TyUnit *)
by reflexivity. 

(* TyProd *)
by rewrite -(IHt1 _ S rho ESrho) -(IHt2 _ S rho ESrho) 2!upFst 2!upSnd. 

(* TySum *)
specialize (IHt1 D' S rho ESrho). specialize (IHt2 D' S rho ESrho). 
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
specialize (IHt1 D' S rho ESrho). 
specialize (IHt2 D' S rho ESrho). 
split. 
+ move => H x x' xx'. destruct (IHt1 x x') as [_ IHb]. 
  specialize (IHb xx'). 
  specialize (H _ _ IHb). 
  rewrite -2!upApp in H.   
  by rewrite ->IHt2 in H. 
+ move => H x x' xx'. 
  destruct (IHt1 (dn x) (dn x')) as [IHa _]. 
  rewrite !updn in IHa. 
  specialize (IHa xx'). 
  specialize (H _ _ IHa). 
  destruct (IHt2 (v (dn x)) (v' (dn x'))) as [_ IHd]. 
  specialize (IHd H). by rewrite !upApp!updn in IHd. 

(* TyPrim *)
rewrite /EcS/up/=.
rewrite ScExpsAsSub. by rewrite cast_UIP cast_id cast_UIP cast_id. 

(* TyAll *)
specialize (IHt _ (liftSub _ S)).
split => H rho' ESrho' EXT. 
  (* For this case we need second closure property of environments *)
+ have CL2 := closedWrtLift CLOSED ESrho' ESrho EXT. 
  destruct CL2 as [rho0 [H2 [H3 H4]]]. 
  destruct (IHt rho0 H2 v v') as [IH1 _].
  rewrite -!upSpec in IH1. 
  specialize (H _ H2 H4). 
  rewrite H3 in IH1. apply IH1. 
  by apply H. 

  (* This time we need first closure property of environments,
     together with simple properties of pi and lifting *)
+ specialize (IHt rho' ESrho' v v'). 
  rewrite -!upSpec in IHt. apply IHt. apply H. 
  apply (closedWrtSubst CLOSED (liftSub s S) ESrho').    
  rewrite /ext in EXT. rewrite -EXT.  
  apply functional_extensionality_dep => p. 
  apply functional_extensionality => S'.
  rewrite /EcS 2!ScS_assoc. 
  by rewrite liftPi.  

(* TyExists *)
split => [[rho' [H1 [H2 H3]]] | [rho1 [H1 [H2 H3]]]]. 
+ exists (EcS rho' (liftSub _ S)).
  split. by apply (closedWrtSubst CLOSED). 
  split. rewrite /ext. rewrite -H2. 
  apply functional_extensionality_dep => p. 
  apply functional_extensionality => S'. 
  rewrite /EcS 2!ScS_assoc.
  by rewrite liftPi.

  specialize (IHt _ (liftSub s S) rho' H1 v v'). rewrite -IHt.
  rewrite -2!upInst. apply H3. 

+ have CL1 := closedWrtLift CLOSED.   
  specialize (CL1 _ _ s S rho1 H1 _ ESrho H2). 
  destruct CL1 as [rho0 [H4 [H5 H6]]]. 
  exists rho0.  
  split => //. 
  split => //. 
  specialize (IHt _ (liftSub s S) _ H4 v v'). 
  rewrite 2!upInst. 
  rewrite IHt {IHt}.
  rewrite H5. apply H3. 
Qed.

End Sem.