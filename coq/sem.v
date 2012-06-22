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

(* This is lemma 3, part 1 *)
Lemma interpEquiv D (t1 t2: Ty D) A : equivTy A t1 t2 -> |t1| = |t2|.
Proof. move => E. induction E => /=//; congruence. Qed. 

(* This is lemma 3, part 2 *)
Lemma interpSubst D (t: Ty D) : forall D' (S: Sub D D'), |t| = |apSubTy S t|.
Proof. induction t => /=//; congruence. Qed.

(*---------------------------------------------------------------------------
   Relational semantics
   ---------------------------------------------------------------------------*)

(* Relation environments *)
Definition RelEnv D := 
  forall p, Sub (tyArity p) D -> relation (interpPrim p).

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

(* These are the two conditions on sets of environments specified in 4.2.2 *)
(* We also include the condition that environments respect equivalence *)
Structure ClosedRelEnvSet A (E:RelEnvSet) := {
  goodEnvs : forall D rho, E D rho -> GoodRelEnv A rho;
  closedWrtSubst : forall D D' (S: Sub D' D) rho, E D rho -> E D' (EcS rho S);
  closedWrtLift : forall D D' s (S: Sub D' D) rho1 rho2, 
  E (s::D') rho1 -> 
  E D rho2 ->
  rho1 >> EcS rho2 S ->
  exists rho, 
  E (s::D) rho /\
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
  | TyExists s t => fun x y => exists rho', ES rho' -> rho' >> rho -> semTy rho' x y
  end.

Notation "rho |= x == y :> t" := (semTy (t:=t) rho x y) (at level 67, x at level 67, y at level 67).

Variable A: seq (Ax sig). 

(*---------------------------------------------------------------------------
   Unfortunately we need casts just to state the semSubst and semEquiv lemmas. 
   "up" sends a value from |t| to |apSubTy S t|
   "dn" sends a value from |apSubTy S t| to |t|
   We have various lemmas connecting these.
   ---------------------------------------------------------------------------*)
Section UpDn. 

  Variables D D' : Ctxt sig.
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

  Variables D D' : Ctxt sig.
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

End UpDnProps.


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

Variable CLOSED: ClosedRelEnvSet A ES. 


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
have SS:= (apScS S (expsAsSub ixs)). 
admit. 

(* TyAll *)
specialize (IHt _ (liftSub _ S)).
split => H rho' ESrho' EXT. 
  (* For this case we need second closure property of environments *)
+ have CL2 := closedWrtLift CLOSED. 
  specialize (CL2 _ _ s S rho' rho ESrho' ESrho EXT). 
  destruct CL2 as [rho0 [H2 [H3 H4]]]. 
  specialize (IHt rho0 H2 v v').
  rewrite -!upSpec in IHt. 
  specialize (H _ H2 H4). 
  destruct IHt as [IH1 IH2].   
  rewrite H3 in IH1. apply IH1. 
  by apply H. 

  (* This time we need first closure property of environments,
     together with simple properties of pi and lifting *)
+ specialize (IHt rho' ESrho' v v'). 
  rewrite -!upSpec in IHt. apply IHt. apply H. 
  have CL1 := closedWrtSubst CLOSED. 
  apply (CL1 _ _ (liftSub s S) rho' ESrho').
  rewrite /ext. rewrite /ext in EXT. rewrite -EXT.  
  apply functional_extensionality_dep => p. 
  apply functional_extensionality => S'.
  rewrite /EcS 2!ScS_assoc. 
  by rewrite liftPi.  

(* TyExists *)
specialize (IHt _ (liftSub _ S)).
split => H. 
+ destruct H as [rho' H'].  
admit.
admit. 
Qed.

End Sem.