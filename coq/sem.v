Require Import ssreflect ssrbool ssrfun seq.
Require Import Relations Program.Equality.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import syn Casts.

(*---------------------------------------------------------------------------
   Semantics
   ---------------------------------------------------------------------------*)
Section Sem.

Structure SEM (sig: SIG) := mkSEM {
  (* Underlying interpretation of primitive type constructors *)
  interpPrim : PrimType sig -> Type
}.

Variable sig: SIG.
Variable sem: SEM sig.

Reserved Notation "| t |" (at level 60).

(* Index-erasure interpretation of types *)
Fixpoint interpTy D (t: Ty D) : Type :=
  match t with
  | TyUnit       => unit
  | TyProd t1 t2 => |t1| * |t2|
  | TySum  t1 t2 => |t1| + |t2|
  | TyArr  t1 t2 => |t1| -> |t2|
  | TyAll    _ t => |t| 
  | TyExists _ t => |t|
  | TyPrim   p _ => interpPrim sem p
  end%type
where "| t |" := (interpTy t).

(* Relation environments *)
Definition RelEnv D := 
  forall p, Sub (tyArity p) D -> relation (interpPrim sem p).

(* Compose environment with substitution *)
Definition EcS D D' (rho: RelEnv D') (S: Sub D D') : RelEnv D
:= fun p S' => rho p (ScS S S').

(* This is \cal E from Section 4.2.2 *)
Definition RelEnvSet := forall D, RelEnv D -> Prop.

(* These are the two conditions on sets of environments specified in 4.2.2 *)
Definition ClosedRelEnvs (E:RelEnvSet) :=
  forall D D' (S: Sub D' D) rho, E D rho -> E D' (EcS rho S)
/\
  forall D D' s (S: Sub D' D) rho1 rho2, 
  E (s::D') rho1 -> E D rho2 ->
  EcS rho1 (pi _ s) = EcS rho2 S ->
  exists rho, E (s::D) rho /\
  EcS rho (liftSub s S) = rho1 /\
  EcS rho (pi _ s) = rho2.

Variable ES: RelEnvSet. 
Variable C: ClosedRelEnvs ES. 

Definition ext D (rho: RelEnv D) (s: Srt sig) (rho': RelEnv (s::D)) :=
  ES rho' -> EcS rho' (pi _ s) = rho.

Implicit Arguments ext [D].

Fixpoint semTy D (rho: RelEnv D) (t:Ty D) : relation (|t|) :=
  match t with
  | TyUnit => fun x y => True
  | TyProd t1 t2 => fun x y => semTy rho x.1 y.1 /\ semTy rho x.2 y.2
  | TySum t1 t2 => fun x y => 
    match x, y with inl x1, inl y1 => semTy rho x1 y1
                  | inr x2, inr y2 => semTy rho x2 y2
                  | _, _ => False 
    end
  | TyArr t1 t2 => fun x y => forall x' y', semTy rho x' y' -> semTy rho (x x') (y y')
  | TyPrim p ixs => rho p (expsAsSub ixs)
  | TyAll s t => fun x y => forall rho', ext rho s rho' -> semTy rho' x y
  | TyExists s t => fun x y => exists rho', ext rho s rho' -> semTy rho' x y
  end.

Notation "r '|=' x '===' y : t" := (semTy (t:=t) r x y)  (at level 80, x, y at next level).

(* This is lemma 3, part 1 *)
Lemma interpEquiv D (t1 t2: Ty D) A : equivTy A t1 t2 -> |t1| = |t2|.
Proof. move => E. induction E => /=//; congruence. Qed. 

(* This is lemma 3, part 2 *)
Lemma interpSubst D (t: Ty D) : forall D' (S: Sub D D'), |t| = |apSubTy S t|.
Proof. induction t => /=//; congruence. Qed.


(*---------------------------------------------------------------------------
   Unfortunately we need casts just to state the semSubst lemma. 
   "up" sends a value from |t| to |apSubTy S t|
   "dn" sends a value from |apSubTy S t| to |t|
   We have various lemmas connecting these.
   ---------------------------------------------------------------------------*)
Section UpDn. 

  Variables D D' : Ctxt sig.
  Variables S : Sub D D'.
  Variables t t1 t2 : Ty D.

  Definition up t x := x :? interpSubst t S.
  Definition dn t x := x :? sym_equal (interpSubst t S).

  Lemma dnup (x: |t|) : dn (up x) = x.
  Proof. by rewrite /up/dn cast_coalesce cast_id. Qed. 

  Lemma updn (x: |apSubTy S t|) : up (dn x) = x.
  Proof. by rewrite /up/dn cast_coalesce cast_id. Qed. 
End UpDn.

Section UpDnProps.

  Variables D D' : Ctxt sig.
  Variables S : Sub D D'.
  Variables t t1 t2 : Ty D.

  Lemma upApp (f: |TyArr t1 t2|) (x: |t1|) : up S (f x) = (up _ f) (up S x). 
  Proof. rewrite /up. rewrite (cast_app (interpSubst t1 S) (interpSubst t2 S)).
  set F1 := f :? arrow_eq _ _. simpl in F1. 
  set F2 := f :? interpSubst _ _. simpl (id _) in F2. 
  have: F1 = F2 by apply cast_UIP. by move ->. 
  Qed. 

  Lemma upFst (p: |TyProd t1 t2|) : (up _ p).1 = (up S p.1).
  Proof. 
  rewrite /up -(cast_fst (interpSubst t1 S) (interpSubst t2 S)). 
  set H := interpSubst _ _. 
  set H':= prod_eq _ _. simpl interpTy in H. by rewrite cast_UIP. 
  Qed. 

  Lemma upSnd (p: |TyProd t1 t2|) : (up _ p).2 = (up S p.2).
  Proof. 
  rewrite /up -(cast_snd (interpSubst t1 S) (interpSubst t2 S)). 
  set H := interpSubst _ _. 
  set H':= prod_eq _ _. simpl interpTy in H. by rewrite cast_UIP. 
  Qed. 

  Lemma upInl (x: |t1|) : up (t:=TySum t1 t2) S (inl _ x) = inl _ (up (t:=t1) S x).
  Proof.  
  rewrite /up -(cast_inl (interpSubst t1 S) (interpSubst t2 S)). 
  set H := interpSubst _ _. 
  set H' := sum_eq _ _. simpl interpTy in H. by rewrite cast_UIP. 
  Qed. 

  Lemma upInr (x: |t2|) : up (t:=TySum t1 t2) S (inr _ x) = inr _ (up (t:=t2) S x).
  Proof.  
  rewrite /up -(cast_inr (interpSubst t1 S) (interpSubst t2 S)). 
  set H := interpSubst _ _. 
  set H' := sum_eq _ _. simpl interpTy in H. by rewrite cast_UIP. 
  Qed. 

(*
  Lemma upSpec : forall (Z:Ty (S m)), forall x : usem (All Z), up (X:=All Z) x = up (s := liftSubst s) (X:=Z) x.
  intros.
  apply cast_UIP.
  Qed.
*)

End UpDnProps.

(* This is lemma 4, part 2 *)
Lemma semSubst D (t: Ty D) : forall D' (S:Sub D D') rho v v', 
  rho |= up S v === up S v' : apSubTy S t 
  <->
  EcS rho S |= v === v' : t.
Proof. induction t => /= D' S rho v v'.

(* TyUnit *)
by reflexivity. 

(* TyProd *)
by rewrite -IHt1 -IHt2 2!upFst 2!upSnd. 

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
split. 
+ move => H rho' EXT. 
  rewrite /ext in EXT. 

admit. 
+ move => H rho' EXT. admit. 

(* TyExists *)
split. 
+ move => H. admit. 
+ move => H. admit. 
Qed. 


End Sem.


