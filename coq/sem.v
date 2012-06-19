Require Import ssreflect ssrbool ssrfun seq.
Require Import Relations Program.Equality.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import syn.

(*---------------------------------------------------------------------------
   Semantics
   ---------------------------------------------------------------------------*)

Structure SEM (sig: SIG) := mkSEM {
  (* Underlying interpretation of primitive type constructors *)
  interpPrim : PrimType sig -> Type
}.

Section USem.

Variable sig: SIG.
Variable sem: SEM sig.

(* Index-erasure interpretation of types *)
Fixpoint interpTy D (t: Ty D) : Type :=
  match t with
  | TyUnit       => unit
  | TyProd t1 t2 => (interpTy t1 * interpTy t2)%type
  | TySum  t1 t2 => (interpTy t1 + interpTy t2)%type
  | TyArr  t1 t2 => interpTy t1 -> interpTy t2
  | TyAll    _ t => interpTy t
  | TyExists _ t => interpTy t
  | TyPrim   p _ => interpPrim sem p
  end.

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

Fixpoint semTy D (rho: RelEnv D) (t:Ty D) : relation (interpTy t) :=
  match t return relation (interpTy t) with
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

Lemma interpSubst D (t: Ty D) : 
  forall D' (S: Sub D D'), interpTy t = interpTy (apSubTy S t).
Proof. induction t => /=//; congruence. Qed.

Require Import Casts.
Definition up D D'(S:Sub D D') t (x: interpTy t) : interpTy (apSubTy S t) :=  
  (eq_rect _ (fun X : _ => X) x _ (interpSubst t S)).  

Definition dn D D'(S:Sub D D') t (x: interpTy (apSubTy S t)) := 
  (eq_rect _ (fun X : _ => X) x _ (sym_equal (interpSubst t S))).

Lemma dnup D D' t (S: Sub D D') (x: interpTy t) : dn (up S x) = x.
Proof. by rewrite /up/dn cast_coalesce cast_id. Qed. 

Lemma updn D D' t (S: Sub D D') (x: interpTy (apSubTy S t)) : up S (dn x) = x.
Proof. by rewrite /up/dn cast_coalesce cast_id. Qed. 

Section upLift.
  Variables D D' : Ctxt sig.
  Variables S : Sub D D'.
  Variables t1 t2 : Ty D.

  Lemma upApp (f:interpTy (TyArr t1 t2)) (x:interpTy t1) : up _ (f x) = (up _ f) (up S x). 
  Proof. rewrite /up. rewrite (cast_app (interpSubst t1 S) (interpSubst t2 S)).
  set F1 := f :? arrow_eq _ _. simpl in F1. 
  set F2 := f :? interpSubst _ _. simpl (id _) in F2. 
  have: F1 = F2 by apply cast_UIP. by move ->. 
  Qed. 

  Lemma upFst (p : interpTy (TyProd t1 t2)) : (up _ p).1 = (up S p.1).
  Proof. 
  rewrite /up -(cast_fst (interpSubst t1 S) (interpSubst t2 S)). 
  set H := interpSubst _ _. 
  set H':= prod_eq _ _. simpl interpTy in H. by rewrite cast_UIP. 
  Qed. 

  Lemma upSnd (p : interpTy (TyProd t1 t2)) : (up _ p).2 = (up S p.2).
  Proof. 
  rewrite /up -(cast_snd (interpSubst t1 S) (interpSubst t2 S)). 
  set H := interpSubst _ _. 
  set H':= prod_eq _ _. simpl interpTy in H. by rewrite cast_UIP. 
  Qed. 

  Lemma upInl (x : interpTy t1) : up (t:=TySum t1 t2) S (inl _ x) = inl _ (up (t:=t1) S x).
  Proof.  
  rewrite /up -(cast_inl (interpSubst t1 S) (interpSubst t2 S)). 
  set H := interpSubst _ _. 
  set H' := sum_eq _ _. simpl interpTy in H. by rewrite cast_UIP. 
  Qed. 

  Lemma upInr (x : interpTy t2) : up (t:=TySum t1 t2) S (inr _ x) = inr _ (up (t:=t2) S x).
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

End upLift.



Lemma semSubst D (t: Ty D) : forall D' (S:Sub D D') rho v v', 
  semTy (t:=apSubTy S t) rho (up S v) (up S v') <-> semTy (t:=t) (EcS rho S) v v'.
Proof. induction t => /= D' S rho v v'.

(* TyUnit *)
reflexivity. 

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

End USem.

