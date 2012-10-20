(*---------------------------------------------------------------------------
   The syntax of algebraically-indexed types
   (Section 3.1 from POPL'13)
   ---------------------------------------------------------------------------*)
Require Import ssreflect ssrbool ssrfun seq.
Require Import Relations Program.Equality Casts exp.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "c '.<' x , .. , y '>'" (right associativity, at level 30, x, y at next level).
Reserved Notation "c '.<>' " (at level 2). 

Section TySyntax.

Variable sig: SIG. 

(*---------------------------------------------------------------------------
   Having formalized the syntax of index expressions, we now move on to types
   ---------------------------------------------------------------------------*)

(* Well-sorted type expressions, in context *)
Inductive Ty (D: IxCtxt sig) :=
| TyUnit
| TyProd (t1 t2: Ty D) 
| TySum (t1 t2: Ty D)
| TyArr (t1 t2: Ty D)
| TyPrim (p: PrimType sig) (ixs: Exps D (tyArity p))
| TyAll s (t: Ty (s::D))
| TyExists s (t: Ty (s::D)).

Fixpoint existentialFree D (t: Ty D) :=
  match t with
  | TyUnit       => True
  | TyProd t1 t2 => existentialFree t1 /\ existentialFree t2
  | TySum  t1 t2 => existentialFree t1 /\ existentialFree t2
  | TyArr  t1 t2 => existentialFree t1 /\ existentialFree t2
  | TyAll    _ t => existentialFree t
  | TyExists _ t => False
  | TyPrim   p _ => True
  end.

Fixpoint quantifierFree D (t: Ty D) :=
  match t with
  | TyUnit       => True
  | TyProd t1 t2 => quantifierFree t1 /\ quantifierFree t2
  | TySum  t1 t2 => quantifierFree t1 /\ quantifierFree t2
  | TyArr  t1 t2 => quantifierFree t1 /\ quantifierFree t2
  | TyAll    _ t => False
  | TyExists _ t => False
  | TyPrim   p _ => True
  end.

(* The action of an index substitution on types *)
Fixpoint apSubTy D D' (S: Sub D D') (t: Ty D): Ty D' :=
  match t with
  | TyUnit       => TyUnit _
  | TyProd t1 t2 => TyProd   (apSubTy S t1) (apSubTy S t2)
  | TySum  t1 t2 => TySum    (apSubTy S t1) (apSubTy S t2)
  | TyArr  t1 t2 => TyArr    (apSubTy S t1) (apSubTy S t2)
  | TyAll    s t => TyAll    (apSubTy (liftSub s S) t)
  | TyExists s t => TyExists (apSubTy (liftSub s S) t)
  | TyPrim p ixs => TyPrim   (apSubSeq S ixs)
  end.

Lemma apTyScS E (t:Ty E) : forall E' E'' (S:Sub E' E'') (S':Sub E E'),
  apSubTy (ScS S S') t = apSubTy S (apSubTy S' t).
Proof. induction t => E' E'' S S' /=. 
  done. 
  by rewrite IHt1 IHt2. 
  by rewrite IHt1 IHt2. 
  by rewrite IHt1 IHt2. 
  by rewrite (proj2 (apScSAndSeq _ _)).    
  by rewrite liftScS IHt. 
  by rewrite liftScS IHt. 
Qed. 

Lemma apSubTyId D (t : Ty D) : apSubTy (idSub D) t = t.
Proof.
  induction t => /=.
    by reflexivity.
    by rewrite IHt1 IHt2. 
    by rewrite IHt1 IHt2. 
    by rewrite IHt1 IHt2. 
    by rewrite (proj2 (apSubIdAndSeq _)).  
    by rewrite liftSubId IHt. 
    by rewrite liftSubId IHt. 
Qed.

Lemma apSubTyScS D (t : Ty D) :   forall D' D'' (S : Sub D' D'') (S' : Sub D D'),
    apSubTy S (apSubTy S' t) = apSubTy (ScS S S') t.
Proof.
 induction t => D' D'' S S' => /=.
   by reflexivity.
   by rewrite IHt1 IHt2.
   by rewrite IHt1 IHt2.
   by rewrite IHt1 IHt2.
   by rewrite (proj2 (apScSAndSeq S S')).
   by rewrite IHt liftScS. 
   by rewrite IHt liftScS. 
Qed.


(* Equational theory lifted to types *)
Inductive equivTy D A : relation (Ty D) :=
| EquivTyRefl (t: Ty D) :
  equivTy A t t

| EquivTySym (t1 t2: Ty D) :
  equivTy A t1 t2 -> equivTy A t2 t1

| EquivTyTrans (t1 t2 t3: Ty D) : 
  equivTy A t1 t2 -> equivTy A t2 t3 -> equivTy A t1 t3

| EquivTyProd (t1 t1' t2 t2': Ty D) :
  equivTy A t1 t1' -> equivTy A t2 t2' ->
  equivTy A (TyProd t1 t2) (TyProd t1' t2')

| EquivTySum (t1 t1' t2 t2': Ty D) :
  equivTy A t1 t1' -> equivTy A t2 t2' ->
  equivTy A (TySum t1 t2) (TySum t1' t2')

| EquivTyArr (t1 t1' t2 t2': Ty D) :
  equivTy A t1 t1' -> equivTy A t2 t2' ->
  equivTy A (TyArr t1 t2) (TyArr t1' t2')

| EquivTyPrim (op: PrimType sig) (es es': Exps D _):
  equivSeq A es es' ->
  equivTy A (TyPrim (p:= op) es) (TyPrim es')

| EquivTyAll s (t t': Ty (s::D)) :
  equivTy A (D:=s::D) t t' ->
  equivTy A (TyAll t) (TyAll t')

| EquivTyExists s (t t': Ty (s::D)) :
  equivTy A (D:=s::D) t t' ->
  equivTy A (TyExists t) (TyExists t').


End TySyntax.

Implicit Arguments TyPrim [sig D].

(* Some handy notation for applying type constructors *)
Notation "c '.<' x , .. , y '>'" := (TyPrim c (Cons x .. (Cons y (Nil _)) .. )) :Ty_scope.
Notation "c '.<>'" := (TyPrim c (Nil _)) : Ty_scope. 
Notation "D '|-' e '===' f" := (@mkAx _ D _ e f) (at level 80, e, f at next level).
Notation "t '-->' s" := (TyArr t s) (at level 55, right associativity) : Ty_scope.
Notation "t * s" := (TyProd t s) (at level 40, left associativity) : Ty_scope.
Notation "t + s" := (TySum t s) (at level 50, left associativity) : Ty_scope.

Definition all sig D s (t:Ty (sig:=sig) (s::D)) := TyAll (s:=s) t.
Implicit Arguments all [sig D].

Delimit Scope Ty_scope with Ty.
Bind Scope Ty_scope with Ty.

(* This is lemma 2, part 2 *)
Lemma equivTySubst sig D A (t t': Ty (sig:=sig) D) :
  equivTy A t t' -> forall D' (S: Sub D D'), equivTy A (apSubTy S t) (apSubTy S t').
Proof.
move => E. induction E => D' S. 
(* EquivTyRefl *)
+ by apply: EquivTyRefl.
(* EquivTySym *)
+ by apply: EquivTySym.
(* EquivTyTrans *)
+ apply: EquivTyTrans => //. 
(* EquivTyProd *)
+ apply: EquivTyProd => //. 
(* EquivTySum *)
+ apply: EquivTySum => //. 
(* EquivTyArr *)
+ apply: EquivTyArr => //. 
(* EquivTyPrim *)
+ apply: EquivTyPrim. apply equivSubst => //.  
(* EquivTyAll *)
+ apply: EquivTyAll. apply IHE. 
(* EquivTyExists *)
+ apply: EquivTyExists. apply IHE. 
Qed. 


