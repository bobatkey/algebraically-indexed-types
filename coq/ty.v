(*---------------------------------------------------------------------------
   The syntax of types
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

(* Typing contexts: just a sequences of types *)
Definition Ctxt D := seq (Ty D). 

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

Fixpoint apSubCtxt D D' (S: Sub D D') (G: Ctxt D) : Ctxt D' :=
  if G is t::G then apSubTy S t :: apSubCtxt S G else nil.

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

Lemma apCtxtScS E (G: Ctxt E) : forall E' E'' (S: Sub E' E'') (S': Sub E E'),
  apSubCtxt (ScS S S') G = apSubCtxt S (apSubCtxt S' G). 
Proof. induction G => //. move => E' E'' S S'. by rewrite /= apTyScS IHG. Qed. 

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

Lemma apSubCtxtId D (G : Ctxt D) : apSubCtxt (idSub D) G = G.
Proof.
  induction G => /=//.
  by rewrite IHG apSubTyId.
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

Lemma apSubCtxtScS D D' D'' (S : Sub D' D'') (S' : Sub D D') (G : Ctxt D) :
  apSubCtxt S (apSubCtxt S' G) = apSubCtxt (ScS S S') G.
Proof.
  induction G => /=//. 
  by rewrite IHG apSubTyScS.
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

(*---------------------------------------------------------------------------
   Finally, we define terms
   ---------------------------------------------------------------------------*)
Definition TmVar D := Ix (T:= Ty D).

Variable A: seq (Ax sig). 

Inductive Tm D (G: Ctxt D) : Ty D -> Type :=
| VAR t : TmVar G t -> Tm G t
| TYEQ t1 t2 : equivTy A t1 t2 -> Tm G t1 -> Tm G t2
| UNIT : Tm G (TyUnit _)
| PAIR t1 t2 : Tm G t1 -> Tm G t2 -> Tm G (TyProd t1 t2)
| PROJ1 t1 t2 : Tm G (TyProd t1 t2) -> Tm G t1
| PROJ2 t1 t2 : Tm G (TyProd t1 t2) -> Tm G t2
| INL t1 t2 : Tm G t1 -> Tm G (TySum t1 t2)
| INR t1 t2 : Tm G t2 -> Tm G (TySum t1 t2)
| CASE t1 t2 t : Tm G (TySum t1 t2) -> Tm (t1::G) t -> Tm (t2::G) t -> Tm G t
| ABS t1 t2 : Tm (t1::G) t2 -> Tm G (TyArr t1 t2)  
| APP t1 t2 : Tm G (TyArr t1 t2) -> Tm G t1 -> Tm G t2
| UNIVABS s t : Tm (D:=s::D) (apSubCtxt (pi D s) G) t -> Tm G (TyAll t)
| UNIVAPP s t e : Tm G (TyAll (s:=s) t) -> Tm G (apSubTy (consSub e (idSub _)) t)
| EXPACK s e t : Tm G (apSubTy (consSub e (idSub _)) t) -> Tm G (TyExists (s:=s) t)
| EXUNPACK s t t' : Tm G (TyExists t) -> 
                    Tm (D:=s::D) (t :: apSubCtxt (pi D s) G) (apSubTy (pi D s) t') -> Tm G t'
.

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

Fixpoint apSubTyTmVar sig D D' (S: Sub (sig:=sig) D D') (G: Ctxt D) t  (v: TmVar G t)
  : TmVar (apSubCtxt S G) (apSubTy S t)
  :=
  match v with
  | ixZ _ _ => ixZ _ _
  | ixS _ _ _ v => ixS _ (apSubTyTmVar S v)
  end.

Lemma funny {sig A D D'} (S: Sub (sig:=sig) D D') (G: Ctxt D) s (t: Ty _) e :
  Tm A (apSubCtxt S G) (apSubTy (consSub (apSub S e) (idSub _)) (apSubTy (liftSub s S) t)) =
  Tm A (apSubCtxt S G) (apSubTy S (apSubTy (consSub e (idSub _)) t)).
Proof. apply f_equal. 
rewrite -!apTyScS. 
by rewrite ScSingle. 
Qed. 

Lemma funny2 {sig A D D'} (S: Sub (sig:=sig) D D') (G: Ctxt D) s (t: Ty _) :
Tm A (apSubCtxt (liftSub s S) (apSubCtxt (pi D s) G)) (apSubTy (liftSub s S) t) = 
Tm A (apSubCtxt (pi D' s) (apSubCtxt S G)) (apSubTy (liftSub s S) t).
Proof. by rewrite -!apCtxtScS liftPi. Qed. 

Lemma funny3 {sig A D D'} (S: Sub (sig:=sig) D D') (G: Ctxt D) s (t: Ty _) (t': Ty _) :
Tm A (apSubCtxt (liftSub s S) (t :: apSubCtxt (pi D s) G))
     (apSubTy (liftSub s S) (apSubTy (pi _ s) t')) =
Tm A (apSubTy (liftSub s S) t :: apSubCtxt (pi _ s) (apSubCtxt S G))
     (apSubTy (pi _ s) (apSubTy S t')).
Proof. rewrite -apTyScS liftPi apTyScS. simpl.  
by rewrite -apCtxtScS liftPi apCtxtScS.    
Qed. 

Fixpoint apSubTyTm {sig A D D'} (S: Sub (sig:=sig) D D') (G: Ctxt D) (t: Ty D) (M: Tm A G t)
  :=
  match M in Tm _ _ t return Tm A (apSubCtxt S G) (apSubTy S t) with
  | VAR _ v => VAR _ (apSubTyTmVar S v)
  | TYEQ t1 t2 eq M => TYEQ (equivTySubst eq S) (apSubTyTm S M)
  | UNIT => UNIT _ _
  | PAIR t1 t2 M1 M2 => PAIR (apSubTyTm S M1) (apSubTyTm S M2)
  | PROJ1 t1 t2 M => PROJ1 (apSubTyTm S M)
  | PROJ2 t1 t2 M => PROJ2 (apSubTyTm S M)
  | INL t1 t2 M => INL _ (apSubTyTm S M)
  | INR t1 t2 M => INR _ (apSubTyTm S M)
  | CASE t1 t2 t M M1 M2 => CASE (apSubTyTm S M) (apSubTyTm S M1) (apSubTyTm S M2)
  | ABS t1 t2 M => ABS (apSubTyTm S M)
  | APP t1 t2 M1 M2 => APP (apSubTyTm S M1) (apSubTyTm S M2)
  | UNIVAPP s t e M => (UNIVAPP (apSub S e) (apSubTyTm S M)) :? (funny S G t e)
  | EXPACK s e t M => EXPACK (apSubTyTm S M :? (sym_equal (funny S G t e)))
  | UNIVABS s t M => UNIVABS (apSubTyTm (liftSub s S) M :? funny2 _ _ _)
  | EXUNPACK s t t' M1 M2 => EXUNPACK (apSubTyTm S M1) (apSubTyTm (liftSub s S) M2 :? funny3 _ _ _ _)
  end.




