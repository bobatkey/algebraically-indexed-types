Require Import ssreflect ssrbool ssrfun seq.
Require Import Relations Program.Equality.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Syntax.

(*---------------------------------------------------------------------------
   Everything is parameterized on a signature, which specifies a type
   for index sorts, for primitive type constructors, and for
   index-level constructors, along with their arities.

   Axioms are introduced later. 
   ---------------------------------------------------------------------------*)
Structure SIG := mkSIG {
  (* Type of sorts e.g. one sort: unit-of-measure *)
  Srt: Type;                  

  (* Type of primitive type constructors e.g. one primitive: real *)
  PrimType: Type;             

  (* Type of index-level constructors e.g. three unit operators, 1 * and inv *)
  IndexOp: Type;              

  (* Arity of index-level operators, e.g. 1:unit, * : (unit,unit)unit, inv: (unit)unit *)
  opArity: IndexOp -> seq Srt * Srt;

  (* Arity of primitive type constructors, e.g. real (unit) *)
  tyArity: PrimType -> seq Srt
}.

(* In this section, assume some sig: SIG *)
Variable sig: SIG.

(* Index variables each have a sort *)
Definition Ctxt := seq (Srt sig). 

(* Index variables, in context. D is \Delta in paper *)
Inductive Var : Ctxt -> Srt sig -> Type :=
| VarZ D s : Var (s::D) s
| VarS D s s' : Var D s -> Var (s'::D) s.

(* Well-sorted index expressions, in context. D is \Delta in paper *)
Inductive Exp (D: Ctxt) : Srt sig -> Type :=
| VarAsExp s :> Var D s -> Exp D s
| AppCon op : Exps D (opArity op).1 -> Exp D (opArity op).2

(* Well-sorted sequences of index expressions, in context *)
with Exps (D: Ctxt) : Ctxt -> Type :=
| Nil : Exps D nil
| Cons s ss : Exp D s -> Exps D ss -> Exps D (s::ss).

Implicit Arguments AppCon [D].
Implicit Arguments Nil [D]. 

Scheme Exp_ind2 := Induction for Exp Sort Prop
with Exps_ind2 := Induction for Exps Sort Prop.

Combined Scheme Exp_Exps_ind from Exp_ind2, Exps_ind2. 

(* Renamings and substitutions. *)
Structure Ren D D' := mkRen {
  getRen :> forall s, Var D s -> Var D' s
}. 

Structure Sub D D' := mkSub {
  getSub :> forall s, Var D s -> Exp D' s
}.

Lemma inj_Ren D D' (R1 R2: Ren D D') : getRen R1 = getRen R2 -> R1 = R2. 
Proof. destruct R1; destruct R2. move => E. injection E. by  move ->. Qed. 

Lemma inj_Sub D D' (S1 S2: Sub D D') : getSub S1 = getSub S2 -> S1 = S2. 
Proof. destruct S1; destruct S2. move => E. injection E. by  move ->. Qed. 

Global Coercion expsAsSub D D' (ixs: Exps D D') : Sub D' D.
refine (mkSub _) => s. 
induction ixs => v.
inversion v.  
dependent destruction v.
+ exact e. 
+ exact (IHixs v). 
Defined.

Program Definition liftRen D D' s (R: Ren D D') : Ren (s::D) (s::D') := 
  mkRen (fun s' v =>
  match v with
  | VarZ _ _ => VarZ _ _
  | VarS _ _ _ v' => VarS _ (R _ v')
  end).

Fixpoint apRen D D' s (r: Ren D D') (ix: Exp D s): Exp D' s :=
  match ix with
  | VarAsExp _ v => VarAsExp (r _ v)
  | AppCon op ixs => AppCon op (apRenSeq r ixs)
  end
with apRenSeq D D' ss (r: Ren D D') (ixs: Exps D ss) : Exps D' ss  :=
  if ixs is Cons _ _ ix ixs 
  then Cons (apRen r ix) (apRenSeq r ixs) 
  else Nil.

Lemma apRenVar D D' s f (v: Var D s) : apRen (mkRen (D':=D') f) v = f s v. 
Proof. done. Qed. 

Definition shExp D s s' : Exp D s -> Exp (s'::D) s := apRen (mkRen (fun _ v => VarS _ v)).

Definition idSub D : Sub D D := mkSub (@VarAsExp _).

Program Definition consSub D D' s (ix: Exp D' s) (S: Sub D D') : Sub (s::D) D' :=
  mkSub (fun s' (v: Var (s::D) s') =>
    match v with VarZ _ _ => ix
               | VarS _ _ _ v' => S _ v'
    end).

Definition tlSub D D' s (S: Sub (s::D) D') : Sub D D' := mkSub (fun s' v => S s' (VarS s v)).
Definition hdSub D D' s (S: Sub (s::D) D') : Exp D' s := S s (VarZ _ _). 


Fixpoint apSub D D' s (S: Sub D D') (ix: Exp D s): Exp D' s :=
  match ix with
  | VarAsExp _ v => S _ v
  | AppCon op ixs => AppCon op (apSubSeq S ixs)
  end
with apSubSeq D D' ss (S: Sub D D') (ixs: Exps D ss) : Exps D' ss  :=
  if ixs is Cons _ _ ix ixs 
  then Cons (apSub S ix) (apSubSeq S ixs) 
  else Nil.

Lemma apSubVar D D' s f (v: Var D s) : apSub (mkSub (D':=D') f) v = f s v. 
Proof. done. Qed. 


Lemma apSubAppCon D D' (S: Sub D D') op (ixs: Exps D _) : 
  apSub S (AppCon op ixs) = AppCon op (apSubSeq S ixs). 
Proof. done. Qed.

Lemma apSubSeqCons D D' (S: Sub D D') s ss (e: Exp D s) (es: Exps D ss) :
  apSubSeq S (Cons e es) = Cons (apSub S e) (apSubSeq S es).
Proof. done. Qed.

(* This is the lifting operation \sigma_{i:s} of the paper *)
Program Definition liftSub D D' s (S: Sub D D') : Sub (s::D) (s::D') :=
  mkSub (fun s' v =>
  match v with
  | VarZ _ _ => VarAsExp (VarZ _ _)
  | VarS _ _ _ v' => shExp s (S _ v')
  end).

Definition RcR D D' D'' (R: Ren D' D'') (R': Ren D D') : Ren D D'' := 
  mkRen (fun s v => R s (R' s v)).

Definition ScR D D' D'' (S: Sub D' D'') (R: Ren D D') : Sub D D'' :=
  mkSub (fun s v => S s (R s v)).

Definition RcS D D' D'' (R: Ren D' D'') (S: Sub D D') : Sub D D'' :=
  mkSub (fun s v => apRen R (S s v)).

Definition ScS D D' D'' (S: Sub D' D'') (S': Sub D D') : Sub D D'' :=
  mkSub (fun s v => apSub S (S' s v)).

Ltac Rewrites E := 
  (intros; simpl; try rewrite E; 
   repeat (match goal with | [H:context[_=_] |- _] => rewrite H end); 
   auto).

Require Import FunctionalExtensionality.
Ltac ExtVar :=
 match goal with
    [ |- ?X = ?Y ] => 
    (apply (@functional_extensionality_dep _ _ X Y) ; 
     let t := fresh "t" in intro t;
     apply functional_extensionality; 
     let v := fresh "v" in intro v; 
     dependent destruction v; auto) 
  end.

Lemma liftSubId D s : liftSub _ (@idSub D) = @idSub (s::D). 
Proof. apply inj_Sub. ExtVar. Qed.

Lemma apSubId D :
  (forall s (e : Exp D s), apSub (idSub _) e = e) /\ 
  (forall ss (es: Exps D ss), apSubSeq (idSub _) es = es). 
Proof. apply Exp_Exps_ind; Rewrites liftSubId. Qed.

Lemma liftRcR E E' E'' s (r:Ren E' E'') (r':Ren E E') :
  liftRen s (RcR r r') = RcR (liftRen s r) (liftRen s r').
Proof. apply inj_Ren; ExtVar. Qed.

Lemma apRcR E E' E'' (r:Ren E' E'') (r':Ren E E') :
  (forall s (e:Exp E s), apRen (RcR r r') e = apRen r (apRen r' e)) /\
  (forall ss (es:Exps E ss), apRenSeq (RcR r r') es = apRenSeq r (apRenSeq r' es)). 
Proof. apply Exp_Exps_ind; Rewrites liftRcR. Qed.

Lemma liftScR E E' E'' s (S:Sub E' E'') (R:Ren E E') :
  liftSub s (ScR S R) = ScR (liftSub s S) (liftRen s R).
Proof. apply inj_Sub; ExtVar. Qed.

Lemma apScR E E' E'' (S:Sub E' E'') (R:Ren E E') : 
  (forall s (e:Exp E s), apSub (ScR S R) e = apSub S (apRen R e)) /\
  (forall ss (es:Exps E ss), apSubSeq (ScR S R) es = apSubSeq S (apRenSeq R es)).
Proof. apply Exp_Exps_ind; Rewrites liftScR. Qed.

Lemma liftRcS E E' E'' s (R:Ren E' E'') (S:Sub E E') : 
  liftSub s (RcS R S) = RcS (liftRen s R) (liftSub s S).
Proof. apply inj_Sub; ExtVar. simpl. rewrite /shExp. by rewrite -!(proj1 (apRcR _ _)). Qed. 

Lemma apRcS E E' E'' (R:Ren E' E'') (S:Sub E E') : 
  (forall s (e:Exp E s), apSub (RcS R S) e = apRen R (apSub S e)) /\
  (forall ss (es:Exps E ss), apSubSeq (RcS R S) es = apRenSeq R (apSubSeq S es)).
Proof. apply Exp_Exps_ind; Rewrites liftScR. Qed.

Lemma liftScS E E' E'' s (S:Sub E' E'') (S':Sub E E') :
  liftSub s (ScS S S') = ScS (liftSub s S) (liftSub s S').
Proof. apply inj_Sub; ExtVar. simpl. rewrite /shExp. rewrite -(proj1 (apRcS _ _)). 
by rewrite -(proj1 (apScR _ _)). Qed. 

Lemma apScS E E' E'' (S:Sub E' E'') (S':Sub E E') : 
  (forall s (e:Exp E s), apSub (ScS S S') e = apSub S (apSub S' e)) /\
  (forall ss (es:Exps E ss), apSubSeq (ScS S S') es = apSubSeq S (apSubSeq S' es)).
Proof. apply Exp_Exps_ind; Rewrites liftScR. Qed.

Lemma ScS_assoc E E' E'' E''' (S1: Sub E'' E''') (S2: Sub E' E'') (S3: Sub E E') :
  ScS S1 (ScS S2 S3) = ScS (ScS S1 S2) S3.
Proof. apply inj_Sub; ExtVar. simpl. by rewrite (proj1 (apScS S1 S2)). 
simpl. by rewrite (proj1 (apScS S1 S2)). Qed. 

Lemma ScExpsAsSub E E' E'' (S: Sub E'' E') (ixs: Exps _ E) :
expsAsSub (apSubSeq S ixs) = ScS S (expsAsSub ixs).
Proof. admit.  Qed. 

(* Well-sorted type expressions, in context *)
Inductive Ty (D: Ctxt) :=
| TyUnit
| TyProd (t1 t2: Ty D) 
| TySum (t1 t2: Ty D)
| TyArr (t1 t2: Ty D)
| TyPrim (p: PrimType sig) (ixs: Exps D (tyArity p))
| TyAll s (t: Ty (s::D))
| TyExists s (t: Ty (s::D)).

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

Definition shiftSub D D' s (S: Sub D D') : Sub D (s::D') := 
  mkSub (fun s v => shExp _ (S s v)). 

(* This is the operation \pi_{i:s} of the paper *)
Definition pi D s : Sub D (s::D) := shiftSub s (idSub D). 

Lemma apSubPi D s s' (e:Exp D s') : apSub (pi D s) e = shExp s e.
Proof. rewrite /pi/shExp/shiftSub/shExp. simpl. admit. 
Qed. 

Lemma liftSubDef E E' t (s:Sub E' E) : liftSub t s = consSub (VarZ _ _) (shiftSub _ s).
Proof. apply inj_Sub. ExtVar. Qed. 

Lemma liftPi D D' s (S: Sub D D') : ScS (liftSub s S) (pi D s) = ScS (pi D' s) S.
Proof. 
apply inj_Sub. apply functional_extensionality_dep => s'. 
apply functional_extensionality => v. simpl. by rewrite apSubPi. 
Qed. 

(*---------------------------------------------------------------------------
   Now we introduce equational theories for indices, induced by a set of
   axioms. The equational theory is lifted to types.
   ---------------------------------------------------------------------------*)

(* Well-sorted axiom, in context *)
Inductive Ax := mkAx D s (lhs: Exp D s) (rhs: Exp D s).

(* Equational theory induced by axioms *)
Inductive equiv D : forall s, seq Ax -> relation (Exp D s) :=
| EquivRefl s axs (e: Exp D s) : 
  equiv axs e e

| EquivSym s axs (e1 e2: Exp D s) : 
  equiv axs e1 e2 -> equiv axs e2 e1

| EquivTrans s axs (e1 e2 e3: Exp D s) : 
  equiv axs e1 e2 -> equiv axs e2 e3 -> equiv axs e1 e3

| EquivComp axs p (es es': Exps D _) : 
  equivSeq axs es es' -> equiv axs (AppCon p es) (AppCon p es')

| EquivByAxZ s axs D' sigma (e e':Exp D' s) : 
  equiv (mkAx e e' :: axs) (apSub sigma e) (apSub sigma e')

| EquivByAxS s ax axs (e e':Exp D s) : 
  equiv axs e e' ->
  equiv (ax :: axs) e e'

with equivSeq D : forall ss, seq Ax -> relation (Exps D ss) :=
| EquivNil axs : 
  equivSeq axs Nil Nil

| EquivCons axs s ss (e e': Exp D s) (es es': Exps D ss) : 
  equiv axs e e' -> equivSeq axs es es' -> equivSeq axs (Cons e es) (Cons e' es').

Scheme equiv_ind2 := Induction for equiv Sort Prop
with equivSeq_ind2 := Induction for equivSeq Sort Prop.

Combined Scheme equivBoth_ind from equiv_ind2, equivSeq_ind2. 

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
  
End Syntax.

Notation "D '|-' e '===' f" := (@mkAx _ D _ e f) (at level 80, e, f at next level).
Notation "t '-->' s" := (TyArr t s) (at level 55, right associativity) : Ty_scope.
Notation "t * s" := (TyProd t s) (at level 40, left associativity) : Ty_scope.
Notation "t + s" := (TySum t s) (at level 50, left associativity) : Ty_scope.
Delimit Scope Ty_scope with Ty.

Implicit Arguments AppCon [sig D].
Implicit Arguments TyPrim [sig D].

(* This is lemma 2, part 1 *)
Lemma equivSubst sig D D' (S: Sub D D') : 
   (forall s A (e f: Exp (sig:=sig) _ s), 
    equiv A e f -> equiv A (apSub S e) (apSub S f))

/\ (forall ss A (es fs: Exps (sig:=sig) _ ss), 
    equivSeq A es fs -> equivSeq A (apSubSeq S es) (apSubSeq S fs)).
Proof.
apply equivBoth_ind.
(* EquivRefl *)
+ move => s A e. by apply: EquivRefl.
(* EquivSym *)
+ move => s A e1 e2 E1 E2. by apply: EquivSym.
(* EquivTrans *)
+ move => s A e1 e2 e3 _ E2 _ E4. by apply: EquivTrans E2 E4. 
(* EquivComp *)
+ move => A op es es' E1 E2. rewrite 2!apSubAppCon. by apply EquivComp. 
(* EquivByAxZ *)
+ move => s A D'' S' e e'. 
  rewrite -2!(proj1 (apScS S S')). by apply EquivByAxZ.       
(* EquivByAxS *)
+ move => s A As e e' E1 E2. by apply EquivByAxS. 
(* EquivNil *)
+ move => A. by apply: EquivNil.
(* EquivCons *)
+ move => A s ss e1 e2 es1 es2 E1 E2 E3 E4. rewrite 2!apSubSeqCons. by apply: EquivCons. 
Qed. 

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

