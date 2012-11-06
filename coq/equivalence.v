(*---------------------------------------------------------------------------
   Contextual equivalence and type isomorphism
   (Section 3.3 from POPL'13 paper)
   ---------------------------------------------------------------------------*)
Require Import ssreflect ssrbool ssrfun seq.
Require Import Relations Program.Equality.
Require Import FunctionalExtensionality.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import exp ty tm esem Casts.

Section ContextualEquivalence.

Variable sig : SIG.
Variable A : seq (Ax sig).

Variable interpPrim : PrimType sig -> Type.

(* Typing context for primitive operations *)
Variable G_ops : Ctxt (sig:=sig) [::].

(* Interpretation for primitive operations *)
Variable eta_ops : interpCtxt interpPrim G_ops.

(* Given typing context G and type t, construct n-ary arrow type G -> t *)
Fixpoint mkArrTy D (G: Ctxt (sig:=sig) D) (t: Ty D) : Ty D :=
  if G is s::G then mkArrTy G (TyArr s t) else t.

(* Given index context D and type t, construct closed n-ary polymorphic type \forall D.t *)
Fixpoint mkForallTy (D : IxCtxt sig) : Ty D -> Ty [::] :=
  if D is _::_
  then fun t => mkForallTy (TyAll t) 
  else fun t => t.

(* Boolean type *)
Definition tyBool D : Ty (sig:=sig) D := TySum (TyUnit D) (TyUnit D).

Fixpoint mkLamTm D (G G': Ctxt (sig:=sig) D) (t: Ty D) : Tm A (G ++ G') t -> Tm A G' (mkArrTy G t) :=
  if G is _::_
  then fun M => mkLamTm (ABS M) 
  else fun M => M. 

Fixpoint piAll (D : IxCtxt sig) : Sub [::] D :=
  if D is s::D
  then ScS (pi D s) (piAll D)
  else idSub [::]. 

Lemma tmEqPiNilCtxt (G : Ctxt [::]) (t : Ty [::]) :
      Tm A (apSubCtxt (piAll [::]) G) t = Tm A G t.
Proof. by rewrite apSubCtxtId. Qed.

Lemma tmEqPiConsCtxt D (G : Ctxt [::]) s (t : Ty (s :: D)) :
  Tm A (apSubCtxt (piAll (s :: D)) G) t = Tm A (apSubCtxt (pi D s) (apSubCtxt (piAll D) G)) t.
Proof. by rewrite /= -(apSubCtxtScS (pi D s) (piAll D)). Qed.

Fixpoint mkForallTm (D : IxCtxt sig) (G : Ctxt [::]) :
  forall t : Ty D, Tm A (apSubCtxt (piAll D) G) t -> Tm A G (mkForallTy t) :=
  if D is _::_
  then fun t M => mkForallTm (UNIVABS (M :? tmEqPiConsCtxt G t))
  else fun t M => M :? tmEqPiNilCtxt G t.

(* Contextual equivalence: Definition 1 from POPL'13 paper *)
Definition ctxtEq D (G: Ctxt D) (t: Ty D) (M1 M2: Tm A (G ++ (apSubCtxt (piAll D) G_ops)) t) :=
  forall (T : Tm A G_ops (mkForallTy (mkArrTy G t) --> tyBool [::])%Ty), 
    let M1' := mkForallTm (mkLamTm M1) in
    let M2' := mkForallTm (mkLamTm M2) in
    interpTm (APP T M1') eta_ops = interpTm (APP T M2') eta_ops.

(* Underlying equivalence, sound for contextual equivalence and sometimes useful *)
Definition usemEq D (G: Ctxt D) (t: Ty D) (M1 M2: Tm A (G ++ apSubCtxt (piAll D) G_ops) t) :=
  forall eta,
   interpTm M1 (catEnv eta (eta_ops :? interpSubCtxt interpPrim G_ops (piAll D))) =
   interpTm M2 (catEnv eta (eta_ops :? interpSubCtxt interpPrim G_ops (piAll D))).

Lemma mkArrTy_usem D G :
  forall t (M1 M2 : Tm A (G ++ (apSubCtxt (piAll D) G_ops)) t),
    (forall (eta : interpCtxt interpPrim G),
         (interpTm M1 (catEnv eta (eta_ops :? interpSubCtxt interpPrim G_ops (piAll D)))) =
         (interpTm M2 (catEnv eta (eta_ops :? interpSubCtxt interpPrim G_ops (piAll D))))) ->
         (interpTm (mkLamTm M1) (eta_ops :? interpSubCtxt interpPrim G_ops (piAll D))) =
         (interpTm (mkLamTm M2) (eta_ops :? interpSubCtxt interpPrim G_ops (piAll D))).
Proof.
  induction G => t' M1 M2 M1_M2.
   (* nil *)
   apply (M1_M2 tt).
   (* cons *)
   simpl. apply IHG. 
   simpl. move => eta.
   apply functional_extensionality => x.
   apply: M1_M2 (x,eta). 
Qed.

Lemma mkForallTy_usem D :
  forall (t : Ty D) (M1 M2 : Tm A (apSubCtxt (piAll D) G_ops) t),
  (               (interpTm M1 (eta_ops :? interpSubCtxt interpPrim G_ops (piAll D))) =
                  (interpTm M2 (eta_ops :? interpSubCtxt interpPrim G_ops (piAll D)))) ->
                 (interpTm (mkForallTm M1) eta_ops) =
                 (interpTm (mkForallTm M2) eta_ops).
Proof.
  induction D => t' M1 M2 H.
  (* nil *)
   simpl. 
   revert M1 M2 H.
   rewrite cast_UIP. by rewrite apSubCtxtId.
   move => H M1 M2.
   rewrite (cast_UIP M1). by rewrite apSubCtxtId.
   move => H1.
   rewrite (cast_UIP M2). 
   revert H M1 M2 H1. rewrite apSubCtxtId.
   move => H M1 M2 H1. by rewrite 3!cast_id. 
   (* cons *)
   apply IHD.
   simpl. 
   rewrite cast_coalesce. 
   revert M1 M2 H.
   rewrite cast_UIP. apply interpSubCtxt. 
   rewrite cast_UIP. rewrite apSubCtxtScS. apply interpSubCtxt. 
   move => H1 H2 M1 M2.
   rewrite (cast_UIP M1). rewrite apSubCtxtScS. reflexivity.
   move => H3.
   rewrite (cast_UIP M2).
   revert H1 H2 H3 M1 M2.
   rewrite apSubCtxtScS.
   move => H1 H2 H3 M1 M2.
   rewrite (cast_UIP eta_ops H1 H2). 
   by rewrite 2!cast_id. 
Qed.


(* Underlying equivalence is contained in contextual equivalence *)
Theorem usemEq_implies_ctxtEq D (G: Ctxt D) (t: Ty D) (M1 M2: Tm A (G ++ (apSubCtxt (piAll D) G_ops)) t):
  usemEq M1 M2 ->
  ctxtEq M1 M2.
Proof.
  rewrite /usemEq/ctxtEq.
  move => M1_usemEq_M2 T /=.
  apply f_equal.
  apply mkForallTy_usem. 
  by apply mkArrTy_usem.
Qed. 

(* Contextual equivalence is an equivalence relation *)
Lemma ctxtEq_equivalence D (G: Ctxt D) (t: Ty D) : equivalence _ (@ctxtEq _ G t). 
Proof. 
apply Build_equivalence. 
(* Reflexivity *)
move => M. done. 
(* Transitivity *)
move => M1 M2 M3 H1 H2.
move => T.  
simpl. 
specialize (H1 T). specialize (H2 T). 
simpl in H1. simpl in H2. by rewrite H1 H2. 
(* Symmetry *)
move => M1 M2 H. 
move => T. simpl. specialize (H T). simpl in H. done. 
Qed. 

(* Test lemma: beta reduction of identity *)
Example apply_identity D (G: Ctxt D) t (M: Tm A (G ++ _) t) : ctxtEq (APP (ABS ##0) M) M.
Proof. apply usemEq_implies_ctxtEq; by rewrite /usemEq => eta/=. Qed. 


End ContextualEquivalence.

(*==============================================================================================
   TYPE ISOMORPHISMS

   We define an isomorphism between types X and Y, written X ~= Y,
   as a pair of maps i and j such that
     forall psi, psi |= i : X -> Y
     forall psi, psi |= j : Y -> X
   and
     forall psi, psi |= j o i = id : X -> X
     forall psi, psi |= i o j = id : Y -> Y

   We then show ~= is
     (a) an equivalence relation
     (b) a congruence, wrt all type constructors
   and then prove
     (a) units-independent isomorphisms, such as commutative of product, currying, etc
     (b) units-dependent isomorphisms, as used in the proof of the Pi theorem in POPL'97.
  ==============================================================================================*)

Section Iso.

Variable sig: SIG.
Variable A: seq (Ax sig).
Variable interpPrim: PrimType sig -> Type.
Variable G_ops : Ctxt (sig:=sig) nil.
Variable eta_ops : interpCtxt interpPrim G_ops.

Notation "| t |" := (interpTy interpPrim t).

Definition Id D (t:Ty D) := fun (x:|t|) => x.
Implicit Arguments Id [D]. 

Notation "G |- x =~= y :> t" := (@ctxtEq sig A interpPrim G_ops eta_ops _ G t x y) (at level 67, x at level 67,y at level 67).

Definition iso D (X Y: Ty D) := 
  exists i : Tm A (apSubCtxt (piAll D) G_ops) (TyArr X Y), 
  exists j : Tm A (apSubCtxt (piAll D) G_ops) (TyArr Y X),
  (forall M : Tm A (apSubCtxt (piAll D) G_ops) X,
  [::] |- APP j (APP i M) =~= M :> X) /\
  (forall M : Tm A (apSubCtxt (piAll D) G_ops) Y,
  [::] |- APP i (APP j M) =~= M :> Y).

Lemma iso_refl D (X: Ty D) : iso X X.
Proof. 
exists (ABS ##0).  
exists (ABS ##0). 
split => M; by apply usemEq_implies_ctxtEq. 
Qed. 

Lemma iso_sym D (X Y: Ty D) : iso X Y -> iso Y X.
Proof. intros [i [j [ij ji] ] ]. 
exists j. exists i. done.  
Qed. 

Lemma iso_prod_assoc D (X Y Z: Ty D) : iso (X*(Y*Z))%Ty ((X*Y)*Z)%Ty.
Proof.
exists (ABS (PAIR (PAIR (PROJ1 ##0) (PROJ1 (PROJ2 ##0))) (PROJ2 (PROJ2 ##0)))). 
exists (ABS (PAIR (PROJ1 (PROJ1 ##0)) (PAIR (PROJ2 (PROJ1 ##0)) (PROJ2 ##0)))).
split => M; apply usemEq_implies_ctxtEq; rewrite /usemEq => eta/=; set P := interpTm _ _.
  elim P => [P1 P2]. elim P2 => [P3 P4]. done. 
  elim P => [P1 P2]. elim P1 => [P3 P4]. done. 
Qed. 

Lemma iso_prod_unit D (X: Ty D) : iso (X*(TyUnit _)) X.
Proof. 
exists (ABS (PROJ1 ##0)).   
exists (ABS (PAIR ##0 (UNIT _ _))). 
split => M; apply usemEq_implies_ctxtEq; rewrite /usemEq => eta/=; set P := interpTm _ _.
case: P => [P1 P2]. by case P2. 
done. 
Qed. 

End Iso. 


