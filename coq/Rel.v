(*===========================================================================
    Binary relations
  ===========================================================================*)
Import Coq.Init.Notations.

Require Export Coq.Classes.Morphisms.
Require Export Relations.

Section RelDefs.
  Variable A B:Type.
  Variable R R':relation A.
  Variable S:relation B.

  Definition difunctional := forall x x' y y', R x y -> R x' y' -> R x y' -> R x' y.

  (* Relation constructions *)
  Definition RelId    := (fun x y => x=y) : relation A.
  Definition RelArrow := (fun f g : A->B =>
    forall x y, R x y -> S (f x) (g y)) : relation (A->B).
  Definition RelProd  := (fun x y : A*B => 
     R (fst x) (fst y) /\ S (snd x) (snd y)) : relation (A*B).
  Definition RelSum :=  (fun x y : A+B =>
    match x with 
    | inl x1 => match y with inl y1 => R x1 y1 | inr y2 => False end
    | inr x2 => match y with inl y1 => False | inr y2 => S x2 y2 end
    end) : relation (A+B).

  (* Composition and inversion *)
  Definition RelComp := (fun x y => exists z, R x z /\ R' z y) : relation A.

  (* Relation equality *)
  Definition RelEq := forall x y, R x y <-> R' x y.

End RelDefs.

Implicit Arguments RelId [].
Implicit Arguments difunctional. 
Implicit Arguments RelComp [A]. 
Implicit Arguments RelArrow.
Implicit Arguments RelProd. 
Implicit Arguments RelSum. 
Implicit Arguments RelEq.

Bind Scope rel_scope with relation.
Open Scope rel_scope.

Notation "R * S" := (RelProd R S) : rel_scope.
Notation "R + S" := (RelSum R S) : rel_scope.
Notation "R 'o' S" := (RelComp R S) (at level 60, right associativity) : rel_scope.

(*
Ltac UnfoldRel := unfold RelProd, RelSum, Relation_Definitions.respectful, RelId, RelComp, RelInv, symmetric, transitive, reflexive, PER, difunctional.
Ltac UnfoldRelAll := unfold RelProd, RelSum, RelArrow, RelId, RelComp, RelInv, symmetric, transitive, reflexive, PER, difunctional in *.
*)

Section RelLemmas.
  Variable A B : Type.
  Variable R : relation A.
  Variable S : relation B.

(*
  Lemma id_PER : PER (RelId A). 
  Proof. split; congruence. Qed.
*)

  Open Scope signature_scope.
  Lemma arrow_symmetric: symmetric _ R -> symmetric _ S -> symmetric _ (R ==> S).
  Proof. firstorder. Qed.

  Lemma arrow_transitive : symmetric _ R -> transitive _ R -> transitive _ S -> transitive _ (R ==> S).
  Proof.
    intros Rsym Rtran Stran f g h H1 H2.
    intros x z H3.
    assert (R z x) by (apply Rsym; assumption).
    assert (R x x) by firstorder.
    firstorder.
  Qed.

(*
  Lemma arrow_PER : PER R -> PER S -> PER (R ==> S).
  Proof.
    UnfoldRel.
    split.
    apply arrow_transitive; intuition.
    apply arrow_symmetric; intuition.
  Qed.

  Lemma prod_PER : PER R -> PER S -> PER (R * S).
  Proof. firstorder. Qed.
*)

  Lemma prod_difunctional : difunctional R -> difunctional S -> difunctional (R * S).
  Proof.
    intros RH SH.
    unfold difunctional in *. unfold RelProd.
    intros p p' q q' pq p'q' pq'.  
    destruct pq as [pq1 pq2].
    destruct p'q' as [p'q'1 p'q'2].
    destruct pq' as [pq'1 pq'2].
    eauto.
  Qed.

  Lemma arrow_difunctional : difunctional S -> difunctional (R ==> S).
  Proof.
    intros SH.
    unfold difunctional, respectful in *.
    intros x x' y y' xy x'y' xy'.
    intros a b ab.
    eauto.
  Qed.

  Lemma sum_difunctional : difunctional R -> difunctional S -> difunctional (R + S).
  Proof.
    intros RH SH.
    unfold difunctional, RelSum in *.
    intros s s' t t' st s't' st'. 
    destruct s as [sl | sr].
    destruct s' as [s'l | s'r]. destruct t as [tl | tr]. destruct t' as [t'l | t'r].
    apply (RH sl s'l tl t'l); intuition. intuition. intuition. intuition.
    destruct t' as [t'l | t'r]. intuition. intuition.
    destruct t as [tl | tr].
    destruct t' as [t'l | t'r]. intuition. intuition. intuition.
    destruct t' as [t'l | t'r]. intuition. intuition. intuition. intuition. 
    destruct s' as [s'l | s'r]. intuition.
    eauto.
  Qed.

End RelLemmas.    

