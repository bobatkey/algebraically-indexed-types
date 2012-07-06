(*===========================================================================
    Binary relations
  ===========================================================================*)
Import Coq.Init.Notations.

Require Export Coq.Classes.Morphisms.
Require Export Relations.
Require Import Casts.

Section RelDefs.
  Variable A B:Type.
  Variable R R':relation A.
  Variable S:relation B.

  Definition difunctional := forall x x' y y', R x y -> R x' y' -> R x y' -> R x' y.

  Inductive difclo : A -> A -> Prop :=
  | difclo_base : forall x y,
                    R x y ->
                    difclo x y
  | difclo_step : forall x x' y y',
                    difclo x y ->
                    difclo x' y' ->
                    difclo x y' ->
                    difclo x' y.

  Definition PER :=
    (forall x y, R x y -> R y x)
      /\
      (forall x y z, R x y -> R y z -> R x z).

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
  Definition RelInv  := (fun x y => R y x) : relation A.

  (* Relation equality *)
  Definition RelEq := forall x y, R x y <-> R' x y.

End RelDefs.

Implicit Arguments RelId [].
Implicit Arguments difunctional. 
Implicit Arguments difclo.
Implicit Arguments PER.
Implicit Arguments RelComp [A]. 
Implicit Arguments RelInv [A].
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

  Lemma difclo_difunctional : difunctional (difclo R).
  Proof.
    unfold difunctional. apply difclo_step.
  Qed.

  Lemma difclo_monotonic : 
    forall R' : relation A,
      (forall x y, R x y -> R' x y) ->
      forall x y,
        difclo R x y -> difclo R' x y. 
  Proof.
    intros R' incl x y difclo_R_x_y.
    induction difclo_R_x_y.
    (* base *)
      apply difclo_base. apply incl. assumption.
    (* step *)
      eapply difclo_step; eassumption.
  Qed.

  Lemma difclo_inv :
    (forall x y, R x y -> R y x) ->
    (forall x y, difclo R x y -> difclo R y x).
  Proof.
    intros R_inv x y difclo_R_x_y.
    induction difclo_R_x_y.
     (* base *) apply difclo_base. intuition.
     (* step *) eapply difclo_step; eassumption.
  Qed.

  Lemma difclo_closure : difunctional R -> RelEq R (difclo R).
  Proof.
    intros dif. unfold RelEq. intros x y. split.
    (* -> *)
      intros r. apply difclo_base. assumption.
    (* <- *)
      intros dif_r. induction dif_r.
      (* difclo_base *)
        assumption.
      (* difclo_step *)
        unfold difunctional in dif.
        eapply dif; eassumption.
  Qed.

  Lemma difclo_ext : forall R', RelEq R R' -> RelEq (difclo R) (difclo R').
  Proof.
    intros R' R_eq_R'.
    intros x y. split.
    (* -> *)
      intro difclo_R_x_y. induction difclo_R_x_y. 
       apply difclo_base. apply R_eq_R'. assumption.
       eapply difclo_step; eassumption.
    (* <- *)
      intro difclo_R'_x_y. induction difclo_R'_x_y. 
       apply difclo_base. apply R_eq_R'. assumption.
       eapply difclo_step; eassumption.
  Qed.

  Lemma difclo_cast :
    forall (C D : Type) (R1 : relation C) (R2 : relation D) (eq : C = D),
      (forall x y, R1 x y -> R2 (x :? eq) (y :? eq)) ->
      forall x y, difclo R1 x y -> difclo R2 (x :? eq) (y :? eq).
  Proof.
    intros C D R1 R2 eq R1_R2 x y difclo_R_x_y.
    induction difclo_R_x_y.
    (* base *)
      apply difclo_base. apply R1_R2. assumption.
    (* step *)
      eapply difclo_step; eassumption.
  Qed.

  Lemma difclo_cast2 : 
    forall (C D : Type) (R1 : relation C) (R2 : relation D) (eq : D = C),
      (forall x y, R1 (x :? eq) (y :? eq) -> R2 x y) ->
      forall x y, difclo R1 (x :? eq) (y :? eq) -> difclo R2 x y.
  Proof.
    intros C D R1 R2 eq R1_R2 x y.
    replace x with ((x :? eq) :? sym_equal eq).
    replace y with ((y :? eq) :? sym_equal eq).
    intro. apply difclo_cast with (R1:=R1).
     intros x' y' r. apply (R1_R2 (x' :? sym_equal eq) (y' :? sym_equal eq)).
       rewrite cast_coalesce. rewrite cast_id.
       rewrite cast_coalesce. rewrite cast_id.
       assumption.
    rewrite cast_coalesce in H. rewrite cast_id in H.
    rewrite cast_coalesce in H. rewrite cast_id in H.
    assumption.
    rewrite cast_coalesce. apply cast_id.
    rewrite cast_coalesce. apply cast_id.
  Qed.

  Lemma difclo_cast3 : 
    forall (R' : relation B) (eq : B = A),
      (forall x y, R (x :? eq) (y :? eq) <-> R' x y) ->
      forall x y, difclo R (x :? eq) (y :? eq) <-> difclo R' x y.
  Proof.
    intros R' eq R_R' x y. split.
    apply difclo_cast2. apply R_R'.
    apply difclo_cast. apply R_R'.
  Qed.

  (* Difunctional relations and PERs *)

  Lemma difunctional_yields_per_left :
    difunctional R ->
    PER (R o (RelInv R)).
  Proof.
    intro DIF. unfold RelComp. unfold RelInv. split. 
    (* symmetric *)
    intros x y [z [R1 R2]]. exists z. auto.
    (* transitive *)
    intros x y z [z1 [R1 R2]] [z2 [R3 R4]].
    exists z1. split.
      assumption.
      eapply DIF; eassumption.
  Qed.

  Lemma difunctional_yields_per_right :
    difunctional R ->
    PER ((RelInv R) o R).
  Proof.
    intro DIF. unfold RelComp. unfold RelInv. split. 
    (* symmetric *)
    intros x y [z [R1 R2]]. exists z. auto.
    (* transitive *)
    intros x y z [z1 [R1 R2]] [z2 [R3 R4]].
    exists z1. split.
      assumption.
      eapply DIF; eassumption.
  Qed.

  Definition Saturated R1 R2 :=
    forall x1 x2 x3 x4,
      R1 x1 x2 -> R x2 x3 -> R2 x3 x4 -> R x1 x4.

  (* If 'R' is a QPER, then it is a saturated relation between the two PERS derived *)
  Lemma qper_saturated :
    difunctional R ->
    Saturated (difclo R o RelInv (difclo R)) (RelInv (difclo R) o difclo R).
  Proof.
    intro DIF.
    unfold Saturated. unfold RelComp. unfold RelInv.
    intros x1 x2 x3 x4 [z1 [R1 R2]] R3 [z2 [R4 R5]].
    apply difclo_closure. apply DIF.
    assert (difclo R x2 x3). apply difclo_closure; assumption.
    eauto using difclo_difunctional.
  Qed.

  Lemma reflexive_qper_transitive :
    (forall x, R x x) ->
    difunctional R ->
    (forall x y z, R x y -> R y z -> R x z).
  Proof.
    intros REFL DIF. intros x y z R1 R2.
    eapply DIF. apply R2. apply R1. apply REFL.
  Qed.

  Lemma functionalrel_difunctional :
    forall (f : A -> A), difunctional (fun x y => f x = y).
  Proof.
    intro f. unfold difunctional. congruence.
  Qed.

End RelLemmas.
