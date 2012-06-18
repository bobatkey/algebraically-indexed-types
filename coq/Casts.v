Require Import ssreflect. 
Require Import Eqdep.
Require Import JMeq.

(*===========================================================================
    Casts, borrowed from Adam Chlipala's Lambda Tamer library
  ===========================================================================*)
Notation "e :? pf" := (eq_rect _ (fun X : _ => X) e _ pf)
  (no associativity, at level 90).

Lemma cast_id A (x:A) (pf:A=A) : (x :? pf) = x.
Proof. unfold eq_rect. by rewrite (UIP_refl _ A pf). Qed.


Theorem cast_coalesce T1 T2 T3 (e : T1) (pf1 : T1 = T2) (pf2 : T2 = T3):
  ((e :? pf1) :? pf2) = (e :? trans_eq pf1 pf2).
Proof.
  generalize pf1 pf2.
  subst.
  move => pf1 pf2.
  rewrite (UIP_refl _ _ pf1).
  rewrite (UIP_refl _ _ pf2).
  reflexivity.
Qed.

Lemma trans_cast T1 T2 H (x z : T1) (y : T2):
  x = (y :? H)
  -> (y :? H) = z
  -> x = z.
Proof.  move <- => ->. done. Qed.

Lemma cast_JMeq A B (x: A) (H: A=B): JMeq x (x :? H).
Proof. unfold eq_rect. by case H. Qed.

Lemma cast_sym A B (pf: A=B) x: ((x :? sym_equal pf) :? pf) = x.
Proof. have H := cast_coalesce B A B x (sym_equal pf) pf. by subst. Qed.

Lemma cast_sym_opp A B (pf: A=B) x: ((x :? pf) :? sym_equal pf) = x.
Proof. have H := cast_coalesce A B A x pf (sym_equal pf). by subst. Qed. 

Definition prod_eq A B A' B' (pfA: A=A') (pfB: B=B'): (A*B = A'*B')%type.
Proof. congruence. Defined. 

Definition sum_eq A B A' B' (pfA: A=A') (pfB: B=B'): (A+B = A'+B')%type.
Proof. congruence. Defined. 

Definition arrow_eq A B A' B' (pfA: A=A') (pfB: B=B'): ((A->B) = (A'->B'))%type.
Proof. congruence. Defined. 

Implicit Arguments prod_eq [A B A' B'].
Implicit Arguments sum_eq [A B A' B'].
Implicit Arguments arrow_eq [A B A' B'].

Require Import Program.Equality.

Lemma cast_fst :
  forall (A B A' B':Type),
  forall (pfA:A=A') (pfB:B=B') (p:A*B),
  fst (p :? prod_eq pfA pfB) = (fst p :? pfA).
Proof. intros. unfold eq_rect. case pfA. unfold prod_eq, trans_eq, f_equal. case pfB. trivial.
Qed.

Lemma cast_snd :
  forall (A B A' B':Type),
  forall (pfA:A=A') (pfB:B=B') (p:A*B),
  snd (p :? prod_eq pfA pfB) = (snd p :? pfB).
intros. unfold eq_rect. case pfA. unfold prod_eq, trans_eq, f_equal. case pfB. trivial.
Qed.

Lemma cast_inl :
  forall (A B A' B':Type),
  forall (pfA:A=A') (pfB:B=B') (a:A),
  (inl _ a :? sum_eq pfA pfB) = (inl _ (a :? pfA)).
intros. unfold eq_rect. case pfA. unfold sum_eq, trans_eq, f_equal. case pfB. trivial.
Qed.

Lemma cast_inr :
  forall (A B A' B':Type),
  forall (pfA:A=A') (pfB:B=B') (b:B),
  (inr _ b :? sum_eq pfA pfB) = (inr _ (b :? pfB)).
intros. unfold eq_rect. case pfA. unfold sum_eq, trans_eq, f_equal. case pfB. trivial.
Qed.

Lemma cast_app :
  forall (A B A' B':Type),
  forall (pfA:A=A') (pfB:B=B') (f:A->B) (a:A),
  ((f a) :? pfB) = (f :? arrow_eq pfA pfB) (a :? pfA).
intros. unfold eq_rect. case pfA. case pfB. unfold arrow_eq, trans_eq, f_equal. trivial.
Qed.

Implicit Arguments cast_fst [A B A' B'].
Implicit Arguments cast_snd [A B A' B'].
Implicit Arguments cast_inl [A B A' B'].
Implicit Arguments cast_inr [A B A' B'].
Implicit Arguments cast_app [A B A' B'].


Lemma cast_UIP : forall (A B:Type) (a:A) (pf1:A=B) (pf2:A=B),
  (a :? pf1) = (a :? pf2).
intros. 
rewrite (UIP _ A B pf1 pf2). trivial.
Qed.