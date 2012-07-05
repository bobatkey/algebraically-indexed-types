Require Import ssreflect. 
Require Import Eqdep.
Require Import JMeq Program.Equality.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*===========================================================================
    Casts, borrowed from Adam Chlipala's Lambda Tamer library
  ===========================================================================*)
Notation "e :? pf" := (eq_rect _ (fun X : _ => X) e _ pf)
  (no associativity, at level 90).

Lemma cast_id A (x:A) (pf:A=A) : (x :? pf) = x.
Proof. by rewrite /eq_rect (UIP_refl _ A pf). Qed.

Lemma cast_UIP A B (a:A) (pf1:A=B) (pf2:A=B) :
  (a :? pf1) = (a :? pf2).
Proof. by rewrite (UIP _ A B pf1 pf2). Qed.

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
Proof. by move <- => ->. Qed.

Lemma cast_JMeq A B (x: A) (H: A=B): JMeq x (x :? H).
Proof. unfold eq_rect. by case H. Qed.

Lemma cast_sym A B (pf: A=B) x: ((x :? sym_equal pf) :? pf) = x.
Proof. have H := cast_coalesce x (sym_equal pf) pf. by subst. Qed.

Lemma cast_sym_opp A B (pf: A=B) x: ((x :? pf) :? sym_equal pf) = x.
Proof. have H := cast_coalesce x pf (sym_equal pf). by subst. Qed. 

Definition prod_eq A B A' B' (pfA: A=A') (pfB: B=B'): (A*B = A'*B')%type.
Proof. congruence. Defined. 

Definition sum_eq A B A' B' (pfA: A=A') (pfB: B=B'): (A+B = A'+B')%type.
Proof. congruence. Defined. 

Definition arrow_eq A B A' B' (pfA: A=A') (pfB: B=B'): ((A->B) = (A'->B'))%type.
Proof. congruence. Defined. 

Lemma cast_fstAux A B A' B' (pfA:A=A') (pfB:B=B') (p:A*B):
  fst (p :? prod_eq pfA pfB) = (fst p :? pfA).
Proof. rewrite/eq_rect. case pfA. rewrite/prod_eq/trans_eq/f_equal. by case pfB. Qed.

Lemma cast_sndAux A B A' B' (pfA:A=A') (pfB:B=B') (p:A*B):
  snd (p :? prod_eq pfA pfB) = (snd p :? pfB).
Proof. rewrite /eq_rect. case pfA. rewrite/prod_eq/trans_eq/f_equal. by case pfB. Qed.

Lemma cast_pairAux A B A' B' (pfA:A=A') (pfB:B=B') (x:A) (y:B):
  ((x,y) :? prod_eq pfA pfB) = (x :? pfA, y :? pfB).
Proof. rewrite /eq_rect. case pfA. rewrite/prod_eq/trans_eq/f_equal. by case pfB. Qed.

Lemma cast_fst A B A' B' (pfA:A=A') (pfB:B=B') (pfAB: (A*B)%type=(A'*B')%type) (p:A*B):
  fst (p :? pfAB) = (fst p :? pfA).
Proof. rewrite -(cast_UIP _ (prod_eq pfA pfB)). apply cast_fstAux. Qed.

Lemma cast_snd A B A' B' (pfA:A=A') (pfB:B=B') (pfAB: (A*B)%type=(A'*B')%type) (p:A*B):
  snd (p :? pfAB) = (snd p :? pfB).
Proof. rewrite -(cast_UIP _ (prod_eq pfA pfB)). apply cast_sndAux. Qed.

Lemma cast_pair A B A' B' (pfA:A=A') (pfB:B=B') (pfAB: (A*B)%type=(A'*B')%type) (x:A) (y:B):
  ((x,y) :? pfAB) = (x :? pfA, y :? pfB).
Proof. rewrite -(cast_UIP _ (prod_eq pfA pfB)). apply cast_pairAux. Qed.

Lemma cast_inlAux A B A' B' (pfA:A=A') (pfB:B=B') (a:A):
  (inl _ a :? sum_eq pfA pfB) = (inl _ (a :? pfA)).
Proof. rewrite /eq_rect. case pfA. unfold sum_eq, trans_eq, f_equal. by case pfB. Qed.

Lemma cast_inrAux A B A' B' (pfA:A=A') (pfB:B=B') (b:B):
  (inr _ b :? sum_eq pfA pfB) = (inr _ (b :? pfB)).
Proof. rewrite /eq_rect. case pfA. unfold sum_eq, trans_eq, f_equal. by case pfB. Qed.

Lemma cast_inl A B A' B' (pfA: A=A') (pfB: B=B') (pfAB: (A+B)%type = (A'+B')%type) (a:A) :
  (inl _ a :? pfAB) = (inl _ (a :? pfA)).
Proof. rewrite -(cast_UIP _ (sum_eq pfA pfB)). apply cast_inlAux. Qed. 

Lemma cast_inr A B A' B' (pfA: A=A') (pfB: B=B') (pfAB: (A+B)%type = (A'+B')%type) (b:B) :
  (inr _ b :? pfAB) = (inr _ (b :? pfB)).
Proof. rewrite -(cast_UIP _ (sum_eq pfA pfB)). apply cast_inrAux. Qed. 

Lemma cast_appAux :
  forall (A B A' B':Type),
  forall (pfA:A=A') (pfB:B=B') (f:A->B) (a:A),
  ((f a) :? pfB) = (f :? arrow_eq pfA pfB) (a :? pfA).
intros. unfold eq_rect, f_equal. case pfA. case pfB. unfold arrow_eq, trans_eq, f_equal. trivial.
Qed.

Lemma cast_app A B A' B' (pfA:A=A') (pfB:B=B') (pfAB: (A->B)=(A'->B')) (f:A->B) (a:A):
  ((f a) :? pfB) = (f :? pfAB) (a :? pfA).
Proof. rewrite -(cast_UIP _ (arrow_eq pfA pfB)). apply cast_appAux. Qed.

Lemma cast_appFunAux :
  forall (A B A' B':Type),
  forall (pfA:A=A') (pfB:B=B') (f:A->B) (a:A'),
  (f :? arrow_eq pfA pfB) a = (f (a:?sym_equal pfA) :? pfB).
intros. unfold eq_rect, f_equal. case pfB. unfold arrow_eq, trans_eq, f_equal. by destruct pfA. 
Qed.


Lemma cast_appFun A A' B B' (pfA:A=A') (pfB:B=B') (pfAB: (A->B)=(A'->B')) (f:A->B) (a:A'):
  (f :? pfAB) a = (f (a :? sym_equal pfA) :? pfB).
Proof. rewrite -(cast_UIP _ (arrow_eq pfA pfB)). by rewrite -cast_appFunAux.  Qed.
