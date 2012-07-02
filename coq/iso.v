(****************************************************************************)
(* Semantic isomorphisms of algebraically-indexed types                     *)
(****************************************************************************)

Require Import ssreflect ssrbool ssrfun seq.
Require Import Relations Program.Equality.
Require Import Rel syn Casts sem.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

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
Variable interpPrim: PrimType sig -> Type.

Notation "| t |" := (interpTy interpPrim t).

Definition Id D (t:Ty D) := fun (x:|t|) => x.
Implicit Arguments Id [D]. 

Variable ES: RelEnvSet interpPrim. 
Variable A: seq (Ax sig). 
Variable CLOSED: ClosedRelEnvSet A ES. 

Notation "rho |= x == y :> t" := (@semTy sig interpPrim ES _ rho t x y) (at level 67, x at level 67, y at level 67).


Open Scope Ty_scope.
Definition iso D (X Y:Ty D) := exists i, exists j, 
   (forall psi, psi |= i==i :> X --> Y) /\ 
   (forall psi, psi |= j==j :> Y --> X) /\
   (forall psi, psi |= (fun x => j(i(x))) == Id X :> X-->X) /\
   (forall psi, psi |= (fun y => i(j(y))) == Id Y :> Y-->Y).

Notation "X ~= Y" := (iso X Y) (at level 70).

Section StandardIsos.

Open Scope Ty_scope.

Variable D : Ctxt sig.
Variables W X Y Z : Ty D.
Variable s : Srt sig. 
Variables W' X' Y' Z' : Ty (s::D). 

Axiom ENVDIF: forall D (psi: RelEnv interpPrim D) (p: PrimType sig) (exps: Sub (tyArity p) D), 
  difunctional (psi p exps). 

(*---------------------------------------------------------------------------
   Type isomorphism is an equivalence relation
   ---------------------------------------------------------------------------*)
Lemma iso_refl : X ~= X.
Proof. exists (fun x => x), (fun x => x) => /=//. Qed.

Lemma iso_sym : X ~= Y -> Y ~= X.
Proof. intros [i [j H] ]. exists j, i. intuition. Qed.

Lemma iso_tran : X ~= Y -> Y ~= Z -> X ~= Z.
Proof. move => H1 H2. destruct H1 as [i1 [j1 [H1a [H1b [H1c H1d] ] ] ] ]. simpl in *. 
destruct H2 as [i2 [j2 [H2a [H2b [H2c H2d] ] ] ] ]. simpl in *. 
exists (fun x => i2 (i1 (x))), (fun x => j1 (j2 (x))). 

simpl. 
split. intuition.  
split. intuition.
split. 

intros psi x x' xx'.
(* By logical interpretation of functions, we know i1 x ~ i1 x' *)  
have H3 : semTy ES psi (i1 x) (i1 x'); auto.

(* We now use difunctionality of the semantics *)
assert (H4 := H2c psi (i1 x) (i1 x') H3). 
assert (H5 := H1b psi (j2 (i2 (i1 x))) (i1 x') H4).
assert (H6 := H1c psi x x' xx').
assert (H7 := H1b psi (i1 x) (i1 x') H3).
assert (DIF:= @sem_difunctional sig interpPrim ES A CLOSED ENVDIF D X psi).
apply (DIF (j1(i1 x)) (j1(j2(i2(i1(x))))) x' (j1(i1 x')) H6 H5 H7).

(* By logical interpretation of functions, we know j1 z ~ y1 z' *)
intros psi z z' zz'.
assert (H3 : semTy ES psi (j2 z) (j2 z')); auto.

(* We now use difunctionality of the semantics *)
assert (H4 := H1d psi (j2 z) (j2 z') H3).
assert (H5 := H2a psi (i1 (j1 (j2 z))) (j2 z') H4).
assert (H6 := H2d psi z z' zz').
assert (H7 := H2a psi (j2 z) (j2 z') H3).
assert (DIF := @sem_difunctional sig interpPrim ES A CLOSED ENVDIF D Z psi).
unfold difunctional in DIF.
apply (DIF (i2(j2 z)) (i2(i1(j1(j2 z)))) z' (i2(j2 z')) H6 H5 H7).
Qed.

(*---------------------------------------------------------------------------
   Type isomorphism is a congruence
   ---------------------------------------------------------------------------*)
(* Product *)
Lemma iso_prod_cong : W ~= X -> Y ~= Z -> W * Y ~= X * Z.
Proof.
  unfold iso, Id. simpl. 
  intros WX YZ.
  destruct WX as [Xi [Xj [Xihas_ty [Xjhas_ty [Xji Xij] ] ] ] ].
  destruct YZ as [Yi [Yj [Yihas_ty [Yjhas_ty [Yji Yij] ] ] ] ].
  
  exists (fun p => (Xi p.1, Yi p.2)).
  exists (fun p => (Xj p.1, Yj p.2)).
  repeat (split; simpl; intuition).
Qed.

(* Arrow *)
Lemma iso_arrow_cong (X1 X2 Y1 Y2 : Ty D) : X1 ~= X2 -> Y1 ~= Y2 -> X1 --> Y1 ~= X2 --> Y2.
Proof.
  unfold iso, Id. simpl. 
  intros X1X2 Y1Y2.
  destruct X1X2 as [Xi [Xj [Xihas_ty [Xjhas_ty [Xji Xij ] ] ] ] ].
  destruct Y1Y2 as [Yi [Yj [Yihas_ty [Yjhas_ty [Yji Yij ] ] ] ] ].

  exists (fun f => fun x => Yi (f (Xj x))).
  exists (fun f => fun x => Yj (f (Xi x))).
  repeat (split; simpl; intuition).
Qed.

(* Sum *)
Lemma iso_sum_cong (X1 X2 Y1 Y2 : Ty D) : X1 ~= X2 -> Y1 ~= Y2 -> X1 + Y1 ~= X2 + Y2.
Proof.
  unfold iso, Id. simpl. 
  intros X1X2 Y1Y2.
  destruct X1X2 as [Xi [Xj [Xihas_ty [Xjhas_ty [Xji Xij ] ] ] ] ].
  destruct Y1Y2 as [Yi [Yj [Yihas_ty [Yjhas_ty [Yji Yij ] ] ] ] ].

  exists (fun s => match s with inl l => inl _ (Xi l) | inr r => inr _ (Yi r) end).
  exists (fun s => match s with inl l => inl _ (Xj l) | inr r => inr _ (Yj r) end).
  split.
  intro psi.
  case => x. case => y; intuition. case => x'; intuition. 
  split.
  intro psi.
  case => x. case => y; intuition. case => x'; intuition. 
  split.  
  intro psi.
  case => x. case => y; intuition. case => y; intuition.
  intro psi. 
  case => x. case => y; intuition. case => y; intuition.
Qed.

Lemma iso_all_cong : X' ~= Y' -> TyAll X' ~= TyAll Y'.
Proof.
  unfold iso, Id. simpl. 
  intros X'Y'.
  destruct X'Y' as [i [j [ihas_ty [jhas_ty [ji ij ] ] ] ] ].

  exists i, j; intuition.   
Qed.

(*---------------------------------------------------------------------------
   Pushing quantifiers through type constructors
   ---------------------------------------------------------------------------*)
(* Arrows *)
Lemma iso_all_arrow : TyAll (apSubTy (pi _ _) X --> Y') ~= (X --> TyAll Y').
Proof.
  unfold iso, Id. simpl. 
  exists (fun f x => f (up _ x)).
  exists (fun f x => f (dn x)).  
  split.
  intros psi f f' ff' x x' xx' psi' H EXT.
  apply (ff' _ H EXT).  
  have SS:= @semSubst sig interpPrim ES A CLOSED D X (s::D) (pi D s) psi' H x x'.  
  rewrite SS. 
  rewrite /ext in EXT. 
  rewrite EXT. 
  apply xx'. 

  split.
  intros psi f f' ff' psi' H EXT x x' xx'. 
  have SS:= @semSubst sig interpPrim ES A CLOSED D X (s::D) (pi D s) psi' H (dn x) (dn x').  
  specialize (ff' (dn x) (dn x')). 
  apply ff' => //. rewrite EXT in SS. rewrite -SS. 
  rewrite 2!updn. apply xx'. 

  split.
  intros psi f f' ff' psi' H EXT x x' xx'.
  rewrite updn.
  intuition.

  intros psi f f' ff' x x' x'' psi' H EXT.
  rewrite dnup. intuition.
Qed.

(* Products *)
Lemma iso_all_prod : TyAll (X' * Y') ~= TyAll X' * TyAll Y'. 
Proof.
  unfold iso, Id. simpl.
  exists (fun p => p). 
  exists (fun p => p). 
  split. 
  intros. split. intros psi' ESS EXT. specialize (H psi' ESS EXT). apply (proj1 H). 
  intros psi' ESS EXT. apply (proj2 (H psi' ESS EXT)). 
  split.
  intros. destruct H.  auto. 
  split. auto. auto. 
Qed.

(* Elimination of redundant quantifiers *)
Lemma iso_all_redundant : TyAll (apSubTy (pi _ s) X) ~= X.
Proof.
  unfold iso, Id. simpl. 
  exists (fun x => dn x). 
  exists (fun x => up _ x).  
  split.
  intros psi x x' xx'.
Admitted.
(* We need a way of lifting RelEnv D to RelEnv (s::D) *)
(*  specialize (xx' (psi o DOWN _) (SEnvDown _)). 
  assert (DOWN _ o @SHIFT n = Hom.Id). apply HomExtensional. intros u. simpl. rewrite downShift. auto.  
  rewrite <- (Compose_id_r psi). rewrite <- H. rewrite Compose_assoc. 
  admit. (*rewrite SEnvSubstSem. repeat rewrite updn. auto.  *)
  
  split. 
  intros psi x x' xx' psi' ext.  rewrite <- SEnvSubstSem. rewrite (proj1 (SEnvExtendsDef _ _) ext). auto. 
  
  split. 
  intros psi x x' xx' psi' ext.  rewrite updn. apply xx'. auto. 
  intros psi x x' xx'. rewrite dnup. auto. 
Qed.*)


(*---------------------------------------------------------------------------
   Arithmetic-style isomorphisms
   ---------------------------------------------------------------------------*)
(* Product is commutative *)
Lemma iso_prod_comm : X*Y ~= Y*X.
  exists (fun p => (p.2,p.1)).
  exists (fun p => (p.2,p.1)).
  simpl; intuition. 
Qed.

(* Product is associative *)
Lemma iso_prod_assoc : X*(Y*Z) ~= (X*Y)*Z.
  exists (fun p => ((p.1, p.2.1), p.2.2)).
  exists (fun p => (p.1.1, (p.1.2, p.2))).
  simpl; intuition.
Qed.

(* Unit is a right unit for product *)
Lemma iso_prod_unit : X*(TyUnit _) ~= X.
  exists (fun p => p.1).
  exists (fun x => (x,tt)).
  simpl;intuition.
Qed.

(* Sum is commutative *)
Lemma iso_sum_comm : X+Y ~= Y+X.
  exists (fun s  => match s with inl x => @inr _ _ x | inr y => @inl _ _ y end).
  exists (fun s => match s with inl x => @inr _ _ x | inr y => @inl _ _ y end).
  simpl. simpl in *. 
  split. intro psi. destruct x'. destruct y'; intuition. destruct y'; intuition.
  split. intro psi. destruct x'. destruct y'; intuition. destruct y'; intuition.
  split. intro psi. destruct x'. destruct y'; intuition. destruct y'; intuition.
         destruct x'. destruct y'; intuition. by destruct y'. 
Qed.

(* Sum is associative *)
Lemma iso_sum_assoc : X+(Y+Z) ~= (X+Y)+Z.
Proof.
  exists (fun s => 
          match s with 
          | inl x => @inl _ _ (@inl _ _ x) 
          | inr yz => match yz with inl y => @inl _ _ (@inr _ _ y) | inr z => @inr _ _ z end end).
  exists (fun s  =>
          match s with
          | inl xy => match xy with inl x => @inl _ _ x | inr y => @inr _ _ (@inl _ _ y) end
          | inr z => @inr _ _ (@inr _ _ z) end).
  simpl. 
  split. intro psi. destruct x'. destruct y'; intuition. destruct y'; intuition.
    destruct s1. destruct s0; intuition. destruct s0; intuition. 
  split. intro psi. destruct x'. destruct y'; intuition. destruct s1; intuition. destruct s0; intuition. destruct s0; intuition.
  destruct y'; intuition.

  split. intro psi. destruct x'.  destruct y'; intuition. destruct y'; intuition. destruct s0; intuition. 
  destruct x'; intuition.
Qed.


Definition Weird : interpTy interpPrim X + False -> interpTy interpPrim X. 
intros. destruct X0. assumption. done. 
Defined.

(* Void is a right unit for sum *)
(*
Lemma iso_sum_zero : X + Void ~= X.
Proof. 
  unfold iso. fold usem.
  exists Weird. 
  exists (fun x : usem X => @inl _ _ x).
  split. Unfoldsem2.  intros psi x y. destruct x; destruct y. simpl. auto. destruct f. destruct f. destruct f. 
  split. Unfoldsem2. intros. auto. 
  split. Unfoldsem2. intros. destruct x; destruct y; auto. destruct f.
  Unfoldsem2.  intros. simpl. auto. 
Qed.
*)

(* Product distributes over sum *)
(* Annoyingly, can't get proof through if we pattern match on product; need to use fst/snd *)
Lemma iso_prod_sum : X*(Y+Z) ~= X*Y + X*Z.
  exists (fun p  =>
        match snd p with
        | inl y => inl _ (p.1, y)
        | inr z => inr _ (p.1, z) end).
  exists (fun s =>
        match s with
        | inl p => (p.1, inl _ p.2)
        | inr p => (p.1, inr _ p.2) end).

  simpl. 
  split.
  
  intros psi [p1 p2] [q1 q2] H.
  simpl.   
  destruct p2; destruct q2; intuition. 
  
  split. 
  
  intros psi s1 s2 H. 
  destruct s1; destruct s2; intuition. 

  split. 

  destruct x'; intuition. 
  destruct x'; intuition. 
Qed.

(* Exponential of a sum *)
Lemma iso_sum_arrow : (X+Y)-->Z ~= (X-->Z)*(Y-->Z).
Proof.
  exists (fun f =>
         (fun a => f (@inl _ _ a), fun b => f (@inr _ _ b))).
  exists (fun p =>
          fun s => 
          match s with inl a => (fst p) a | inr b => (snd p) b end).

  simpl. 

  split.
  intros psi f g. simpl. intuition. 
  split. intros psi f g fg. simpl. case. move => a.  case; intuition. move => b. case; intuition. 
  split. intuition. 
  split. intuition. 
  intuition. 
Qed.

(* Currying *)
Lemma iso_curry : (X*Y) --> Z ~= X --> Y --> Z.
Proof.
  exists (fun g => fun x => fun y => g (x,y)). simpl. 
  exists (fun f => fun p  => f (fst p) (snd p)).
  simpl; intuition. 
Qed.

Lemma iso_swaparg : X --> Y --> Z ~= Y --> X --> Z.
Proof.
  exists (fun f => fun x => fun y => f y x).
  exists (fun f => fun x => fun y => f y x).
  simpl; intuition. 
Qed.

(* Exponential of unit *)
Lemma iso_arrow_unit : X --> TyUnit _ ~= TyUnit _.
Proof.
  exists (fun f => tt).
  exists (fun _ : unit => fun _ => tt).
  simpl; intuition. 
Qed.

(* Unit exponential *)
Lemma iso_unit_arrow : TyUnit _ --> X ~= X.
Proof.
  exists (fun f  => f tt).
  exists (fun x  => fun _:unit => x). 
  simpl; intuition. 
Qed.

(* Exponential of product *)
Lemma iso_arrow_prod : Z --> (X*Y) ~= (Z-->X) * (Z-->Y).
Proof.
  exists (fun f  => (fun z => fst (f z), fun z => snd (f z))).
  exists (fun p  => fun z => (fst p z, snd p z)).
  simpl; intuition. 
  simpl; intuition; apply (H _ _ H0).  
  simpl; intuition; apply (H _ _ H0).  
Qed.

End StandardIsos.


End Iso.