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

Variable Gops : @Ctxt sig [::].
Variable eta_ops : interpCtxt interpPrim Gops.

Fixpoint mkArrTy D (G : @Ctxt sig D) (t : Ty D) : Ty D :=
  if G is s::G then mkArrTy G (TyArr s t) else t.

Fixpoint mkLamTm D (G G': @Ctxt sig D) (t: Ty D) : Tm A (G ++ G') t -> Tm A G' (mkArrTy G t) :=
  if G is t'::G 
  then fun M => mkLamTm (ABS M) 
  else fun M => M. 

Fixpoint mkForallTy (D : IxCtxt sig) : Ty D -> Ty [::] :=
  if D is s::D 
  then fun t => mkForallTy (TyAll t) 
  else fun t => t.

Fixpoint piAll (D : IxCtxt sig) : Sub [::] D :=
  if D is s::D
  then ScS (pi D s) (piAll D)
  else idSub [::]. 

Lemma tmEqCtxt (G : Ctxt [::]) (t : Ty [::]) :
      Tm A (apSubCtxt (piAll [::]) G) t = Tm A G t.
Proof. 
  by rewrite apSubCtxtId.
Qed.

Lemma tmEq2 D (G : Ctxt [::]) s (t : Ty (s :: D)) :
  Tm A (apSubCtxt (piAll (s :: D)) G) t = Tm A (apSubCtxt (pi D s) (apSubCtxt (piAll D) G)) t.
Proof.
  simpl. rewrite -(apSubCtxtScS (pi D s) (piAll D)). reflexivity.
Qed.

Fixpoint mkForallTm (D : IxCtxt sig) (G : @Ctxt sig [::]) :
  forall t : Ty D, Tm A (apSubCtxt (piAll D) G) t -> Tm A G (mkForallTy t) :=
  match D return forall t : Ty D, @Tm sig A D (apSubCtxt (piAll D) G) t -> @Tm sig A [::] G (mkForallTy t) with
    | nil    => fun t M => M :? tmEqCtxt G t
    | s :: D => fun t M => mkForallTm (@UNIVABS sig A D (apSubCtxt (piAll D) G) s _ (M :? tmEq2 G t))
  end.

Definition tyBool D : @Ty sig D := TySum (TyUnit D) (TyUnit D).

Definition ctxtEq D (G : Ctxt D) (t : Ty D) (M1 M2 : Tm A (G ++ (apSubCtxt (piAll D) Gops)) t) :=
  forall (T : @Tm sig A [::] Gops (mkForallTy (mkArrTy G t) --> tyBool [::])%Ty), 
    let M1' := mkForallTm (mkLamTm M1) in
    let M2' := mkForallTm (mkLamTm M2) in
    interpTm (APP T M1') eta_ops = interpTm (APP T M2') eta_ops.

Fixpoint app_env D (G G' : Ctxt D) :
  interpCtxt interpPrim G -> interpCtxt interpPrim G' -> interpCtxt interpPrim (G ++ G') :=
  match G return interpCtxt interpPrim G -> interpCtxt interpPrim G' -> interpCtxt interpPrim (G ++ G') with
    | nil    => fun eta1 eta2 => eta2
    | s :: G => fun eta1 eta2 => (eta1.1, app_env eta1.2 eta2)
  end.


(* Underlying equivalence, sound for contextual equivalence and sometimes useful *)
Definition usemEq D (G : Ctxt D) (t : Ty D) (M1 M2 : Tm A (G ++ apSubCtxt (piAll D) Gops) t) :=
  forall eta,
   interpTm M1 (app_env eta (eta_ops :? interpSubCtxt interpPrim Gops (piAll D))) =
   interpTm M2 (app_env eta (eta_ops :? interpSubCtxt interpPrim Gops (piAll D))).

Lemma mkArrTy_usem D G :
  forall t (M1 M2 : Tm A (G ++ (apSubCtxt (piAll D) Gops)) t),
    (forall (eta : interpCtxt interpPrim G),
         (interpTm M1 (app_env eta (eta_ops :? interpSubCtxt interpPrim Gops (piAll D)))) =
         (interpTm M2 (app_env eta (eta_ops :? interpSubCtxt interpPrim Gops (piAll D))))) ->
         (interpTm (mkLamTm M1) (eta_ops :? interpSubCtxt interpPrim Gops (piAll D))) =
         (interpTm (mkLamTm M2) (eta_ops :? interpSubCtxt interpPrim Gops (piAll D))).
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
  forall (t : Ty D) (M1 M2 : Tm A (apSubCtxt (piAll D) Gops) t),
  (               (interpTm M1 (eta_ops :? interpSubCtxt interpPrim Gops (piAll D))) =
                  (interpTm M2 (eta_ops :? interpSubCtxt interpPrim Gops (piAll D)))) ->
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



Theorem usemEq_implies_ctxtEq D (G : Ctxt D) (t : Ty D) (M1 M2 : Tm A (G ++ (apSubCtxt (piAll D) Gops)) t):
  usemEq M1 M2 ->
  ctxtEq M1 M2.
Proof.
  rewrite /usemEq /ctxtEq.
  move => M1_usemEq_M2 T.
  simpl. 
  apply f_equal.
  apply mkForallTy_usem. 
  apply mkArrTy_usem. intuition. 
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

Lemma ctxtEq_pair D (G: Ctxt D) (t1 t2: Ty D) (M1 M1': Tm A (G ++ _) t1) (M2 M2': Tm A (G ++ _) t2) : ctxtEq M1 M1' -> ctxtEq M2 M2' -> ctxtEq (PAIR M1 M2) (PAIR M1' M2'). 
Proof. move => EQ1 EQ2. 
move => C. 
simpl. 
rewrite /ctxtEq.
set C1 (*:@Tm sig A [::] Gops (mkForallTy (mkArrTy G (t1*t2)) --> tyBool [::])%Ty *) := 
  (*ABS *) (APP C (mkForallTm (mkLamTm (PAIR M1 M2)))). 
rewrite /ctxtEq in EQ1.
apply f_equal. 
apply mkForallTy_usem. 
apply mkArrTy_usem => eta. 
Admitted.

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
Variable Gops : Ctxt (sig:=sig) nil.
Variable eta_ops : interpCtxt interpPrim Gops.

Notation "| t |" := (interpTy interpPrim t).

Definition Id D (t:Ty D) := fun (x:|t|) => x.
Implicit Arguments Id [D]. 

Notation "G |- x =~= y :> t" := (@ctxtEq sig A interpPrim Gops eta_ops _ G t x y) (at level 67, x at level 67,y at level 67).

Definition iso D (X Y: Ty D) := 
  exists i : Tm A (apSubCtxt (piAll D) Gops) (TyArr X Y), 
  exists j : Tm A (apSubCtxt (piAll D) Gops) (TyArr Y X),
  (forall M : Tm A (apSubCtxt (piAll D) Gops) X,
  [::] |- APP j (APP i M) =~= M :> X) /\
  (forall M : Tm A (apSubCtxt (piAll D) Gops) Y,
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

(* Need shifting on terms wrt term variables *)
Lemma iso_tran D (X Y Z: Ty D) : iso X Y -> iso Y Z -> iso X Z.
Proof. 
move => [i1 [j1 [ij1 ji1]]] [i2 [j2 [ij2 ji2]]]. 
exists (ABS (APP (shTmTm _ i2) (APP (shTmTm _ i1) ##0))). 
exists (ABS (APP (shTmTm _ j1) (APP (shTmTm _ j2) ##0))). 
split => M. rewrite /ctxtEq => C. 
specialize (ij2 (APP i1 M)). 
rewrite /ctxtEq in ij2.
simpl. 
apply f_equal => //. 
apply mkForallTy_usem. 
simpl. set MM := interpTm M _. set EE := eta_ops :? _.
Admitted.
(* 
simpl. apply f_equal2 => //.

simpl. 
simpl in ij2.  
rewrite ij2. apply f_equal2 in ij2. simpl. set EO := (eta_ops :? _). apply f_equal2. 
firstorder. apply f_equal in ij2. rewrite ij2. 
apply mkArrTy_usem. 
rewrite interpTm_specialize (ij2 (APP C (mkForallTm (mkLamTm (APP j1 ##0))))). mkforalltm (mklamtm (APP (shTmTm Z j1 (APP C _))). specialize (ij2 C). 
specialize (ji2 ij2). 
(shTmTm _ i1) (shTmTm _ M))). 
specialize (ij1 M C).
apply usemEq_implies_ctxtEq. rewrite /usemEq => eta. rewrite cast_UIP.  admit. 
move => H. simpl. 
simpl in ij1. 
 rewrite ij1. simpl. apply f_equal. specialize (ji2 M T).
rewrite /ctxtEq in ij1. specialize (ij1 T). simpl in ij1. simpl. rewrite ij1. simpl in ij1. apply usemEq_implies_ctxtEq in ij1.  
simpl in ij1. simpl in ij1. rewrite ij1. 
rewrite cast_UIP.  
set P := interpTm _ _.
simpl. rewrite ij1. done. 
Lemma iso_prod_comm D (X Y: Ty D) : iso (X*Y) (Y*X). 
Proof. rewrite /iso. 
exists (ABS (PAIR (PROJ2 ##0) (PROJ1 ##0))). 
exists (ABS (PAIR (PROJ2 ##0) (PROJ1 ##0))). 
split => M; apply usemEq_implies_ctxtEq; rewrite /usemEq => eta/=; set P := interpTm _ _. 
  by case: P.
  by case: P.
Qed. 
*)

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

(*
Lemma iso_all_cong D s (X Y: Ty (s::D)) : iso X Y -> iso (TyAll X) (TyAll Y).
Proof.
move => [i [j [ij ji]]].   
exists (ABS (APP (shTmTm _ i) ##0)).
exists (ABS (APP (shTmTm _ j) ##0)).  
Qed. 
*)

Lemma iso_prod_cong D (W X Y Z: Ty D) : iso W X -> iso Y Z -> iso (W * Y) (X * Z).
Proof. rewrite /iso. move => [i1 [j1 [ij1 ji1]]] [i2 [j2 [ij2 ji2]]].
(* We want to write this but we need to shift i1 and i2 with respect to *term* variables *)
exists (ABS (PAIR (APP (shTmTm _ i1) (PROJ1 ##0)) (APP (shTmTm _ i2) (PROJ2 ##0)))). 
exists (ABS (PAIR (APP (shTmTm _ j1) (PROJ1 ##0)) (APP (shTmTm _ j2) (PROJ2 ##0)))).
Admitted. 

(*split => M; apply usemEq_implies_ctxtEq; rewrite /usemEq => eta/=; set P := interpTm _ _.
 rewrite cast_UIP. admit. 
  move => H. done. rewrite cast_id. coalesce. UIP.  simpl. by rewrite apSubCtxtId.
rewrite cast_UIP. 
simpl. case: P => [P1 P2]. 
*)

End Iso. 


