Require Import ssreflect ssrbool ssrfun seq.
Require Import Relations Program.Equality.
Require Import FunctionalExtensionality.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import exp ty sem Casts.

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

(* 
Definition mkForallTm (D : IxCtxt sig) (G : @Ctxt sig [::]) :
  forall t : Ty D, Tm A (apSubCtxt (piAll D) G) t -> Tm A G (mkForallTy t).
induction D.
 simpl. rewrite apSubCtxt_id. trivial.
 simpl. move => t' tm.
  apply IHD. apply UNIVABS. rewrite ScS_apSubCtxt. apply tm.
Defined.
*)

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
  forall (T : @Tm sig A [::] Gops (TyArr (mkForallTy (mkArrTy G t)) (tyBool [::]))), 
    let M1' := mkForallTm (mkLamTm M1) in
    let M2' := mkForallTm (mkLamTm M2) in
    interpTm (APP T M1') eta_ops = interpTm (APP T M2') eta_ops.

(* And now, semantic equivalence *)
Variable ME : ModelEnv interpPrim A.

Fixpoint app_env D (G G' : Ctxt D) :
  interpCtxt interpPrim G -> interpCtxt interpPrim G' -> interpCtxt interpPrim (G ++ G') :=
  match G return interpCtxt interpPrim G -> interpCtxt interpPrim G' -> interpCtxt interpPrim (G ++ G') with
    | nil    => fun eta1 eta2 => eta2
    | s :: G => fun eta1 eta2 => (eta1.1, app_env eta1.2 eta2)
  end.

Definition semEq D (G : Ctxt D) (t : Ty D) (M1 M2 : Tm A (G ++ apSubCtxt (piAll D) Gops) t) :=
  forall rho eta1 eta2,
   semCtxt (ME:=ME) rho eta1 eta2 ->
   semTy rho (interpTm M1 (app_env eta1 (eta_ops :? interpSubCtxt interpPrim Gops (piAll D))))
             (interpTm M2 (app_env eta2 (eta_ops :? interpSubCtxt interpPrim Gops (piAll D)))).

Lemma mkArrTy_rel D (rho : RelEnv ME D) G :
  forall t (M1 M2 : Tm A (G ++ (apSubCtxt (piAll D) Gops)) t),
    (forall (eta1 eta2 : interpCtxt interpPrim G),
       semCtxt rho eta1 eta2 ->
       semTy rho
         (interpTm M1 (app_env eta1 (eta_ops :? interpSubCtxt interpPrim Gops (piAll D))))
         (interpTm M2 (app_env eta2 (eta_ops :? interpSubCtxt interpPrim Gops (piAll D))))) ->
    semTy rho
         (interpTm (mkLamTm M1) (eta_ops :? interpSubCtxt interpPrim Gops (piAll D)))
         (interpTm (mkLamTm M2) (eta_ops :? interpSubCtxt interpPrim Gops (piAll D))).
Proof.
  induction G => t' M1 M2 M1_M2.
   (* nil *)
   apply (M1_M2 tt tt).
   exact Logic.I. 
   (* cons *)
   simpl. apply IHG. 
   simpl. move => eta1 eta2 eta1_eta2 x x' x_x'.
   apply (M1_M2 (x,eta1) (x',eta2)).
   split. apply x_x'. apply eta1_eta2.
Qed.

Lemma mkForallTy_rel D :
  forall (t : Ty D) (M1 M2 : Tm A (apSubCtxt (piAll D) Gops) t),
  (forall rho,
     semTy (ME:=ME) rho (interpTm M1 (eta_ops :? interpSubCtxt interpPrim Gops (piAll D)))
                  (interpTm M2 (eta_ops :? interpSubCtxt interpPrim Gops (piAll D)))) ->
  forall rho,
    semTy (ME:=ME) rho (interpTm (mkForallTm M1) eta_ops)
                 (interpTm (mkForallTm M2) eta_ops).
Proof.
  induction D => t' M1 M2 H rho.
   (* nil *)
   simpl. 
   specialize (H rho).
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
   move => rho' k. 
   specialize (H (k,rho')).
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

Lemma tyBool_rel D (b1 b2 : interpTy interpPrim (tyBool D)) (rho: RelEnv ME D) :
  semTy rho b1 b2 ->
  b1 = b2.
Proof. destruct b1 as [[]|[]]; destruct b2 as [[]|[]]; intuition. Qed.

Variable rho_nil : RelEnv ME [::].
Variable eta_ops_rel : semCtxt rho_nil eta_ops eta_ops.

Theorem semEq_implies_ctxtEq D (G : Ctxt D) (t : Ty D) (M1 M2 : Tm A (G ++ (apSubCtxt (piAll D) Gops)) t):
  semEq M1 M2 ->
  ctxtEq M1 M2.
Proof.
  rewrite /semEq /ctxtEq.
  move => M1_semEq_M2 T.
  assert (T_rel_T : semTy rho_nil (interpTm T eta_ops) (interpTm T eta_ops)). apply Abstraction => //. 
  apply tyBool_rel with (rho:=rho_nil).
  apply T_rel_T.
  apply mkForallTy_rel.
  move => rho. apply mkArrTy_rel.
  intuition. 
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



End ContextualEquivalence.

