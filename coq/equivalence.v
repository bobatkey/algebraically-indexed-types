Require Import ssreflect ssrbool ssrfun seq.
Require Import Relations Program.Equality.
Require Import FunctionalExtensionality.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import syn sem Casts.

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

Lemma apSubTy_id D (t : @Ty sig D) : apSubTy (idSub D) t = t.
Proof.
  induction t => /=.
  + by reflexivity.
  + by rewrite IHt1 IHt2. 
  + by rewrite IHt1 IHt2. 
  + by rewrite IHt1 IHt2. 
  + by rewrite (proj2 (apSubId D)).
  + by rewrite liftSubId IHt. 
  + by rewrite liftSubId IHt. 
Qed.

Lemma apSubCtxt_id D (G : @Ctxt sig D) : apSubCtxt (idSub D) G = G.
Proof.
  induction G => /=.
  + by reflexivity.
  + by rewrite IHG apSubTy_id.
Qed.

Lemma ScS_apSubTy D (t : @Ty sig D) : 
  forall D' D'' (S : Sub D' D'') (S' : Sub D D'),
    apSubTy S (apSubTy S' t) = apSubTy (ScS S S') t.
Proof.
 induction t => D' D'' S S' => /=.
 + by reflexivity.
 + by rewrite IHt1 IHt2.
 + by rewrite IHt1 IHt2.
 + by rewrite IHt1 IHt2.
 + by rewrite (proj2 (apScS S S')).
 + by rewrite IHt liftScS. 
 + by rewrite IHt liftScS. 
Qed.

Lemma ScS_apSubCtxt D D' D'' (S : Sub D' D'') (S' : Sub D D') (G : @Ctxt sig D) :
  apSubCtxt S (apSubCtxt S' G) = apSubCtxt (ScS S S') G.
Proof.
  induction G => /=. 
  + by reflexivity.
  + by rewrite IHG ScS_apSubTy.
Qed.
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
  by rewrite apSubCtxt_id.
Qed.

Lemma tmEq2 D (G : Ctxt [::]) s (t : Ty (s :: D)) :
  Tm A (apSubCtxt (piAll (s :: D)) G) t = Tm A (apSubCtxt (pi D s) (apSubCtxt (piAll D) G)) t.
Proof.
  simpl. rewrite -ScS_apSubCtxt. reflexivity.
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
Variable ES : RelEnvSet interpPrim.
Variable SUBST : Substitutive ES.
Variable RESPECTFUL : Respectful A ES. 

Fixpoint app_env D (G G' : Ctxt D) :
  interpCtxt interpPrim G -> interpCtxt interpPrim G' -> interpCtxt interpPrim (G ++ G') :=
  match G return interpCtxt interpPrim G -> interpCtxt interpPrim G' -> interpCtxt interpPrim (G ++ G') with
    | nil    => fun eta1 eta2 => eta2
    | s :: G => fun eta1 eta2 => (eta1.1, app_env eta1.2 eta2)
  end.

Definition semEq D (G : Ctxt D) (t : Ty D) (M1 M2 : Tm A (G ++ apSubCtxt (piAll D) Gops) t) :=
  forall rho eta1 eta2,
    ES rho -> 
    semCtxt ES rho eta1 eta2 ->
    semTy ES rho (interpTm M1 (app_env eta1 (eta_ops :? interpSubCtxt interpPrim Gops (piAll D))))
                 (interpTm M2 (app_env eta2 (eta_ops :? interpSubCtxt interpPrim Gops (piAll D)))).

Lemma mkArrTy_rel D (rho : RelEnv interpPrim D) (_ : ES rho) G :
  forall t (M1 M2 : Tm A (G ++ (apSubCtxt (piAll D) Gops)) t),
    (forall (eta1 eta2 : interpCtxt interpPrim G),
       semCtxt ES rho eta1 eta2 ->
       semTy ES rho
         (interpTm M1 (app_env eta1 (eta_ops :? interpSubCtxt interpPrim Gops (piAll D))))
         (interpTm M2 (app_env eta2 (eta_ops :? interpSubCtxt interpPrim Gops (piAll D))))) ->
    semTy ES rho
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
     ES rho ->
     semTy ES rho (interpTm M1 (eta_ops :? interpSubCtxt interpPrim Gops (piAll D)))
                  (interpTm M2 (eta_ops :? interpSubCtxt interpPrim Gops (piAll D)))) ->
  forall rho,
    ES rho ->
    semTy ES rho (interpTm (mkForallTm M1) eta_ops)
                 (interpTm (mkForallTm M2) eta_ops).
Proof.
  induction D => t' M1 M2 H rho ES_rho.
   (* nil *)
   simpl. 
   specialize (H rho ES_rho).
   revert M1 M2 H.
   rewrite cast_UIP. by rewrite apSubCtxt_id.
   move => H M1 M2.
   rewrite (cast_UIP M1). by rewrite apSubCtxt_id.
   move => H1.
   rewrite (cast_UIP M2). 
   revert H M1 M2 H1. rewrite apSubCtxt_id.
   move => H M1 M2 H1. rewrite 3!cast_id. trivial.
   (* cons *)
   apply IHD.
   simpl. 
   move => rho' ES_rho' rho'' ES_rho'' rho'_rho''. 
   specialize (H rho'' ES_rho'').
   rewrite cast_coalesce. 
   revert M1 M2 H.
   rewrite cast_UIP. apply interpSubCtxt. 
   rewrite cast_UIP. rewrite ScS_apSubCtxt. apply interpSubCtxt. 
   move => H1 H2 M1 M2.
   rewrite (cast_UIP M1). rewrite ScS_apSubCtxt. reflexivity.
   move => H3.
   rewrite (cast_UIP M2).
   revert H1 H2 H3 M1 M2.
   rewrite ScS_apSubCtxt.
   move => H1 H2 H3 M1 M2.
   rewrite (cast_UIP eta_ops H1 H2). 
   rewrite 2!cast_id. trivial.

   assumption.
Qed.

Lemma tyBool_rel D (b1 b2 : interpTy interpPrim (tyBool D)) rho :
  semTy ES rho b1 b2 ->
  b1 = b2.
Proof.
  simpl. destruct b1 as [[]|[]]; destruct b2 as [[]|[]]; intuition.
Qed.

Variable rho_nil : RelEnv interpPrim [::].
Variable ES_rho_nil : ES rho_nil.
Variable eta_ops_rel : semCtxt ES rho_nil eta_ops eta_ops.

Theorem semEq_implies_ctxtEq D (G : Ctxt D) (t : Ty D) (M1 M2 : Tm A (G ++ (apSubCtxt (piAll D) Gops)) t):
  semEq M1 M2 ->
  ctxtEq M1 M2.
Proof.
  rewrite /semEq /ctxtEq.
  move => M1_semEq_M2 T.
  assert (T_rel_T : semTy ES rho_nil (interpTm T eta_ops) (interpTm T eta_ops)). apply Abstraction => //. 
  apply tyBool_rel with (rho:=rho_nil).
  apply T_rel_T.
  apply mkForallTy_rel.
  move => rho ES_rho. apply mkArrTy_rel.
   assumption.
   intuition. apply ES_rho_nil.
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

