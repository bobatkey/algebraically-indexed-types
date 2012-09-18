Require Import ssreflect ssrbool ssrfun seq eqtype ssralg.
Require Import ssrint rat ssrnum. 

Require Import Relations.

Require Import syn model sem.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*---------------------------------------------------------------------------
   Syntactic theory of scalings
   ---------------------------------------------------------------------------*)
Inductive ExSrt := Unit.
Inductive ExPrimType := TyReal.
Inductive ExIndexOp := UnitProd | UnitInv | UnitOne | UnitAbs.

Canonical ExSIG := mkSIG
  (fun i => match i with UnitProd => ([:: Unit; Unit], Unit)
                       | UnitInv => ([:: Unit], Unit)
                       | UnitOne => ([::], Unit) 
                       | UnitAbs => ([:: Unit], Unit) end)
  (fun t => match t with TyReal => [::Unit] end).


Definition unitExpr D := Exp D Unit.
Definition tyExpr D := Ty (sig:=ExSIG) D.

Definition unitOne D: unitExpr D  := 
  AppCon UnitOne (Nil _). 

Definition unitProd D (u1 u2: unitExpr D) : unitExpr D := 
  AppCon UnitProd (Cons u1 (Cons u2 (Nil _))).

Definition unitInv D (u: unitExpr D) : unitExpr D :=
  AppCon UnitInv (Cons u (Nil _)). 

Definition abs D (u: unitExpr D) : unitExpr D :=
  AppCon UnitAbs (Cons u (Nil _)). 

Notation "u '*' v" := (unitProd u v) (at level 40, left associativity) : Unit_scope. 
Notation "u ^-1" := (unitInv u) (at level 3, left associativity, format "u ^-1") : Unit_scope.
Notation "'one'" := (unitOne _). 
Delimit Scope Unit_scope with Un.

Definition real D (u: unitExpr D) : tyExpr D :=
  TyPrim TyReal (Cons u (Nil _)).  
Arguments Scope real [Unit_scope].

Definition allUnits D (t: tyExpr (Unit::D)) : tyExpr D := TyAll t. 

Notation "#0" := (VarAsExp (VarZ _ _)).
Notation "#1" := (VarAsExp (VarS _ (VarZ _ _))).
Notation "#2" := (VarAsExp (VarS _ (VarS _ (VarZ _ _)))).

Definition ExAxioms : seq (Ax ExSIG) :=
[::
  (* right identity *)
  [::Unit] |- #0 * one === #0;

  (* commutativity *)
  [::Unit;Unit] |- #0 * #1 === #1 * #0;

  (* associativity *)
  [::Unit;Unit;Unit] |- #0 * (#1 * #2) === (#0 * #1) * #2;

  (* right inverse *)
  [::Unit] |- #0 * #0^-1 === one;

  (* abs is a group homomorphism *)
  [::Unit;Unit] |- abs (#0 * #1) === abs #0 * abs #1
]%Un.

Definition uequiv D : relation (unitExpr D) := equiv (sig:=ExSIG) ExAxioms.

Definition Gops : Ctxt [::] := 
[::
  (* 0 *)
  allUnits (real #0);

  (* 1 *)
  real one;

  (* + *)
  allUnits (real #0 --> real #0 --> real #0);

  (* - *)
  allUnits (real #0 --> real #0 --> real #0);

  (* * *)
  allUnits (allUnits (real #0 --> real #1 --> real (#0 * #1)%Un));

  (* reciprocal *)
  allUnits (real #0 --> real #0^-1 + TyUnit _)%Un;

  (* abs *)
  allUnits (real #0 --> real (abs #0))
]%Ty.

(*---------------------------------------------------------------------------
   Underlying semantics
   ---------------------------------------------------------------------------*)

Variable F: numFieldType.
Definition interpPrim : PrimType ExSIG -> Type := fun _ => F. 

Definition eta_ops : interpCtxt interpPrim Gops :=
  (0%R,
  (1%R,
  (fun x y => (x + y)%R,
  (fun x y => (x - y)%R,
  (fun x y => (x * y)%R,
  (fun x => (if x==0 then inr _ tt else inl _ (1 / x))%R,
  (fun x => `|x|%R, 
  tt))))))).  


(*---------------------------------------------------------------------------
   Our first relational interpretation: scaling factors
   ---------------------------------------------------------------------------*)

(* Non-zero scale factor type *)
Structure scaling : Type := Scaling {tval :> F; _ : tval != 0%R}.

Canonical scaling_subType := Eval hnf in [subType for tval by scaling_rect].
Definition scaling_eqMixin := Eval hnf in [eqMixin of scaling by <:]. 
Canonical scaling_eqType := Eval hnf in EqType scaling scaling_eqMixin.  
Implicit Type t : scaling.

Lemma scaling_neq0 (x:scaling) : val x != 0%R. Proof. by elim x. Qed.

Lemma eqEquivalence (T:eqType) : equivalence _ (fun x y:T => x==y).
Proof. split. by move => x/=.   
move => x y z/= E1 E2. by rewrite (eqP E1) (eqP E2).
move => x y/= E1. by rewrite (eqP E1). 
Qed. 

Lemma scaling_inj (x y: scaling) : val x = val y -> x == y. 
Proof. by move /val_inj ->. Qed. 

(* Used to be nonzero1r *)
Definition scaling_one := Scaling (GRing.oner_neq0 _).
Definition scaling_prod (x y: scaling) : scaling :=
  Scaling (GRing.mulf_neq0 (scaling_neq0 x) (scaling_neq0 y)). 
Definition scaling_inv (x: scaling) : scaling :=
  Scaling (GRing.invr_neq0 (scaling_neq0 x)). 

Lemma normr_neq0 (x: F) : (x != 0 -> `|x| != 0)%R. 
Proof. by rewrite -2!Num.Theory.normr_gt0 Num.Theory.normr_id. Qed. 

Definition scaling_abs (x: scaling) : scaling :=
  Scaling (normr_neq0 (scaling_neq0 x)). 

Definition ScalingInterpretation := mkInterpretation
  (fun s => eqEquivalence scaling_eqType)
  (fun p =>
   match p with
     UnitOne  => fun args => scaling_one
   | UnitProd => fun args => scaling_prod args.1 args.2.1
   | UnitAbs  => fun args => scaling_abs args.1
   | UnitInv  => fun args => scaling_inv args.1
   end ).

Definition ScalingModel : Model ExAxioms. 
Proof. 
apply (@mkModel _ ExAxioms ScalingInterpretation). 
split. 
(* right identity *)
move => /= [x u] /=.
apply scaling_inj. by rewrite /= GRing.mulr1. 
split. 
(* commutativity *)
move => /= [x [y u]] /=. 
apply scaling_inj. by rewrite /= GRing.mulrC. 
split. 
(* associativity *)
move => /= [x [y [z u]]] /=. 
apply scaling_inj. by rewrite /= GRing.mulrA. 
split. 
(* right inverse *)
move => /= [x u] /=. 
apply scaling_inj. rewrite /= GRing.mulrV => //. 
elim x => [x' neq]. by rewrite GRing.unitfE neq. 
split.
(* homomorphism of abs *)
move => /= [x [y u]] /=.
apply scaling_inj. by rewrite /= Num.Theory.normrM. 
(* end *)
done. 
Defined. 

Definition ScalingModelEnv := mkModelEnv (interpPrim := interpPrim) (M:=ScalingModel)
  (fun X => 
    match X with TyReal => 
    fun realArgs => 
    fun x y => y = (val realArgs.1 * x)%R end). 

Definition ScalingModelRelSet := modelRelSet ScalingModelEnv.

Definition scalingSemTy := semTy ScalingModelRelSet.

Definition initialScalingEnv: RelEnv interpPrim [::] := 
  modelRel (D:=[::]) (ME:=ScalingModelEnv) tt. 

(* Interpretation of pervasives preserve scaling relations *)
Lemma eta_ops_ok : semCtxt ScalingModelRelSet initialScalingEnv eta_ops eta_ops.
Proof.
split. 
(* 0 *)
move => rho' MEM EXT.
rewrite /ScalingModelRelSet/modelRelSet/= in MEM. 
destruct MEM as [[k u] ->]. simpl. 
by rewrite GRing.mulr0. 
split.
(* 1 *)
rewrite /initialScalingEnv/=. by rewrite GRing.mulr1. 
split. 
(* + *)
move => rho' MEM EXT.
rewrite /ScalingModelRelSet/modelRelSet/= in MEM. 
destruct MEM as [[k u] ->]. simpl. 
move => x x' ->. 
move => y y' ->. 
by rewrite GRing.mulrDr. 
split. 
(* - *)
move => rho' MEM EXT.
rewrite /ScalingModelRelSet/modelRelSet/= in MEM. 
destruct MEM as [[k u] ->]. simpl. 
move => x x' ->. 
move => y y' ->. 
by rewrite GRing.mulrBr.
split. 
(* * *)
move => rho' MEM EXT.
rewrite /ScalingModelRelSet/modelRelSet/= in MEM. 
destruct MEM as [[k u] ->]. simpl. 
move => rho'' MEM' EXT'.
rewrite /ScalingModelRelSet/modelRelSet/= in MEM'. 
destruct MEM' as [[k'' [k' u']] ->]. simpl. 
move => x x' ->. 
move => y y' ->. 
elim k' => [k1 neq]/=. 
elim k'' => [k2 neq']/=. 
rewrite -2!(GRing.mulrA k2). 
by rewrite (GRing.mulrCA k1 x y). 
split. 
(* recip *)
move => rho' MEM EXT.
rewrite /ScalingModelRelSet/modelRelSet/= in MEM. 
destruct MEM as [[k u] ->]. simpl. 
move => x x' ->.
elim k => [k1 neq]/=. 
case E: (x == 0%R).
(* It's zero *)
+ by rewrite (eqP E) GRing.mulr0 eq_refl. 
(* It's not zero *)
+ apply negbT in E. 
have NEQ: (k1 * x)%R != 0%R by rewrite GRing.mulf_neq0.
apply negbF in NEQ. 
rewrite negbK in NEQ. 
rewrite NEQ.
rewrite (GRing.mulrC k1).  
rewrite !GRing.div1r. rewrite GRing.invrM. 
done. by rewrite GRing.unitfE E. 
by rewrite GRing.unitfE neq. 
split. 
(* abs *)
move => rho' MEM EXT.
rewrite /ScalingModelRelSet/modelRelSet/= in MEM. 
destruct MEM as [[k u] ->]. simpl. 
move => x x' ->. 
by rewrite Num.Theory.normrM. 
(* finish *)
done. 
Qed. 

(*---------------------------------------------------------------------------
   Our second relational interpretation: rational exponents
   We can use this to show non-definability results.
   The two interpretations could easily be combined (just pair them)
   ---------------------------------------------------------------------------*)

Definition ExpInterpretation := mkInterpretation
  (fun s => eqEquivalence rat_eqType)
  (fun p =>
   match p with
     UnitOne  => fun args => 0%R
   | UnitProd => fun args => (args.1 + args.2.1)%R
   | UnitAbs  => fun args => args.1
   | UnitInv  => fun args => (-args.1)%R
   end ).

Definition ExpModel : Model ExAxioms. 
Proof. 
apply (@mkModel _ ExAxioms ExpInterpretation). 
split. 
(* right identity *)
move => /= [x u] /=.
by rewrite /= GRing.addr0. 
split. 
(* commutativity *)
move => /= [x [y u]] /=.
by rewrite /= GRing.addrC. 
split. 
(* associativity *)
move => /= [x [y [z u]]] /=. 
by rewrite /= GRing.addrA.
split. 
(* right inverse *)
move => /= [x u] /=. 
by rewrite GRing.addrN. 
split.
(* homomorphism of abs *)
move => /= [x [y u]] /=.
done.
(* end *)
done. 
Defined. 

Definition ExpModelEnv := mkModelEnv (interpPrim := interpPrim) (M:=ExpModel)
  (fun X => 
    match X with TyReal => 
    fun expArgs => 
    fun x y => (x==0%R /\ y==0%R \/ (x == y%R /\ expArgs.1 \is a Qint)) end). 

Definition ExpModelRelSet := modelRelSet ExpModelEnv.

Definition expSemTy := semTy ExpModelRelSet.

Definition initialExpEnv: RelEnv interpPrim [::] := 
  modelRel (D:=[::]) (ME:=ExpModelEnv) tt. 

(* Interpretation of pervasives preserve exponent relations *)
Lemma eta_ops_okForExp : semCtxt ExpModelRelSet initialExpEnv eta_ops eta_ops.
Proof.
split. 
(* 0 *)
move => rho' MEM EXT.
rewrite /ExpModelRelSet/modelRelSet/= in MEM. 
destruct MEM as [[k u] ->]. simpl. 
intuition. 
split.
(* 1 *)
rewrite /initialExpEnv. simpl. 
by right. 
split. 
(* + *)
move => rho' MEM EXT.
rewrite /ExpModelRelSet/modelRelSet/= in MEM. 
destruct MEM as [[k u] ->]. simpl. 
move => x x'. elim. 
+ move => [H1 H2]. rewrite (eqP H1) (eqP H2).
  move => y y'. elim. 
  - move => [H3 H4]. rewrite (eqP H3) (eqP H4). rewrite !GRing.addr0. by intuition. 
  - move => [H3 H4]. rewrite (eqP H3). rewrite !GRing.add0r. by intuition. 
+ move => [H1 H2]. rewrite (eqP H1). 
  move => y y'. elim. 
  - move => [H3 H4]. rewrite (eqP H3) (eqP H4). rewrite !GRing.addr0. by intuition. 
  - move => [H3 H4]. rewrite (eqP H3). by intuition. 
split. 
(* - *)
move => rho' MEM EXT.
rewrite /ExpModelRelSet/modelRelSet/= in MEM. 
destruct MEM as [[k u] ->]. simpl. 
move => x x'. elim. 
+ move => [H1 H2]. rewrite (eqP H1) (eqP H2).
  move => y y'. elim. 
  - move => [H3 H4]. rewrite (eqP H3) (eqP H4). rewrite !GRing.subr0. by intuition. 
  - move => [H3 H4]. rewrite (eqP H3). rewrite !GRing.sub0r. by intuition. 
+ move => [H1 H2]. rewrite (eqP H1). 
  move => y y'. elim. 
  - move => [H3 H4]. rewrite (eqP H3) (eqP H4). rewrite !GRing.subr0. by intuition. 
  - move => [H3 H4]. rewrite (eqP H3). by intuition. 
split. 
(* * *)
move => rho' MEM EXT.
rewrite /ExpModelRelSet/modelRelSet/= in MEM. 
destruct MEM as [[k u] ->]. simpl. 
move => rho'' MEM' EXT'.
rewrite /ExpModelRelSet/modelRelSet/= in MEM'. 
destruct MEM' as [[k'' [k' u']] ->]. simpl. 
move => x x'. elim. 
+ move => [H1 H2]. rewrite (eqP H1) (eqP H2).
  move => y y'. elim. 
  - move => [H3 H4]. rewrite (eqP H3) (eqP H4). rewrite !GRing.mulr0. by intuition. 
  - move => [H3 H4]. rewrite (eqP H3). rewrite !GRing.mul0r. by intuition. 
+ move => [H1 H2]. rewrite (eqP H1). 
  move => y y'. elim. 
  - move => [H3 H4]. rewrite (eqP H3) (eqP H4). rewrite !GRing.mulr0. by intuition. 
  - move => [H3 H4]. rewrite (eqP H3). right. split => //.
    (* There has to be an easier way to do this; ask Georges *)
    move: H2 H4. 
    move/QintP=>[x1 ->]. 
    move/QintP=>[x2 ->]. apply/QintP. exists (x1 + x2)%R. by rewrite -GRing.rmorphD.  
split. 
(* recip *)
move => rho' MEM EXT.
rewrite /ExpModelRelSet/modelRelSet/= in MEM. 
destruct MEM as [[k u] ->]. simpl. 
move => x x'. elim. 
+ move => [H1 H2]. by rewrite (eqP H1) (eqP H2) (eq_refl _). 
+ move => [H1 H2]. rewrite (eqP H1). 
case E: (x' == 0%R) => //.
(* It's not zero *)
+ apply negbT in E. 
right. split => //. 
(* Again, there has to be an easier way to do this *)
move: H2. 
move/QintP=>[x1 ->]. 
apply/QintP. exists (-x1)%R. by rewrite -GRing.rmorphN.  
split. 
(* abs *)
move => rho' MEM EXT.
rewrite /ExpModelRelSet/modelRelSet/= in MEM. 
destruct MEM as [[k u] ->]. simpl. 
move => x x'. elim. 
+ move => [H1 H2]. rewrite (eqP H1) (eqP H2) (eq_refl _).
  rewrite !Num.Theory.normr_eq0.  intuition. 
+ move => [H1 H2]. rewrite (eqP H1). intuition. 
(* finish *)
done. 
Qed. 

(*---------------------------------------------------------------------------
   Now some applications.
   First we prove that the type of square root contains only \x.0
   ---------------------------------------------------------------------------*)

Definition sqrtTy : Ty [::] := allUnits (real (#0 * #0)%Un --> real #0)%Ty.

Open Scope ring_scope.
Lemma sqrtTrivial (f:F->F) (x:F) : 
  expSemTy (t:=sqrtTy) initialExpEnv f f -> 
  f x = 0.
Proof. move => /=H. 
set rho: RelEnv interpPrim [::Unit] := 
  modelRel (D:=[::Unit]) (ME:=ExpModelEnv) (1%:Q/2%:Q, tt). 
specialize (H rho). 
have ESrho: ExpModelRelSet rho by exists (1%:Q/2%:Q, tt).
specialize (H ESrho). 
have EXT: ext initialExpEnv rho.
rewrite /ext.
Require Import FunctionalExtensionality. 
apply functional_extensionality_dep => X.  
apply functional_extensionality => S.
rewrite /EcS. rewrite /rho. destruct X.
apply functional_extensionality => y. 
apply functional_extensionality => y'.
simpl. 
rewrite (proj1 (interpExpApSub _ _)).
done. 
specialize (H EXT x x).
rewrite /rho in H.  
simpl in H.
have H':   x == 0 /\ x == 0 \/ x == x /\ 1%:~R / 2%:~R + 1%:~R / 2%:~R \is a Qint by intuition. 
specialize (H H'). clear H'. 
destruct H. destruct H as [H1 H2]. by rewrite (eqP H1). 
destruct H as [H1 H2]. 
done. 
Qed. 

(*---------------------------------------------------------------------------
   Next we prove that the type of squaring exhibits a scaling property
   ---------------------------------------------------------------------------*)

Definition sqrTy : Ty [::] := allUnits (real #0 --> real (#0 * #0)%Un)%Ty.

Lemma sqrScaling (f:F->F) (k x:F) :   
  k != 0 ->
  scalingSemTy (t:=sqrTy) initialScalingEnv f f -> 
  f (k * x) = k^2 * f x.
Proof. move => neq /=H. 
set rho: RelEnv interpPrim [::Unit] := 
  modelRel (D:=[::Unit]) (ME:=ScalingModelEnv) (Scaling neq, tt). 
specialize (H rho). 
have ESrho: ScalingModelRelSet rho by exists (Scaling neq, tt).
specialize (H ESrho). 
have EXT: ext initialScalingEnv rho.
rewrite /ext.
Require Import FunctionalExtensionality. 
apply functional_extensionality_dep => X.  
apply functional_extensionality => S.
rewrite /EcS. rewrite /rho. destruct X.
apply functional_extensionality => y. 
apply functional_extensionality => y'.
simpl. 
rewrite (proj1 (interpExpApSub _ _)).
simpl. rewrite /initialScalingEnv. done.  
specialize (H EXT x (k*x) (refl_equal _)).
rewrite /rho in H.  
done. 
Qed. 