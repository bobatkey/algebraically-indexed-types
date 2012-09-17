Require Import ssreflect ssrbool ssrfun seq eqtype ssralg.
Require Import Relations.

Require Import syn model.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*---------------------------------------------------------------------------
   Example: scaling (units-of-measure)
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

Variable F: fieldType.

Require Import sem.

(* A model of the theory: non-zero scale factors *)
Structure scaling : Type := Scaling {tval :> F; _ : tval != 0%R}.

Canonical scaling_subType :=
  Eval hnf in [subType for tval by scaling_rect].
Definition scaling_eqMixin := Eval hnf in [eqMixin of scaling by <:]. 
Canonical scaling_eqType :=   Eval hnf in EqType scaling scaling_eqMixin.  
Implicit Type t : scaling.

Lemma scaling_neq0 (x:scaling) : val x != 0%R. Proof. by elim x. Qed.

Lemma eqEquivalence : equivalence _ (fun x y:scaling => x==y).
Proof. split. by move => x/=.   
move => x y z/= E1 E2. by rewrite (eqP E1) (eqP E2).
move => x y/= E1. by rewrite (eqP E1). 
Qed. 

Lemma scaling_inj (x y: scaling) : val x = val y -> x == y. 
Proof. move => EQ.
apply val_inj in EQ.   
by rewrite EQ. 
Qed. 

Definition scaling_one := Scaling (GRing.nonzero1r _).
Definition scaling_prod (x y: scaling) : scaling :=
  Scaling (GRing.mulf_neq0 (scaling_neq0 x) (scaling_neq0 y)). 
Definition scaling_inv (x: scaling) : scaling :=
  Scaling (GRing.invr_neq0 (scaling_neq0 x)). 

Definition ScalingInterpretation := mkInterpretation
  (fun s => eqEquivalence)
  (fun p =>
   match p with
     UnitOne  => fun args => scaling_one
   | UnitProd => fun args => scaling_prod args.1 args.2.1
   | UnitAbs  => fun args => args.1
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
done. 
(* end *)
done. 
Defined. 

Definition interpPrim : PrimType ExSIG -> Type := fun _ => F. 

Definition ScalingModelEnv := mkModelEnv (interpPrim := interpPrim) (M:=ScalingModel)
  (fun X => 
    match X with TyReal => 
    fun realArgs => 
    fun x y => y = (val realArgs.1 * x)%R end). 

Definition ScalingModelRelSet := modelRelSet ScalingModelEnv.

Definition scalingSemTy := semTy ScalingModelRelSet.

Definition eta_ops : interpCtxt interpPrim Gops :=
  (0%R,
  (1%R,
  (fun x y => (x + y)%R,
  (fun x y => (x - y)%R,
  (fun x y => (x * y)%R,
  (fun x => (if x==0 then inr _ tt else inl _ (1 / x))%R,
  (fun x => x, 
  tt))))))).  

(* Interpretation of pervasives preserve scaling relations *)
Lemma eta_ops_ok : semCtxt ScalingModelRelSet (fun X args x y => True) eta_ops eta_ops.
Proof.
split. 
(* 0 *)
move => rho' MEM EXT.
rewrite /ScalingModelRelSet/modelRelSet/= in MEM. 
destruct MEM as [[k u] ->]. simpl. 
by rewrite GRing.mulr0. 
split.
(* 1 *)
done. 
split. 
(* + *)
move => rho' MEM EXT.
rewrite /ScalingModelRelSet/modelRelSet/= in MEM. 
destruct MEM as [[k u] ->]. simpl. 
move => x x' ->. 
move => y y' ->. 
by rewrite GRing.mulr_addr. 
split. 
(* - *)
move => rho' MEM EXT.
rewrite /ScalingModelRelSet/modelRelSet/= in MEM. 
destruct MEM as [[k u] ->]. simpl. 
move => x x' ->. 
move => y y' ->. 
by rewrite GRing.mulr_subr. 
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
rewrite !GRing.div1r. rewrite GRing.invr_mul. 
done. by rewrite GRing.unitfE E. 
by rewrite GRing.unitfE neq. 
split. 
(* abs *)
move => rho' MEM EXT.
rewrite /ScalingModelRelSet/modelRelSet/= in MEM. 
destruct MEM as [[k u] ->]. simpl. 
move => x x' ->. 
done. 
(* finish *)
done. 
Qed. 