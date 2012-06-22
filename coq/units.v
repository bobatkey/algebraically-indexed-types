Require Import ssreflect ssrbool ssrfun seq ssralg.
Require Import Relations.

Require Import syn.

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

Definition real D (u: unitExpr D) : tyExpr D :=
  TyPrim TyReal (Cons u (Nil _)).  

Definition allUnits D (t: tyExpr (Unit::D)) : tyExpr D := TyAll t. 

Notation "u '*' v" := (unitProd u v) (at level 40, left associativity) : Unit_scope. 
Notation "u ^-1" := (unitInv u) (at level 3, left associativity, format "u ^-1") : Unit_scope.
Notation "'one'" := (unitOne _). 
Delimit Scope Unit_scope with Un.

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

Arguments Scope real [Unit_scope].
Definition ExPrimTypes : seq (tyExpr [::]) := 
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
  allUnits (real #0 --> real #0^-1)%Un;

  (* abs *)
  allUnits (real #0 --> real (abs #0))
]%Ty.

Variable F: fieldType.

Require Import sem.
Canonical ExSem := mkSEM (sig:=ExSIG) (fun _ => F). 



                           
