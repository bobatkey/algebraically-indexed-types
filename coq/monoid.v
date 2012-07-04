Require Import ssreflect ssrbool ssrfun seq ssralg.
Require Import Relations.

Require Import syn.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*---------------------------------------------------------------------------
   Example: monoids
   ---------------------------------------------------------------------------*)
Inductive ExSrt := SrtM.
Inductive ExPrimType := TyM.
Inductive ExIndexOp := MProd | MOne.

Canonical ExSIG := mkSIG
  (fun i => match i with MProd => ([:: SrtM; SrtM], SrtM)
                       | MOne => ([::], SrtM) end)
  (fun t => match t with TyM => [::SrtM] end).


Definition mExpr D := Exp D SrtM.
Definition tyExpr D := Ty (sig:=ExSIG) D.

Definition mOne D: mExpr D  := 
  AppCon MOne (Nil _). 

Definition mProd D (u1 u2: mExpr D) : mExpr D := 
  AppCon MProd (Cons u1 (Cons u2 (Nil _))).

Notation "u '*' v" := (mProd u v) (at level 40, left associativity) : Monoid_scope. 
Notation "'one'" := (mOne _). 
Delimit Scope Monoid_scope with Mn.

Definition M D (u: mExpr D) : tyExpr D :=
  TyPrim TyM (Cons u (Nil _)).  
Arguments Scope M [Monoid_scope].

Definition allM D (t: tyExpr (SrtM::D)) : tyExpr D := TyAll t. 

Notation "#0" := (VarAsExp (VarZ _ _)).
Notation "#1" := (VarAsExp (VarS _ (VarZ _ _))).
Notation "#2" := (VarAsExp (VarS _ (VarS _ (VarZ _ _)))).

Definition ExAxioms : seq (Ax ExSIG) :=
[::
  (* right identity *)
  [::SrtM] |- #0 * one === #0;

  (* left identity *)
  [::SrtM] |- one * #0 === #0;

  (* associativity *)
  [::SrtM;SrtM;SrtM] |- #0 * (#1 * #2) === (#0 * #1) * #2;

  (* commutativity *)
  [::SrtM;SrtM] |- #0 * #1 === #1 * #0
]%Mn.

Definition mequiv D : relation (mExpr D) := equiv (sig:=ExSIG) ExAxioms.

Definition ExPrimTypes : seq (tyExpr [::]) := 
[::
  (* 1 *)
  M one;

  (* . *)
  allM (M #0 --> M #0 --> M #0)
]%Ty.

Variable F: fieldType.

Require Import sem.
(*Canonical ExSem := mkSEM (sig:=ExSIG) (fun _ => F). *)



                           
