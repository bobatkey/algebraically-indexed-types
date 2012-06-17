Require Import ssreflect ssrbool ssrfun seq.
Require Import Relations.

Require Import syn.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*---------------------------- Example: scaling --------------------------------*)
Inductive ExSrt := SrtUnit.
Inductive ExPrimType := TyReal.
Inductive ExIndexOp := UnitProd | UnitInv | UnitOne | UnitAbs.

Definition ExSIG := mkSIG
  (fun i => match i with UnitProd => ([:: SrtUnit; SrtUnit], SrtUnit)
                       | UnitInv => ([:: SrtUnit], SrtUnit)
                       | UnitOne => ([::], SrtUnit) 
                       | UnitAbs => ([:: SrtUnit], SrtUnit) end)
  (fun t => match t with TyReal => [::SrtUnit] end).


Definition unitExpr D := IxExp (sig:=ExSIG) D SrtUnit.
Definition tyExpr D := Ty (sig:=ExSIG) D.

Definition unitOne D: unitExpr D  := 
  ConIx (sig:=ExSIG) UnitOne (NilIx _).

Definition unitProd D (u1 u2: unitExpr D) : unitExpr D := 
  ConIx (sig:=ExSIG) UnitProd (ConsIx u1 (ConsIx u2 (NilIx _))).

Definition unitInv D (u: unitExpr D) : unitExpr D :=
  ConIx (sig:=ExSIG) UnitInv (ConsIx u (NilIx _)). 

Definition unitAbs D (u: unitExpr D) : unitExpr D :=
  ConIx (sig:=ExSIG) UnitAbs (ConsIx u (NilIx _)). 

Definition realTy D (u: unitExpr D) : tyExpr D :=
  TyPrim (sig:=ExSIG) TyReal (ConsIx u (NilIx _)).  

Definition arrow D (t1 t2: tyExpr D) : tyExpr D :=
  TyArr (sig:=ExSIG) t1 t2.

Definition allUnits D (t: tyExpr (SrtUnit::D)) : tyExpr D := TyAll (sig:=ExSIG) t. 

Notation "#0" := (VarIx (IxZ _ _)).
Notation "#1" := (VarIx (IxS _ (IxZ _ _))).
Notation "#2" := (VarIx (IxS _ (IxS _ (IxZ _ _)))).

Definition ExAxioms : seq (Ax ExSIG) :=
[::
  (* right identity *)
  mkAx (sig:=ExSIG) (D:=[::SrtUnit]) (unitProd #0 (unitOne _)) #0;

  (* commutativity *)
  mkAx (sig:=ExSIG) (D:=[::SrtUnit;SrtUnit]) (unitProd #0 #1) (unitProd #1 #0);

  (* associativity *)
  mkAx (sig:=ExSIG) (D:=[::SrtUnit;SrtUnit;SrtUnit]) 
    (unitProd #0 (unitProd #1 #2)) 
    (unitProd (unitProd #0 #1) #2);

  (* right inverse *)
  mkAx (sig:=ExSIG) (D:=[::SrtUnit]) (unitProd #0 (unitInv #0)) #0
].

Definition uequiv D : relation (unitExpr D) := equiv (sig:=ExSIG) ExAxioms.

Definition ExPrimTypes : seq (tyExpr [::]) := 
[::
  (* 0 *)
  allUnits (realTy #0);

  (* 1 *)
  realTy (unitOne _);

  (* + *)
  allUnits (arrow (realTy #0) (arrow (realTy #0) (realTy #0)));

  (* - *)
  allUnits (arrow (realTy #0) (arrow (realTy #0) (realTy #0)));

  (* * *)
  allUnits (allUnits (arrow (realTy #0) (arrow (realTy #1) (realTy (unitProd #0 #1)))));

  (* reciprocal *)
  allUnits (arrow (realTy #0) (realTy (unitInv #0)));

  (* abs *)
  allUnits (arrow (realTy #0) (realTy (unitAbs #0)))
].

                           
