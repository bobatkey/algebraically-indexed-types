Require Import ssreflect ssrbool ssrfun seq.
Require Import Relations Program.Equality.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import syn.

(*---------------------------- SEMANTICS ---------------------------------------------------*)

Structure SEM (sig: SIG) := mkSEM {
  (* Underlying interpretation of primitive type constructors *)
  interpPrim : PrimType sig -> Type
}.

Section USem.

Variable sig: SIG.
Variable sem: SEM sig.

(* Index-erasure interpretation of types *)
Fixpoint interpTy D (t: Ty D) :Type :=
  match t with
  | TyUnit       => unit
  | TyProd t1 t2 => (interpTy t1 * interpTy t2)%type
  | TySum  t1 t2 => (interpTy t1 + interpTy t2)%type
  | TyArr  t1 t2 => interpTy t1 -> interpTy t2
  | TyAll    _ t => interpTy t
  | TyExists _ t => interpTy t
  | TyPrim   p _ => interpPrim sem p
  end.

(* Relation environments *)
Definition RelEnv D := 
  forall p, Sub (tyArity p) D -> relation (interpPrim sem p).

Definition EcS D D' (rho: RelEnv D') (S: Sub D D') : RelEnv D
:= fun p S' => rho p (ScS S S').

Definition ext D (rho: RelEnv D) (s: Srt sig) (rho': RelEnv (s::D)) :=
  EcS rho' (pi _ s) = rho.

Implicit Arguments ext [D].

Fixpoint semTy D (rho: RelEnv D) (t:Ty D) : interpTy t -> interpTy t -> Prop :=
  match t with
  | TyUnit => fun x y => True
  | TyProd t1 t2 => fun x y => semTy rho x.1 y.1 /\ semTy rho x.2 y.2
  | TySum t1 t2 => fun x y => 
    match x, y with inl x1, inl y1 => semTy rho x1 y1
                  | inr x2, inr y2 => semTy rho x2 y2
                  | _, _ => False 
    end
  | TyArr t1 t2 => fun x y => forall x' y', semTy rho x' y' -> semTy rho (x x') (y y')
  | TyPrim p ixs => rho p ixs
  | TyAll s t => fun x y => forall rho', ext rho s rho' -> semTy rho' x y
  | TyExists s t => fun x y => exists rho', ext rho s rho' -> semTy rho' x y
  end.

End USem.

