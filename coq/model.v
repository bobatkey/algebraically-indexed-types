(*---------------------------------------------------------------------------
   Models of equational theory
   ---------------------------------------------------------------------------*)

Require Import ssreflect ssrbool ssrfun seq.
Require Import Relations Program.Equality.
Require Import FunctionalExtensionality. 
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import syn.


Section Models.

Variable sig: SIG.
Variable interpPrim: PrimType sig -> Type.

Fixpoint interpSeq X (interp: X -> Type) (xs: seq X): Type :=
  if xs is x::xs then (interp x * interpSeq interp xs)%type
  else unit.

(* Interpretation of sorts and index operations *)
Structure Interpretation := mkInterpretation {
  (* Carrier for each sort *)
  interpSrt : Srt sig -> Type; 

  (* Equivalence relation for each sort *)
  interpEq : forall s, relation (interpSrt s);
  equivEq : forall s, equivalence (interpSrt s) (@interpEq _);

  (* Function for each index operation *)
  interpOp : forall p, interpSeq interpSrt (opArity p).1 -> interpSrt (opArity p).2  
}.

Implicit Arguments interpOp [].

Fixpoint interpVar I D s (v: Var D s) : interpSeq (interpSrt I) D -> interpSrt I s :=
  match v with 
  | VarZ _ _     => fun env => env.1
  | VarS _ _ _ v => fun env => interpVar v env.2
  end.

(* Interpret an index expression compositionally *)
Fixpoint interpExp I D s (e: Exp D s) : interpSeq (interpSrt I) D -> interpSrt I s :=
  match e with
  | VarAsExp _ v => fun env => interpVar v env
  | AppCon op es => fun env => interpOp I op (interpExps es env)
  end

with interpExps I D ss (es: Exps D ss) (env: interpSeq (interpSrt I) D)
  : interpSeq (interpSrt I) ss :=
  if es is Cons _ _ ix ixs then (interpExp ix env, interpExps ixs env) else tt.

Definition interpAx I (A: Ax sig) := 
  let: mkAx D s lhs rhs := A in
  forall env: interpSeq (interpSrt I) D, interpEq (interpExp lhs env) (interpExp rhs env).

Fixpoint interpAxs I (As: seq (Ax sig)) :=
  if As is A::As then interpAx I A /\ interpAxs I As else True.

(* A model is an interpretation together with a proof that the axioms are satisfied *)
Structure Model A := mkModel {
  I :> Interpretation;
  soundness: interpAxs I A
}.

Fixpoint apArgs A (M1 M2: Model A) arity (f:forall s, interpSrt M1 s -> interpSrt M2 s) :
  interpSeq (interpSrt M1) arity -> interpSeq (interpSrt M2) arity :=
  if arity is s::ss
  then fun args => (f s args.1, apArgs f args.2) 
  else fun args => tt.
 
Structure Homomorphism A (M1 M2: Model A) := mkHom {
  hom:> forall s: Srt sig, interpSrt M1 s -> interpSrt M2 s;
  preserves: forall p xs, interpEq (hom (interpOp M1 p xs)) (interpOp M2 p (apArgs hom xs))
}.

Fixpoint seqAsExps D D' : interpSeq (Exp (sig:=sig) D) D' -> Exps D D' :=
  if D' is s::D' 
  then fun ixs => Cons ixs.1 (seqAsExps ixs.2)
  else fun _ => Nil _.

Definition mkFreeInterpretation (A: seq (Ax sig)) D : Interpretation := 
  mkInterpretation (fun s => equivIsEquivalence A D s) (fun p ixs => AppCon p (seqAsExps ixs)).

(*
Definition mkFreeModel A (D:IxCtxt sig) : Model A.  
Proof. apply (@mkModel A (mkFreeInterpretation A D)). 
induction A => //.
simpl. split.  
destruct IHA.  apply EquivByAxS. rewrite /mkFreeInterpretation. simpl. rewrite /interpAxs.  
simpl. done. 
induction Proof. : Ax sig) : Model := Build_Model .

Fixpoint piAll s (D : IxCtxt sig) : Sub [::s] (s::D) :=
  if D is s'::D' return Sub [::s] (s::D)
  then ScS (pi _ _) (piAll s D')
  else idSub [::s].

*)

End Models.