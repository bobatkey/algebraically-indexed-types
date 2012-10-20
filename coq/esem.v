(*---------------------------------------------------------------------------
   Index-erasure semantics of types and terms
   (Section 3.3 from POPL'13)
   ---------------------------------------------------------------------------*)
Require Import ssreflect ssrbool ssrfun seq.
Require Import Relations Program.Equality Rel.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import exp ty tm Casts.

Reserved Notation "| t |" (at level 60).

Section ErasureSem.

Variable sig: SIG.
Variable interpPrim: PrimType sig -> Type.

(* Index-erasure interpretation of types, parameterized
   on the interpretation of primitive types *)
Fixpoint interpTy D (t: Ty D) : Type :=
  match t with
  | TyUnit       => unit
  | TyProd t1 t2 => |t1| * |t2|
  | TySum  t1 t2 => |t1| + |t2|
  | TyArr  t1 t2 => |t1| -> |t2|
  | TyAll    _ t => |t| 
  | TyExists _ t => |t|
  | TyPrim   p _ => interpPrim p
  end%type
where "| t |" := (interpTy t).

Definition interpCtxt D : Ctxt D -> Type := Env (@interpTy _).  

Lemma interpCtxtCons D (g: Ty D) (G: Ctxt D) : interpCtxt (g::G) = (interpTy g * interpCtxt G)%type. 
Proof. done. Qed. 

(* This is lemma 3, part 1 *)
Lemma interpEquiv D (t1 t2: Ty D) A : equivTy A t1 t2 -> |t1| = |t2|.
Proof. move => E. induction E => /=//; congruence. Qed. 

(* This is lemma 3, part 2 *)
Lemma interpSubst D (t: Ty D) : forall D' (S: Sub D D'), |t| = |apSubTy S t|.
Proof. induction t => /=//; congruence. Qed.

Lemma interpTyAll D s (t: Ty (s::D)) e : |TyAll t| = |apSubTy (consSub e (idSub D)) t|.
Proof. by rewrite -interpSubst. Qed.

Lemma interpTyExists D s (t: Ty (s::D)) e : |apSubTy (consSub e (idSub D)) t| = |TyExists t|.
Proof. by rewrite -interpSubst. Qed.

Lemma interpTyPack D s (t: Ty (s::D)) : |TyExists t| = |t|. Proof. done. Qed.

Lemma interpSubCtxt D (G: Ctxt D) : forall D' (S: Sub D D'), interpCtxt G = interpCtxt (apSubCtxt S G). 
Proof. 
induction G. done. move => D' S. by rewrite interpCtxtCons (interpSubst _ S) (IHG _ S). 
Qed. 

Definition interpTmVar D (G: Ctxt D) (t: Ty D) (v: TmVar G t) : interpCtxt G -> (|t|) :=
  lookup v. 

Fixpoint interpTm A D (G: Ctxt D) (t: Ty D) (M: Tm A G t) : interpCtxt G -> (|t|) :=
  match M in Tm _ _ t return interpCtxt G -> |t| with
  | VAR _ v       => fun eta => interpTmVar v eta
  | UNIT          => fun eta => tt
  | TYEQ _ _ pf M => fun eta => interpTm M eta :? interpEquiv pf 
  | PAIR _ _ M N  => fun eta => (interpTm M eta, interpTm N eta)
  | PROJ1 _ _ M   => fun eta => (interpTm M eta).1
  | PROJ2 _ _ M   => fun eta => (interpTm M eta).2
  | INL _ _ M     => fun eta => inl _ (interpTm M eta)
  | INR _ _ M     => fun eta => inr _ (interpTm M eta)
  | CASE _ _ _ M M1 M2 => fun eta => 
    match interpTm M eta with 
    | inl x => interpTm M1 (x,eta) 
    | inr y => interpTm M2 (y,eta) 
    end
  | ABS _ _ M     => fun eta => fun x => interpTm M (x,eta)
  | APP _ _ M N   => fun eta => (interpTm M eta) (interpTm N eta)
  | UNIVABS s t M  => fun eta => interpTm M (eta :? interpSubCtxt G (pi D s))
  | UNIVAPP s t e M => fun eta => interpTm M eta :? interpTyAll t e
  | EXPACK _ e t M => fun eta => interpTm M eta :? interpTyExists t e
  | EXUNPACK s t t' M N => fun eta => 
    interpTm N (interpTm M eta :? interpTyPack t, eta :? interpSubCtxt G (pi D s)) 
      :? sym_equal (interpSubst t' (pi D s))
  end.

End ErasureSem.

