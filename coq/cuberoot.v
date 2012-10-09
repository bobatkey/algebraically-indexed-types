Require Import ssreflect ssrbool ssrfun seq eqtype ssralg.
Require Import ssrint rat ssrnum ssrnat. 
Require Import div.
Require Import Relations.

Require Import exp ty model sem.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*---------------------------------------------------------------------------
   Example: translations
   ---------------------------------------------------------------------------*)
Inductive ExSrt := T2.
Inductive ExPrimType := TyVec | TyReal.

Inductive ExIndexOp := TAdd | TNeg | TZero.

Canonical ExSIG := mkSIG
  (fun i => match i with TAdd => ([:: T2; T2], T2)
                       | TNeg => ([:: T2], T2)
                       | TZero => ([::], T2) end)
  (fun t => match t with TyVec => [::T2] 
                       | TyReal => [::] end).


Definition trExpr D := Exp D T2.
Definition tyExpr D := Ty (sig:=ExSIG) D.

Definition trZero D: trExpr D  := 
  AppCon TZero (Nil _). 

Definition trAdd D (u1 u2: trExpr D) : trExpr D := 
  AppCon TAdd (Cons u1 (Cons u2 (Nil _))).

Definition trNeg D (u: trExpr D) : trExpr D :=
  AppCon TNeg (Cons u (Nil _)). 


Notation "u '+' v" := (trAdd u v) (at level 50, left associativity) : Tr_scope. 
Notation "'-' u" := (trNeg u) : Tr_scope.
Notation "'zero'" := (trZero _). 
Delimit Scope Tr_scope with Tr.

Definition vec D (u: trExpr D) : tyExpr D :=
  TyPrim TyVec (Cons u (Nil _)).
Definition real D : tyExpr D :=
  TyPrim TyReal (Nil _). 

Arguments Scope vec [Tr_scope].

Definition allTr D (t: tyExpr (T2::D)) : tyExpr D := TyAll t. 

Notation "#0" := (VarAsExp (ixZ _ _)).
Notation "#1" := (VarAsExp (ixS _ (ixZ _ _))).
Notation "#2" := (VarAsExp (ixS _ (ixS _ (ixZ _ _)))).

Definition ExAxioms : seq (Ax ExSIG) :=
[::
  (* right identity *)
  [::T2] |- #0 + zero === #0;

  (* commutativity *)
  [::T2;T2] |- #0 + #1 === #1 + #0;

  (* associativity *)
  [::T2;T2;T2] |- #0 + (#1 + #2) === (#0 + #1) + #2;

  (* right inverse *)
  [::T2] |- #0 + - #0 === zero
]%Tr.

Definition trEquiv D : relation (trExpr D) := equiv (sig:=ExSIG) ExAxioms.

Definition Gops : Ctxt [::] :=
[::
  (* 0 *)
  (vec zero);

  (* + *)
  allTr (allTr (vec #0 --> vec #1 --> vec (#0 + #1)%Tr));

  (* - *)
  allTr (vec #0 --> vec ( - #0))%Tr;

  (* "square root" *)
  allTr (vec (#0 + #0) --> vec #0)%Tr
]%Ty.

Require Import matrix.
Variable F: numFieldType.

(* 2-d column vector of F *)
Definition myvec := 'cV[F]_2. 

Definition interpPrim: PrimType ExSIG -> Type := 
  fun p => match p with TyVec => myvec | TyReal => F end.

Definition myzero : myvec := 0%R .
Definition myadd (v w: myvec): myvec := (v+w)%R.
Definition myopp (v: myvec): myvec := (-v)%R.
Definition mysqrt (v : myvec) : myvec := v.

Definition eta_ops : interpCtxt interpPrim Gops :=
  (myzero, (myadd, (myopp, (mysqrt, tt)))). 

(*---------------------------------------------------------------------------
   Our second relational interpretation: rationals
   We can use this to show non-definability results.
   The two interpretations could easily be combined (just pair them)
   ---------------------------------------------------------------------------*)

Definition ExpInterpretation := mkInterpretation
  (interpSrt := fun s => rat)
  (fun p =>
   match p with
     TZero  => fun args => 0%R
   | TAdd => fun args => (args.1 + args.2.1)%R
   | TInv  => fun args => (-args.1)%R
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
Defined. 

Definition ExpModelEnv := mkModelEnv (interpPrim := interpPrim) (M:=ExpModel)
  (fun X => 
    match X with TyReal => fun realArgs x y => x=y
               | TyVec => fun vecArgs x y => (x == y%R /\ exists n : nat, (vecArgs.1 * ((2 ^ n)%:R))%Q \is a Qint) end). 

Definition expSemTy D := semTy (ME:=ExpModelEnv) (D:=D).

Definition initialExpEnv: RelEnv ExpModelEnv [::] := tt. 

(* Interpretation of pervasives preserve rational relations *)
Lemma eta_ops_okForExp : semCtxt initialExpEnv eta_ops eta_ops.
Proof.
split. 
(* 0 *)
split => //.
exists 0. done.
split.
(* + *)
move => k k'/=.
move => x x'.
+ move => [H1 [n1 H2]]. rewrite (eqP H1).
  move => y y'. 
  move => [H3 [n2 H4]]. rewrite (eqP H3). 
  split => //. 
    (* There has to be an easier way to do this; ask Georges *)
    exists (n1+n2). 
    move: H2 H4.
    rewrite mulq_addl.
    rat_to_ring.
    rewrite expnD GRing.natrM GRing.mulrA (GRing.mulrC (2 ^ n1)%:R)%R GRing.mulrA.
    move/QintP=>[x1 ->]. 
    move/QintP=>[x2 ->]. 
    apply/QintP. exists (x1 * (2 ^ n2)%:R + x2 * (2 ^ n1)%:R)%R.
    by rewrite GRing.rmorphD 2!GRing.rmorphM 2!natz.
split. 
(* - *)
move => k/=.
move => x x'. 
move => [H1 [n H2]]. rewrite (eqP H1).  
split => //. 
(* Again, there has to be an easier way to do this *)
exists n. move: H2. rat_to_ring. rewrite GRing.mulNr.
move/QintP=>[x1 ->]. apply/QintP. exists (-x1)%R. by rewrite -GRing.rmorphN.  
split. 
(* sqrt *)
move => k/=.
move => x x'.
move => [H1 [n H2]]. rewrite (eqP H1).
split => //.
exists (S n).
rat_to_ring.
by rewrite expnS GRing.natrM GRing.mulrA GRing.mulrDr GRing.mulr1.
split.
Qed. 

(*---------------------------------------------------------------------------
   Now some applications.
   First we prove that there are no terms with the type forall t, vec(t+t+t) -> vec t
   even though we have a term of type forall t, vec(t+t) -> vec t
   ---------------------------------------------------------------------------*)

Definition badTy : Ty [::] := allTr (vec (#0 + #0 + #0)%Tr --> vec #0)%Ty.

Lemma gcd_2n_3_is_1 : forall n, gcdn (2 ^ n) 3 == 1.
Proof.
move => n. rewrite gcdnC. induction n.
+ by reflexivity.
+ by rewrite expnS Gauss_gcdl. 
Qed.

Open Scope ring_scope.
Lemma badTyUninhabited (f:myvec->myvec) : 
  expSemTy (t:=badTy) initialExpEnv f f -> 
  False.
Proof. rewrite /expSemTy/=. move => H.  
specialize  (H (1%:Q/3%:Q) 0 0).
destruct H; intuition.  
 (* 1/3 + 1/3 + 1/3 is an integer *) exists 1%N. done.
 (* 1/2 * 2^n is not an integer for any 'n' *)
 destruct H0 as [n is_integer].
 move: is_integer.
 rat_to_ring.
 rewrite -{1}(GRing.divr1 (2 ^ n)%:R) GRing.mulf_div GRing.mul1r GRing.mulr1.
 rewrite Qint_def.
 assert (denq ((2 ^ n)%:R%:~R / 3%:R) = 3)%Q.
  apply (@coprimeq_den (2 ^ n)%:R 3). by rewrite natz /coprime gcd_2n_3_is_1.
 rewrite natz in H0. 
 rewrite H0.
 discriminate.
Qed.
