Require Import ssreflect ssrbool ssrfun seq eqtype ssralg.
Require Import ssrint rat ssrnum matrix. 
Require Import Relations.

Require Import exp ty model sem.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*---------------------------------------------------------------------------
   Example: translations
   ---------------------------------------------------------------------------*)
Inductive ExSrt := T2.
Inductive ExPrimType := Vec | Scalar.

Inductive ExIndexOp := TAdd | TNeg | TZero.

Canonical ExSIG := mkSIG
  (fun i => match i with TAdd => ([:: T2; T2], T2)
                       | TNeg => ([:: T2], T2)
                       | TZero => ([::], T2) end)
  (fun t => match t with Vec => [::T2] 
                       | Scalar => [::] end).


Definition trExpr D := Exp D T2.
Definition tyExpr D := Ty (sig:=ExSIG) D.

Open Scope Exp_scope. 
Notation "u '+' v" := (TAdd<u,v>) (at level 50, left associativity) : Tr_scope. 
Notation "'-' u" := (TNeg<u>) : Tr_scope.
Notation "'zero'" := (TZero<>). 
Delimit Scope Tr_scope with Tr.

Definition vec D (u: trExpr D) : tyExpr D :=
  TyPrim Vec (Cons u (Nil _)).
Definition scalar D : tyExpr D :=
  TyPrim Scalar (Nil _). 

Arguments Scope vec [Tr_scope].

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
]%Tr%Ty.

Definition trEquiv D : relation (trExpr D) := equiv (sig:=ExSIG) ExAxioms.

Definition Gops : Ctxt [::] :=
[::
  (* 0 *)
  (vec zero);

  (* + *)
  all T2 (all T2 (vec #0 --> vec #1 --> vec (#0 + #1)%Tr));

  (* - *)
  all T2 (vec #0 --> vec ( - #0))%Tr
]%Ty.

(*
Fixpoint tr D A (G: Ctxt D) (v:bool) : Tm ExAxioms G A -> Tm ExAxioms G A :=
  match A return Tm ExAxioms G A -> Tm ExAxioms G A with
  | TyUnit => fun x => x
  | TyProd A1 A2 => fun p =>
    PAIR (@tr D A1 G v (PROJ1 p)) (@tr D A2 G v (PROJ2 p))
(*
  | TySum A1 A2 => fun s =>
    CASE s (INL _ (@tr A1 v (VAR ExAxioms (TmVarZ _ _)))) 
           (INR _ (@tr A2 v (VAR ExAxioms (TmVarZ _ _))))
*)
  | TyArr A1 A2 => fun f =>
    ABS (@tr D A2 (A1::G) v (APP (shExp f) (@tr D A1 (A1::G) v (VAR _ (ixZ _ _)))))
  | _ => fun x => x
  end.
*)

Variable F: numFieldType.

(* 2-d column vector of F *)
Definition myvec := 'cV[F]_2. 

Definition interpPrim: PrimType ExSIG -> Type := 
  fun p => match p with Vec => myvec | Scalar => F end.

Definition myzero : myvec := 0%R .
Definition myadd (v w: myvec): myvec := (v+w)%R.
Definition myopp (v: myvec): myvec := (-v)%R.

Definition eta_ops : interpCtxt interpPrim Gops :=
  (myzero, (myadd, (myopp, tt))). 

(*---------------------------------------------------------------------------
   Our first relational interpretation: translations
   ---------------------------------------------------------------------------*)

Definition TransInterpretation := mkInterpretation
  (interpSrt := (fun s => myvec))
  (fun p =>
   match p with
     TZero  => fun args => myzero
   | TAdd   => fun args => myadd args.1 args.2.1
   | TInv   => fun args => myopp args.1
   end ).

Definition TransModel : Model ExAxioms. 
Proof. 
apply (@mkModel _ ExAxioms TransInterpretation). 
split. 
(* right identity *)
move => /= [x u] /=. rewrite /myadd/myzero.
by rewrite /= GRing.addr0. 
split. 
(* commutativity *)
move => /= [x [y u]] /=. 
by rewrite /myadd GRing.addrC. 
split. 
(* associativity *)
move => /= [x [y [z u]]] /=. 
by rewrite /myadd GRing.addrA. 
split. 
(* right inverse *)
move => /= [x u] /=. 
by rewrite /myadd/myopp/myzero GRing.addrN. 
split.
Defined. 

Definition TransModelEnv := mkModelEnv (interpPrim := interpPrim) (M:=TransModel)
  (fun X => 
    match X with Scalar => fun realargs => fun x y => x=y 
               | Vec => fun vecArgs =>fun x y => y = (vecArgs.1 + x)%R end). 

Definition transSemTy D := semTy (ME:=TransModelEnv) (D:=D).

Definition initialTransEnv: RelEnv TransModelEnv [::] := tt. 

(* Interpretation of pervasives preserve translation relations *)
Lemma eta_ops_ok : semCtxt initialTransEnv eta_ops eta_ops.
Proof.
split. 
(* 0 *)
rewrite /=/myadd/myzero. 
by rewrite GRing.addr0. 
split.
(* + *)
move => k k'/=.
move => x x' ->. 
move => y y' ->. 
rewrite /myadd.
rewrite -2!(GRing.addrA k'). 
by rewrite (GRing.addrCA k x y). 
split. 
(* - *)
move => k/=.
move => x x' ->.
rewrite /myopp. 
by rewrite GRing.opprD. 
split. 
Qed. 

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
    match X with Scalar => fun realArgs x y => x=y
               | Vec => fun vecArgs x y => (x == y%R /\ vecArgs.1 \is a Qint) end). 

Definition expSemTy D := semTy (ME:=ExpModelEnv) (D:=D).

Definition initialExpEnv: RelEnv ExpModelEnv [::] := tt. 

(* Interpretation of pervasives preserve rational relations *)
Lemma eta_ops_okForExp : semCtxt initialExpEnv eta_ops eta_ops.
Proof.
split. 
(* 0 *)
done. 
split.
(* + *)
move => k k'/=.
move => x x'.
+ move => [H1 H2]. rewrite (eqP H1).
  move => y y'. 
  move => [H3 H4]. rewrite (eqP H3). 
  split => //. 
    (* There has to be an easier way to do this; ask Georges *)
    move: H2 H4. 
    move/QintP=>[x1 ->]. 
    move/QintP=>[x2 ->]. apply/QintP. exists (x1 + x2)%R. by rewrite -GRing.rmorphD.  
split. 
(* - *)
move => k/=.
move => x x'. 
move => [H1 H2]. rewrite (eqP H1).  
split => //. 
(* Again, there has to be an easier way to do this *)
move: H2. 
move/QintP=>[x1 ->]. 
apply/QintP. exists (-x1)%R. by rewrite -GRing.rmorphN.  
split. 
Qed. 

(*---------------------------------------------------------------------------
   Now some applications.
   First we prove that there are no terms with the type forall t, vec(t+t) -> vec t
   ---------------------------------------------------------------------------*)

Definition badTy : Ty [::] := all T2 (vec (#0 + #0)%Tr --> vec #0)%Ty.

Open Scope ring_scope.
Lemma badTyUninhabited (f:myvec->myvec) : 
  expSemTy (t:=badTy) initialExpEnv f f -> 
  False.
Proof. rewrite /expSemTy/=. move => H.  
specialize  (H (1%:Q/2%:Q) 0 0).
destruct H; intuition.  
Qed. 


(*---------------------------------------------------------------------------
   Next we prove that the type of areaTri exhibits a translation property
   ---------------------------------------------------------------------------*)

Definition triTy : Ty [::] := all T2 (vec #0 --> vec #0 --> vec #0 --> scalar _)%Tr%Ty.

Lemma triTrans (f:myvec->myvec->myvec->F) :   
  transSemTy (t:=triTy) initialTransEnv f f -> 
  forall t, 
  forall u v w, f (t+u) (t+v) (t+w) = f u v w.
Proof. rewrite /transSemTy/=. move => H t u v w.
symmetry. 
apply (H t u (t+u) (refl_equal _)
           v (t+v) (refl_equal _)
           w (t+w) (refl_equal _)). 
Qed. 