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
Inductive ExPrimType := Scalar.
Inductive ExIndexOp := UnitProd | UnitInv | UnitOne | UnitAbs.

Canonical ExSIG := mkSIG
  (fun i => match i with UnitProd => ([:: Unit; Unit], Unit)
                       | UnitInv => ([:: Unit], Unit)
                       | UnitOne => ([::], Unit) 
                       | UnitAbs => ([:: Unit], Unit) end)
  (fun t => match t with Scalar => [::Unit] end).


Definition unitExpr D := Exp D Unit.
Definition tyExpr D := Ty (sig:=ExSIG) D.

Open Scope Exp_scope.
Notation "u '*' v" := (UnitProd<u,v>) (at level 40, left associativity) : Unit_scope. 
Notation "u ^-1" := (UnitInv<u>) (at level 3, left associativity, format "u ^-1") : Unit_scope.
Notation "'abs' u" := (UnitAbs<u>) (at level 5, left associativity) : Unit_scope.
Notation "'one'" := (UnitOne<>). 
Delimit Scope Unit_scope with Un.

Definition scalar D (u: unitExpr D) : tyExpr D :=
  TyPrim Scalar (Cons u (Nil _)).  
Arguments Scope scalar [Unit_scope].

Open Scope Ty_scope.
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
  all Unit (scalar #0);

  (* 1 *)
  scalar one;

  (* + *)
  all Unit (scalar #0 --> scalar #0 --> scalar #0);

  (* - *)
  all Unit (scalar #0 --> scalar #0 --> scalar #0);

  (* * *)
  all Unit (all Unit (scalar #0 --> scalar #1 --> scalar (#0 * #1)%Un));

  (* reciprocal *)
  all Unit (scalar #0 --> scalar #0^-1 + TyUnit _)%Un;

  (* abs *)
  all Unit (scalar #0 --> scalar (abs #0))
]%Ty%Un.

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

(*
Lemma eqEquivalence (T:eqType) : equivalence _ (fun x y:T => x==y).
Proof. split. by move => x/=.   
move => x y z/= E1 E2. by rewrite (eqP E1) (eqP E2).
move => x y/= E1. by rewrite (eqP E1). 
Qed. 
*)

Lemma scaling_inj (x y: scaling) : val x = val y -> x = y. 
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
  (interpSrt := (fun s => scaling))
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
    match X with Scalar => 
    fun realArgs => 
    fun x y => y = (val realArgs.1 * x)%R end). 

Definition scalingSemTy D := semTy (ME:=ScalingModelEnv) (D:=D).

Definition initialScalingEnv: RelEnv ScalingModelEnv [::] := tt. 

(* Interpretation of pervasives preserve scaling relations *)
Lemma eta_ops_ok : semCtxt initialScalingEnv eta_ops eta_ops.
Proof.
split. 
(* 0 *)
move => k/=. 
by rewrite GRing.mulr0. 
split.
(* 1 *)
rewrite/=. by rewrite GRing.mulr1. 
split. 
(* + *)
move => k/=.
move => x x' ->. 
move => y y' ->. 
by rewrite GRing.mulrDr. 
split. 
(* - *)
move => k/=.
move => x x' ->. 
move => y y' ->. 
by rewrite GRing.mulrBr.
split. 
(* * *)
move => k/=.
move => k'/=. 
move => x x' ->. 
move => y y' ->. 
elim k => [k1 neq]/=. 
elim k' => [k2 neq']/=. 
rewrite -2!(GRing.mulrA k2). 
by rewrite (GRing.mulrCA k1 x y). 
split. 
(* recip *)
move => k/=.
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
move => k/=.
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
  (interpSrt := fun s => rat)
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
    match X with Scalar => 
    fun expArgs => 
    fun x y => (x==0%R /\ y==0%R \/ (x == y%R /\ expArgs.1 \is a Qint)) end). 

Definition expSemTy D := semTy (ME:=ExpModelEnv) (D:=D).

Definition initialExpEnv: RelEnv ExpModelEnv [::] := tt. 

(* Interpretation of pervasives preserve exponent relations *)
Lemma eta_ops_okForExp : semCtxt initialExpEnv eta_ops eta_ops.
Proof.
split. 
(* 0 *)
move => k/=.
intuition. 
split.
(* 1 *)
rewrite /initialExpEnv. simpl. 
by right. 
split. 
(* + *)
move => k/=.
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
move => k/=.
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
move => k/=.
move => k'/=.
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
move => k/=.
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
move => k/=.
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

Definition sqrtTy : Ty [::] := all Unit (scalar (#0 * #0)%Un --> scalar #0)%Ty.

Open Scope ring_scope.
Lemma sqrtTrivial (f:F->F) : 
  expSemTy (t:=sqrtTy) initialExpEnv f f -> 
  forall x, f x = 0.
Proof. rewrite /expSemTy/=. move => H x. 
specialize  (H (1%:Q/2%:Q) x x).
destruct H; intuition.  
by rewrite (eqP H0). 
Qed. 

(*---------------------------------------------------------------------------
   Next we prove that the type of squaring exhibits a scaling property
   ---------------------------------------------------------------------------*)

Definition sqrTy : Ty [::] := all Unit (scalar #0 --> scalar (#0 * #0)%Un)%Ty.

Lemma sqrScaling (f:F->F) :   
  scalingSemTy (t:=sqrTy) initialScalingEnv f f -> 
  forall k, k != 0 ->
  forall x, f (k * x) = k^2 * f x.
Proof. rewrite /scalingSemTy/=. move => H k neq x. 
apply (H (Scaling neq) x (k*x) (refl_equal _)). 
Qed. 