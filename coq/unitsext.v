(*---------------------------------------------------------------------------
   SCALARS WITH SCALINGS

   This file contains a formalization of the theory of scalars (Figure 1) 
   extended with a square root operation. 
   ---------------------------------------------------------------------------*)

Require Import ssreflect ssrbool ssrfun seq eqtype ssralg.
Require Import ssrnat ssrint rat ssrnum. 

Require Import Relations.

Require Import exp ty model sem.

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
  all Unit (scalar #0 --> scalar (abs #0));

  (* sqrt *)
  all Unit (scalar (#0 * #0) --> scalar (abs #0))%Un
]%Ty%Un.

(*---------------------------------------------------------------------------
   Underlying semantics
   ---------------------------------------------------------------------------*)

Variable F: rcfType.
Definition interpPrim : PrimType ExSIG -> Type := fun _ => F. 

Open Scope ring_scope.
Definition eta_ops : interpCtxt interpPrim Gops :=
  ( 0,
  ( 1,
  ( +%R,
  ( fun x y => x - y,
  ( *%R,
  ( fun x => (if x == 0 then inr _ tt else inl _ (1 / x)),
  ( fun x => `|x|, 
  ( fun x => Num.sqrt x,
  tt)))))))).  


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
move => /= [x _] /=.
apply scaling_inj. by rewrite /= GRing.mulr1. 
split. 
(* commutativity *)
move => /= [x [y _]] /=. 
apply scaling_inj. by rewrite /= GRing.mulrC. 
split. 
(* associativity *)
move => /= [x [y [z _]]] /=. 
apply scaling_inj. by rewrite /= GRing.mulrA. 
split. 
(* right inverse *)
move => /= [x _] /=. 
apply scaling_inj. rewrite /= GRing.mulrV => //. 
elim x => [x' neq]. by rewrite GRing.unitfE neq. 
split.
(* homomorphism of abs *)
move => /= [x [y _]] /=.
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

(* Interpretation of pervasives preserve scaling relations *)
Lemma eta_ops_ok : semCtxt (emptyRelEnv ScalingModelEnv) eta_ops eta_ops.
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
move => k/= x x' -> y y' ->. 
by rewrite GRing.mulrDr. 
split. 
(* - *)
move => k/= x x' -> y y' ->. 
by rewrite GRing.mulrBr.
split. 
(* * *)
move => k k'/= x x' -> y y' ->. 
elim k => [k1 neq]/=. 
elim k' => [k2 neq']/=. 
rewrite -2!(GRing.mulrA k2). 
by rewrite (GRing.mulrCA k1 x y). 
split. 
(* recip *)
move => k/= x x' ->.
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
move => k/= x x' ->. 
by rewrite Num.Theory.normrM. 
split. 
(* sqrt *)
move => /= k x x' ->.
rewrite Num.Theory.sqrtrM. 
rewrite Num.Theory.sqrtr_sqr => //.
apply: Num.Theory.sqr_ge0. 
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
     UnitOne  => fun args => 0
   | UnitProd => fun args => args.1 + args.2.1
   | UnitAbs  => fun args => args.1
   | UnitInv  => fun args => -args.1
   end ).

Definition ExpModel : Model ExAxioms. 
Proof. 
apply (@mkModel _ ExAxioms ExpInterpretation). 
split. 
(* right identity *)
move => /= [x _] /=. by rewrite /= GRing.addr0. 
split. 
(* commutativity *)
move => /= [x [y _]] /=. by rewrite /= GRing.addrC. 
split. 
(* associativity *)
move => /= [x [y [z _]]] /=. by rewrite /= GRing.addrA.
split. 
(* right inverse *)
move => /= [x _] /=. by rewrite GRing.addrN. 
split.
(* homomorphism of abs *)
move => /= [x [y _]] /=. done.
(* end *)
done. 
Defined. 

(* A dyadic rational is one with a finite binary expansion *)
(* They are closed under addition, negation, and halving *)
Definition isDyadic r := exists m, (2^m)%:R * r \is a Qint.

Lemma add_isQInt r1 r2 : r1 \is a Qint -> r2 \is a Qint -> (r1+r2) \is a Qint.
Proof. 
move /QintP => [x1 ->]. move /QintP=>[x2 ->]. 
apply /QintP. exists (x1 + x2). by rewrite -GRing.rmorphD.  
Qed. 

Lemma mul_isQInt r1 r2 : r1 \is a Qint -> r2 \is a Qint -> (r1*r2) \is a Qint.
Proof. 
move /QintP => [x1 ->]. move /QintP => [x2 ->]. 
apply /QintP. exists (x1 * x2). by rewrite -GRing.rmorphM.  
Qed. 

Lemma neg_isQInt r : r \is a Qint -> -r \is a Qint.
Proof. 
move /QintP => [x1 ->]. apply /QintP. exists (-x1). by rewrite -GRing.rmorphN.  
Qed. 

Lemma nat_is_Qint n : n%:R \is a Qint.
Proof. induction n => //. rewrite -addn1 GRing.natrD. apply add_isQInt => //. Qed. 

Lemma isDyadic0 : isDyadic 0. 
Proof. by exists 0%N. Qed. 

Lemma add_isDyadic r1 r2 : isDyadic r1 -> isDyadic r2 -> isDyadic (r1+r2).
Proof.
move => [n1 R1] [n2 R2].
exists (n1+n2)%N.
rewrite expnD GRing.natrM GRing.mulrDr GRing.mulrAC. 
rewrite -(GRing.mulrA (2^n1)%:R). 
apply add_isQInt; apply mul_isQInt => //; apply nat_is_Qint.  
Qed. 

Lemma neg_isDyadic r : isDyadic r -> isDyadic (-r). 
Proof. move => [n R]. exists n. rewrite GRing.mulrN. by apply neg_isQInt. Qed. 

Lemma half_isDyadic r : isDyadic (r+r) -> isDyadic r. 
move => [n R]. 
exists (n.+1). rewrite expnS.
rewrite mul2n -addnn. 
rewrite GRing.natrD. 
rewrite GRing.mulrDr in R. 
by rewrite GRing.mulrDl. 
Qed. 

Definition ExpModelEnv := mkModelEnv (interpPrim := interpPrim) (M:=ExpModel)
  (fun X => 
    match X with Scalar => 
    fun expArgs => 
    fun x y => (x == 0 /\ y == 0 \/ 
               (x == y /\ isDyadic expArgs.1)) end). 

(* Interpretation of pervasives preserve exponent relations *)
Lemma eta_ops_okForExp : semCtxt (emptyRelEnv ExpModelEnv) eta_ops eta_ops.
Proof.
split. 
(* 0 *)
move => k/=.
intuition. 
split.
(* 1 *)
right. split => //. apply isDyadic0. 
split. 
(* + *)
move => k/= x x'.
elim.  
(**) move => [/eqP -> /eqP ->] y y'.
  elim. 
    move => [/eqP -> /eqP ->]. rewrite !GRing.addr0. by intuition. 
  - move => [/eqP -> H4]. rewrite !GRing.add0r. by intuition. 
(**) move => [/eqP -> H1] y y'. 
  elim.
    move => [/eqP -> /eqP ->]. rewrite !GRing.addr0. by intuition. 
    move => [/eqP -> H4]. by intuition. 
split. 
(* - *)
move => k/=.
move => x x'. elim.  
(**) move => [/eqP -> /eqP ->] y y'.
  elim. 
    move => [/eqP -> /eqP ->]. rewrite !GRing.subr0. by intuition. 
  - move => [/eqP -> H4]. rewrite !GRing.sub0r. by intuition. 
(**) move => [/eqP -> H1] y y'. 
  elim.
    move => [/eqP -> /eqP ->]. rewrite !GRing.subr0. by intuition. 
    move => [/eqP -> H4]. by intuition. 
split. 
(* * *)
move => /= k k' /= x x'.
elim. 
(**) move => [/eqP -> /eqP ->]. 
  move => y y'. elim. 
    move => [/eqP -> /eqP ->]. rewrite !GRing.mulr0. by intuition. 
    move => [/eqP -> H3]. rewrite !GRing.mul0r. by intuition. 
(**) move => [/eqP -> H3]. 
  move => y y'. elim. 
    move => [/eqP -> /eqP ->]. rewrite !GRing.mulr0. by intuition. 
    move => [/eqP -> H4]. right. split => //.
    apply add_isDyadic => //. 
split. 
(* recip *)
move => k/= x x'.
elim. 
  move => [/eqP -> /eqP ->]. by rewrite (eq_refl _). 
  move => [/eqP -> H2]. 
case E: (x' == 0%R) => //.
(* It's not zero *)
  apply negbT in E. 
  right. split => //. 
  apply neg_isDyadic => //. 
split. 
(* abs *)
move => k/= x x'.
elim. 
  move => [/eqP -> /eqP ->]. rewrite (eq_refl _). rewrite !Num.Theory.normr_eq0.  intuition. 
  move => [/eqP -> H2]. intuition. 
split. 
(* sqrt *)
move => k/= x x'.
elim. 
  move => [/eqP -> /eqP ->]. rewrite Num.Theory.sqrtr0. intuition.  
  move => [/eqP -> H2]. right. split => //. simpl in k. 
  apply half_isDyadic => //.   
split. 
(* finish *)
Qed. 

(*---------------------------------------------------------------------------
   Now some applications.
   First we prove that the type of cube root contains only \x.0
   ---------------------------------------------------------------------------*)

Definition cuberootTy : Ty [::] := all Unit (scalar (#0 * #0 * #0)%Un --> scalar #0)%Ty.

Require Import div.

Lemma gcd_2n_3_is_1 n: gcdn (2 ^ n) 3 == 1%N.
Proof. rewrite gcdnC. induction n => //. by rewrite expnS Gauss_gcdl. Qed.

Lemma exp2third n : ~ (2 ^ n)%:R * (1 / 3%:R) \is a Qint.
Proof.
 rewrite -{1}(GRing.divr1 (2 ^ n)%:R) GRing.mulf_div !GRing.mul1r.
 rewrite Qint_def.
 have: denq ((2 ^ n)%:R%:~R / 3%:R) = 3%Q.
   apply (@coprimeq_den (2 ^ n)%:R 3). by rewrite natz /coprime gcd_2n_3_is_1.
 rewrite natz GRing.mulr1. move ->. 
 done. 
Qed. 

Lemma cuberootTrivial (f:F->F) : 
  semClosedTy ExpModelEnv cuberootTy f f -> 
  forall x, f x = 0.
Proof. rewrite /semClosedTy/=. move => H x. 
specialize  (H (1%:Q/3%:Q) x x).
destruct H => //. 
right. split => //. by exists 0%N. 
destruct H as [H0 H1]. by rewrite (eqP H0). 
destruct H as [H0 H1].
destruct H1 as [n H1].
contradiction (@exp2third n).  
Qed. 

