Require Import ssreflect ssrbool ssrfun seq eqtype ssralg.
Require Import ssrint rat ssrnum div intdiv. 

Require Import Relations.

Require Import exp ty tm model esem sem.

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
Delimit Scope Unit_scope with Un.

Definition scalar D (u: unitExpr D) : tyExpr D :=
  TyPrim Scalar (Cons u (Nil _)).  
Arguments Scope scalar [Unit_scope].

Open Scope Ty_scope.
Definition ExAxioms : seq (Ax ExSIG) :=
[::
  (* right identity *)
  [::Unit] |- #0 * UnitOne<> === #0;

  (* commutativity *)
  [::Unit;Unit] |- #0 * #1 === #1 * #0;

  (* associativity *)
  [::Unit;Unit;Unit] |- #0 * (#1 * #2) === (#0 * #1) * #2;

  (* right inverse *)
  [::Unit] |- #0 * (UnitInv<#0>) === UnitOne<>;

  (* abs is a group homomorphism *)
  [::Unit;Unit] |- UnitAbs<(#0 * #1)> === UnitAbs<#0> * UnitAbs<#1>
]%Un.

Definition uequiv D : relation (unitExpr D) := equiv (sig:=ExSIG) ExAxioms.

Definition TyOption D (t: tyExpr D) := (t + TyUnit _)%Ty.

Definition Gops : Ctxt [::] := 
[::
  (* variable 0: zero *)
  all Unit (scalar #0);   

  (* variable 1: one *)
  scalar UnitOne<>;

  (* variable 2: + *)
  all Unit (scalar #0 --> scalar #0 --> scalar #0);

  (* variable 3: - *)
  all Unit (scalar #0 --> scalar #0 --> scalar #0);

  (* variable 4: * *)
  all Unit (all Unit (scalar #0 --> scalar #1 --> scalar (#0 * #1)%Un));

  (* variable 5: reciprocal *)
  all Unit (scalar #0 --> TyOption (scalar (UnitInv<#0>)));

  (* variable 6: abs *)
  all Unit (scalar #0 --> scalar (UnitAbs<#0>))
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
   Need field to be non-trivial (more than one element!) 
   ---------------------------------------------------------------------------*)

(* Non-zero scale factor type *)
Structure scaling : Type := Scaling {tval :> F; _ : tval != 0%R}.

Canonical scaling_subType := Eval hnf in [subType for tval by scaling_rect].
Definition scaling_eqMixin := Eval hnf in [eqMixin of scaling by <:]. 
Canonical scaling_eqType := Eval hnf in EqType scaling scaling_eqMixin.  
Implicit Type t : scaling.

Variable NonTrivial: exists s:scaling, val s != 1%R.


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

(* Essentially unary *)
Definition ExpModelEnv := mkModelEnv (interpPrim := interpPrim) (M:=ExpModel)
  (fun X => 
    match X with Scalar => 
    fun expArgs => 
    fun x y => (x==0%R /\ y==0%R) \/ 
               (x == y /\ expArgs.1 \is a Qint) end). 

(* Interpretation of pervasives preserve exponent relations *)
Lemma eta_ops_okForExp : semCtxt (emptyRelEnv ExpModelEnv) eta_ops eta_ops.
Proof.
split. 
(* 0 *)
move => k/=.
intuition. 
split.
(* 1 *)
right. split. done. intuition.  split. 
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
   Simples model we can use to prove trivial inhabitation of square root type
   ---------------------------------------------------------------------------*)

Definition EvenInterpretation := mkInterpretation
  (interpSrt := fun s => int)
  (fun p =>
   match p with
     UnitOne  => fun args => 0%R
   | UnitProd => fun args => (args.1 + args.2.1)%R
   | UnitAbs  => fun args => args.1
   | UnitInv  => fun args => (-args.1)%R
   end ).

Definition EvenModel : Model ExAxioms. 
Proof. 
apply (@mkModel _ ExAxioms EvenInterpretation). 
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

(*---------------------------------------------------------------------------
   Simplest model we can use to prove trivial inhabitation of square root type
   ---------------------------------------------------------------------------*)

Definition BoolInterpretation := mkInterpretation
  (interpSrt := fun s => bool)
  (fun p =>
   match p with
     UnitOne  => fun args => false
   | UnitProd => fun args => args.1 != args.2.1
   | UnitAbs  => fun args => args.1
   | UnitInv  => fun args => args.1
   end ).

Definition BoolModel : Model ExAxioms. 
Proof. 
apply (@mkModel _ ExAxioms BoolInterpretation). 
split. 
(* right identity *)
move => /= [x u] /=.
by case: x. 
split. 
(* commutativity *)
move => /= [x [y u]] /=.
by case: x; case: y. 
split. 
(* associativity *)
move => /= [x [y [z u]]] /=. 
by case: x; case: y; case: z. 
split.
(* right inverse *)
move => /= [x u] /=. 
by case: x. 
split.
(* homomorphism of abs *)
move => /= [x u] /=. 
by case: x.
(* end *)
done. 
Defined. 

(* Essentially unary *)
Definition BoolModelEnv := mkModelEnv (interpPrim := interpPrim) (M:=BoolModel)
  (fun X  => 
    match X with Scalar => 
    fun args => 
    if args.1
    then fun x y => x == 0%R /\ y == 0%R 
    else fun x y => x = y end). 

(* Interpretation of pervasives preserve bool relations *)
Lemma eta_ops_okForBool : semCtxt (emptyRelEnv BoolModelEnv) eta_ops eta_ops.
Proof.
split. 
(* 0 *)
move => k/=.
by case: k.  
split.
(* 1 *)
intuition. split. 
(* + *)
move => k/=.
move => x x'.
case: k. 
+ move => [/eqP-> /eqP->] y y' [/eqP-> /eqP->]. 
split; by rewrite GRing.addr0.  
+ by move => -> y y' ->. 
split.
(* - *)
move => k/=.
move => x x'.
case: k. 
+ move => [/eqP-> /eqP->] y y' [/eqP-> /eqP->]. 
split; by rewrite GRing.subr0.  
+ by move => -> y y' ->. 
split. 
(* * *)
move => /=k/=k'.
move => /=x x'.
case: k.  
+ case: k'. 
  - move => [/eqP-> /eqP->] y y' [/eqP-> /eqP->]. done. 
  - move => -> y y' [/eqP-> /eqP->] /=. by rewrite GRing.mulr0. 
+ case: k'. 
  - move => [/eqP-> /eqP->] y y' ->. by rewrite GRing.mul0r. 
  - move => -> y y' ->. done. 
split.   
(* recip *)
move => /=k.
move => /=x x'. 
case: k. 
+  move => [/eqP-> /eqP->]. by rewrite (eq_refl _). 
+ move ->.  
  case E: (x' == 0%R) => //.  
split. 
(* abs *)
move => /=k.
move => /=x x'. 
case: k. 
+ move => [/eqP-> /eqP->]. by rewrite Num.Theory.normr0. 
+ move => ->. done. 
split. 
(* finish *)
Qed. 

(*---------------------------------------------------------------------------
   Now some applications.
   First we prove that the type of square root contains only \x.0
   ---------------------------------------------------------------------------*)
Definition sqrtTy : Ty [::] := all Unit (scalar (#0 * #0)%Un --> scalar #0)%Ty.

Open Scope ring_scope.
Lemma sqrtTrivial (f:F->F) : 
  semClosedTy BoolModelEnv sqrtTy f f -> 
  forall x, f x = 0.
Proof. rewrite /semClosedTy/=. move => H x. 
specialize  (H true x x).
destruct H; intuition.  
by rewrite (eqP H0). 
Qed. 

(*
(*---------------------------------------------------------------------------
   Now some applications.
   First we prove that the type of square root contains only \x.0
   ---------------------------------------------------------------------------*)

Definition sqrtTy : Ty [::] := all Unit (scalar (#0 * #0)%Un --> scalar #0)%Ty.

Open Scope ring_scope.
Lemma sqrtTrivial (f:F->F) : 
  semClosedTy ExpModelEnv sqrtTy f f -> 
  forall x, f x = 0.
Proof. rewrite /semClosedTy/=. move => H x. 
specialize  (H (1%:Q/2%:Q) x x).
destruct H; intuition.  
by rewrite (eqP H0). 
Qed. 

*)

(*---------------------------------------------------------------------------
   Next we prove that the type of squaring exhibits a scaling property
   ---------------------------------------------------------------------------*)

Definition sqrTy : Ty [::] := all Unit (scalar #0 --> scalar (#0 * #0)%Un)%Ty.

Lemma sqrScaling (f:F->F) :   
  semClosedTy ScalingModelEnv sqrTy f f -> 
  forall k, k != 0 ->
  forall x, f (k * x) = k^2 * f x.
Proof. rewrite /semClosedTy/=. move => H k neq x. 
apply (H (Scaling neq) x (k*x) (refl_equal _)). 
Qed. 

Require Import equivalence Casts.

Definition UTm D (G: Ctxt D) (ty: tyExpr D) := 
  Tm ExAxioms (G ++ apSubCtxt (piAll D) Gops) ty. 

Definition UTmVar D (G: Ctxt D) (ty: tyExpr D) := 
  TmVar (G ++ apSubCtxt (piAll D) Gops) ty. 

Definition apUnit D G (u: unitExpr D) (ty: tyExpr (Unit::D)) (M: UTm G (all Unit ty)) :
  UTm G (apSubTy <<u>> ty) :=
  UNIVAPP u M. 

Definition UAPP D (G: Ctxt D) (t1 t2: Ty D) (M1: UTm G (t1 --> t2)) (M2: UTm G t1) :
  UTm G t2 := APP M1 M2. 

Definition UABS D (G: Ctxt D) (t1 t2: Ty D) (M: UTm (t1::G) t2) : UTm G (t1-->t2) := 
  ABS M.

Definition UVAR0 D (t: Ty D) G : UTm (t::G) t := 
  VAR _ (ixZ _ _). 

Definition UUABS D G (t: tyExpr _) M : UTm G (all Unit t) := 
  UNIVABS (A:=ExAxioms) (s:=Unit) (D:=D) (G:=G ++ apSubCtxt (piAll D) Gops) (t:=t) M.

Fixpoint shVar D (G': Ctxt D) (t: tyExpr D) (v: UTmVar [::] t) : UTmVar G' t
 := if G' is t'::G' return UTmVar G' t then ixS _ (shVar G' v) else v. 

Definition zeroVar D : @UTmVar D [::] _ := (ixZ _ _).
Definition oneVar  D : @UTmVar D [::] _ := ixS _ (ixZ _ _). 
Definition addVar  D : @UTmVar D [::] _ := ixS _ (ixS _ (ixZ _ _)). 
Definition subVar  D : @UTmVar D [::] _ := ixS _ (ixS _ (ixS _ (ixZ _ _))). 
Definition mulVar  D : @UTmVar D [::] _ := ixS _ (ixS _ (ixS _ (ixS _ (ixZ _ _)))). 
Definition recipVar D : @UTmVar D [::] _:= ixS _ (ixS _ (ixS _ (ixS _ (ixS _ (ixZ _ _))))). 
Definition absVar  D : @UTmVar D [::] _ := ixS _ (ixS _ (ixS _ (ixS _ (ixS _ (ixS _ (ixZ _ _)))))). 

Definition zeroAt D G (u: unitExpr D) : UTm G (scalar u) := 
  apUnit u (VAR _ (shVar G (zeroVar _))). 

Definition constOne D (G:Ctxt D) : UTm G (scalar UnitOne<>) := 
  VAR _ (shVar G (oneVar _)).

Definition addAt D G (u: unitExpr D) := 
  apUnit u (VAR _ (shVar G (addVar _))). 
Definition add D G (u: unitExpr D) (M1 M2: UTm G (scalar u)) : UTm G (scalar u) := 
  UAPP (UAPP (addAt G u) M1) M2.

Definition subAt D G (u: unitExpr D) := 
  apUnit u (VAR _ (shVar G (subVar _))). 
Definition sub D G (u: unitExpr D) (M1 M2: UTm G (scalar u)) : UTm G (scalar u) := 
  UAPP (UAPP (subAt G u) M1) M2.

Definition mulAt D G (u1: unitExpr D) : 
  UTm G (all Unit (scalar (apSub (liftSub _ <<u1>>) #0) --> 
                 scalar (shExp _ u1) --> 
                 scalar (apSub (liftSub _ <<u1>>) #0 * 
                         shExp _ u1)%Un))
  := apUnit u1 (VAR _ (shVar G (mulVar _))).  

(* Problem: coq doesn't know that the _ don't need contain variables substituted for by u2 *)
Definition mulAt1 D G u1 (u2: unitExpr D) :
  UTm G (scalar u2 --> scalar (apSub <<u2>> (shExp _ u1)) 
                   --> scalar (u2 * (apSub <<u2>> _))%Un) := 
  apUnit u2 (mulAt G u1). 

Lemma mulCast D G u1 (u2: unitExpr D)  : 
  UTm G (scalar u2 --> scalar (apSub <<u2>> (shExp _ u1)) 
                   --> scalar (u2 * (apSub <<u2>> (shExp _ u1)))%Un) =
  UTm G (scalar u2 --> scalar u1 --> scalar (u2 * u1)%Un). 
Proof. by rewrite (proj1 (apSubSingleShift _)). Qed. 

Definition mulAt2 D G (u1 u2: unitExpr D) : 
  UTm G (scalar u2 --> scalar u1 --> scalar (u2 * u1)%Un) := mulAt1 G u1 u2 :? mulCast G u1 u2.

Definition recipAt D G (u: unitExpr D) := 
  apUnit u (VAR _ (shVar G (recipVar _))). 
Definition recipOf D G (u: unitExpr D) (M: UTm G (scalar u)): 
  UTm G (TyOption (scalar (UnitInv<u>))) := 
  UAPP (recipAt G u) M.

Definition absAt D G (u: unitExpr D) := 
  apUnit u (VAR _ (shVar G (absVar _))). 
Definition absOf D G (u: unitExpr D) (M: UTm G (scalar u)) : UTm G (scalar (UnitAbs<u>)) := 
  UAPP (absAt G u) M.


(*---------------------------------------------------------------------------
   Now a really trivial isomorphism. Zero is the only polymorphic scalar!

     (forall s, real<s>)   ~   unit
   ---------------------------------------------------------------------------*)
Lemma polyZeroIso : 
  iso ExAxioms eta_ops (all Unit (scalar #0)) (TyUnit [::]).
Proof.
  set I: UTm [::] (all Unit (scalar #0) --> TyUnit [::]) := UABS (UNIT _ _). 

  set J: UTm [::] (TyUnit [::] --> all Unit (scalar #0)) := UABS (VAR _ (shVar _(zeroVar _))).

  exists I. 
  exists J. 

split. 

move => M. 
apply: (semEq_implies_ctxtEq eta_ops_ok) => rho /=eta1 eta2 eta12/=. 
move => k/=. 
(* Abstraction theorem *)
have A:= Abstraction _ eta_ops_ok.  
specialize (A _ M). simpl in A. 
rewrite cast_UIP/=. rewrite GRing.mulr0.

(* From forall k:scaling, x = k*x we want to derive that x=0.
   There must be an easier way to do this! *)
destruct NonTrivial as [k' Hk']. 
have A1 := A k'. 
case E: (interpTm M eta_ops == 0). by rewrite (eqP E). 
have NEQ: interpTm M eta_ops != 0 by by rewrite E. 
symmetry in A1. rewrite GRing.mulrC in A1. 
rewrite -{2}(GRing.mulr1 (interpTm M eta_ops)) in A1. 
have M1 := GRing.mulfI NEQ A1. 
simpl in Hk'. rewrite M1 eq_refl in Hk'.
done. 


move => M. 
apply: (semEq_implies_ctxtEq eta_ops_ok).  
done. 
Qed. 

(*---------------------------------------------------------------------------
   Now a slightly more complex one.

     (forall s, real<s> -> real<s>)   ~   real<1>
   ---------------------------------------------------------------------------*)
(*
Lemma polyUnaryIso : 
  iso (D:=[::]) ExAxioms eta_ops (all Unit (scalar #0 --> scalar #0)) (scalar UnitOne<>).
Proof.
  set t1 := all Unit (scalar #0 --> scalar #0). 
  set t2 := scalar UnitOne<>.

  (* ##2 is the second element of eta_ops i.e. 1 *)
  (* fun x: (forall s. scalar<s> -> scalar<s>) => x 1 1 *)
  set I: UTm (D:=[::]) [::] (t1 --> t2) := 
    UABS (UAPP (apUnit UnitOne<> (UVAR0 t1 _)) (constOne _)).  
  exists I. 

  (* Not exactly readable yet... *)
  (* fun y: scalar<1> => fun s => fun z: scalar<s> => z / y *)
  set J: UTm (D:=[::]) [::] (t2 --> t1) :=
    UABS
      (UUABS (t:=scalar #0 --> scalar #0) 
        (UABS (t1:=scalar #0) (UVAR0 _ _))). (shTmTm _ (zeroAt _ _)))). UVAR0 (scalar #0) [::scalar UnitOne<>;  _))). (UAPP (UAPP (UVAR0 _))))). 
        (APP (APP ##5 ##0) (APP ##6 ##1)))).  

  exists J. 


  split. 

move => M.
apply: (semEq_implies_ctxtEq eta_ops_ok) => rho /=eta1 eta2 eta12/=.
move => k x y xy.
rewrite xy.   
admit. 


move => M.
apply: (semEq_implies_ctxtEq eta_ops_ok).  move => rho /=eta1 eta2 eta12.
rewrite cast_UIP/=.  
rewrite cast_UIP/=. 
rewrite cast_id. 
rewrite GRing.mul1r. 


done. rewrite /interpTm. move => k x y xy.

  exists I, J. 

split. 

move => M. 
apply: (semEq_implies_ctxtEq eta_ops_ok) => rho /=eta1 eta2 eta12/=. 
move => k/=. 
*)