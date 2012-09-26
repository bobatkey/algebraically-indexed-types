Require Import ssreflect ssrbool ssrfun seq.
Require Import Relations Program.Equality.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "c '<' x , .. , y '>'" (at level 20, x, y at level 10).
Reserved Notation "c '<>'" (at level 2). 
Reserved Notation "c '_<' x , .. , y '>'" (at level 20, x, y at level 10).
Reserved Notation "c '_<>' " (at level 2). 

(*---------------------------------------------------------------------------
   Generally useful stuff for indexed products.
   We have a type T of "sorts", "kinds", "types", or whatever.
   Then I is an interpretation of T into Type.

   The type "Ix ts t" is a witness of t's position in the sequence ts, typically
   used to represent variables in strongly-typed terms.

   The type "Env ts" is used for environments with domain ts, with a lookup operation
   that takes env: Env ts, ix: Ix ts t, and returns a value of type I t. 
   ---------------------------------------------------------------------------*)
Section Env.

Variable T: Type.

Inductive Ix : seq T -> T -> Type :=  
| ixZ ts t : Ix (t::ts) t
| ixS ts t t' : Ix ts t -> Ix (t'::ts) t.

Variable I: T -> Type.

Fixpoint Env (ts: seq T): Type := if ts is t::ts then (I t * Env ts)%type else unit.

Fixpoint lookup ts t (v: Ix ts t) : Env ts -> I t :=
  match v with 
  | ixZ _ _     => fun env => env.1
  | ixS _ _ _ v => fun env => lookup v env.2
  end.

Lemma lookupZ ts t (env: Env (t::ts)) : lookup (ixZ _ _) env = env.1.
Proof. done. Qed.

Lemma lookupS ts t t' (v: Ix ts t) (env: Env (t'::ts)) : lookup (ixS _ v) env = lookup v env.2.
Proof. done. Qed.

Lemma envExtensional ts (env env': Env ts) : 
  (forall (t:T) (v: Ix ts t), lookup v env = lookup v env') -> env = env'.
Proof. induction ts => //. by elim env; elim env'. 
elim env => [v env1] {env}. 
elim env' => [v' env1'] {env'}. move => H. 
have:= H _ (ixZ _ _). simpl. move ->. 
rewrite (IHts env1 env1') => //. 
move => t' v''. by specialize (H t' (ixS _ v'')). 
Qed. 

End Env.

Fixpoint mapEnv T (I J:T -> Type) ts (f: forall t, I t -> J t) : Env I ts -> Env J ts  := 
  if ts is _::_ 
  then fun env => (f _ env.1, mapEnv f env.2)
  else fun env => tt.

Lemma mapCompose T (I J K: T -> Type) ts (f: forall t, J t -> K t) (g: forall t, I t -> J t) 
  (env: Env I ts) : mapEnv f (mapEnv g env) = mapEnv (fun s x => f _ (g _ x)) env.
Proof. induction ts => //. by rewrite /= IHts. Qed. 

Section Syntax.

(*---------------------------------------------------------------------------
   Everything is parameterized on a signature, which specifies a type
   for index sorts, for primitive type constructors, and for
   index-level constructors, along with their arities.

   Axioms are introduced later. 
   ---------------------------------------------------------------------------*)
Structure SIG := mkSIG {
  (* Type of sorts e.g. one sort: unit-of-measure *)
  Srt: Type;                  

  (* Type of primitive type constructors e.g. one primitive: real *)
  PrimType: Type;             

  (* Type of index-level constructors e.g. three unit operators, 1 * and inv *)
  IndexOp: Type;              

  (* Arity of index-level operators, e.g. 1:unit, * : (unit,unit)unit, inv: (unit)unit *)
  opArity: IndexOp -> seq Srt * Srt;

  (* Arity of primitive type constructors, e.g. real (unit) *)
  tyArity: PrimType -> seq Srt
}.

(* In this section, assume some sig: SIG *)
Variable sig: SIG.

(* Index variables each have a sort *)
Definition IxCtxt := seq (Srt sig). 

(* Index variables, in context. D is \Delta in paper *)
Definition Var (D: IxCtxt) (s:Srt sig) := Ix D s. 

(* Well-sorted index expressions, in context. D is \Delta in paper *)
Inductive Exp (D: IxCtxt) : Srt sig -> Type :=
| VarAsExp s :> Var D s -> Exp D s
| AppCon op : Exps D (opArity op).1 -> Exp D (opArity op).2

(* Well-sorted sequences of index expressions, in context *)
with Exps (D: IxCtxt) : IxCtxt -> Type :=
| Nil : Exps D nil
| Cons s ss : Exp D s -> Exps D ss -> Exps D (s::ss).

Implicit Arguments AppCon [D].
Implicit Arguments Nil [D]. 

Scheme Exp_ind2 := Induction for Exp Sort Prop
with Exps_ind2 := Induction for Exps Sort Prop.

Combined Scheme Exp_Exps_ind from Exp_ind2, Exps_ind2. 

Ltac Rewrites E := 
  (intros; simpl; try rewrite E; 
   repeat (match goal with | [H:context[_=_] |- _] => rewrite H end); 
   auto).

(* Renamings: maps from variables to variables *)
Definition Ren D D' := Env (Var D') D. 
Definition apRenVar D D' (R: Ren D D') s v : Var D' s := lookup v R. 
Definition nilRen D : Ren [::] D := tt.
Definition consRen D D' s v (R: Ren D D') : Ren (s::D) D' := (v,R). 

Lemma apRenVarZ D D' s (R: Ren (s::D) D') : apRenVar R (ixZ _ _) = R.1.  
Proof. apply lookupZ. Qed. 

Lemma apRenVarS D D' s s' (R: Ren (s::D) D') (v: Var D s') : apRenVar R (ixS _ v) = apRenVar R.2 v.  
Proof. apply lookupS. Qed. 

Definition shiftRen D D' s : Ren D D' -> Ren D (s::D') := mapEnv (fun s => ixS _). 

Lemma apRenVarShift D D' s' (R: Ren D D') s (v: Var D s) : 
  apRenVar (shiftRen s' R) v = ixS _ (apRenVar R v). 
Proof. dependent induction v => //. by rewrite apRenVarS IHv. Qed. 

Definition liftRen D D' s (R: Ren D D'): Ren (s::D) (s::D') := 
  consRen (ixZ _ _) (shiftRen s R). 

Lemma apRenVarLift D D' s s' (R: Ren D D') (v: Var D s) : 
  apRenVar (liftRen s' R) (ixS _ v) = ixS _ (apRenVar R v). 
Proof. by rewrite /liftRen/= apRenVarShift. Qed. 

Fixpoint idRen (D: IxCtxt) : Ren D D := 
  if D is s::D' 
  then (liftRen s (idRen D'))
  else tt.    

Lemma apRenVarId D : forall s (v:Var D s), apRenVar (idRen _) v = v. 
Proof. dependent induction v => //. by rewrite apRenVarS apRenVarShift IHv. Qed. 

Fixpoint apRen D D' s (r: Ren D D') (ix: Exp D s): Exp D' s :=
  match ix with
  | VarAsExp _ v => VarAsExp (apRenVar r v)
  | AppCon op ixs => AppCon op (apRenSeq r ixs)
  end
with apRenSeq D D' ss (r: Ren D D') (ixs: Exps D ss) : Exps D' ss  :=
  if ixs is Cons _ _ ix ixs 
  then Cons (apRen r ix) (apRenSeq r ixs) 
  else Nil.

Lemma apRenExtensional E E' (R R': Ren E E') : 
  (forall s (v: Var E s), apRenVar R v = apRenVar R' v) -> R = R'. 
Proof. apply envExtensional. Qed. 

Definition shExp D s s' : Exp D s -> Exp (s'::D) s := apRen (shiftRen s' (idRen D)). 
Definition shExpSeq D ss s' : Exps D ss -> Exps (s'::D) ss := apRenSeq (shiftRen s' (idRen D)). 
Definition RcR D D' D'' (R: Ren D' D'') : Ren D D' -> Ren D D'' := mapEnv (apRenVar R).

Lemma shiftRenRcR E : forall E' E'' s (R:Ren E' E'') (R':Ren E E'),
  shiftRen s (RcR R R') = RcR (shiftRen s R) R'. 
Proof. rewrite /shiftRen. rewrite /RcR. induction E => //. 
move => E' E'' s R R'. 
destruct R' as [v R']. by rewrite /= IHE apRenVarShift. 
Qed. 

Lemma apVarRcR E E' E'' (r:Ren E' E'') (r':Ren E E') :
  (forall s (v:Var E s), apRenVar (RcR r r') v = apRenVar r (apRenVar r' v)).
Proof. dependent induction v => //. destruct r' as [v' r']. apply (IHv r'). Qed. 

Lemma apRcR E E' E'' (r:Ren E' E'') (r':Ren E E') :
  (forall s (e:Exp E s), apRen (RcR r r') e = apRen r (apRen r' e)) /\
  (forall ss (es:Exps E ss), apRenSeq (RcR r r') es = apRenSeq r (apRenSeq r' es)). 
Proof. apply Exp_Exps_ind; Rewrites apVarRcR. Qed.


(* Substitutions: maps from variables to expressions *)
Definition Sub D D' := Env (Exp D') D. 
Definition apSubVar D D' (S: Sub D D') s v : Exp D' s := lookup v S. 
Definition nilSub D : Sub [::] D := tt.
Definition consSub D D' s e (S: Sub D D') : Sub (s::D) D' := (e,S). 
Definition tlSub D D' s (S: Sub (s::D) D') : Sub D D' := S.2.
Definition hdSub D D' s (S: Sub (s::D) D') : Exp D' s := S.1.

Lemma apSubVarZ D D' s (S: Sub (s::D) D') : apSubVar S (ixZ _ _) = S.1.  
Proof. apply lookupZ. Qed. 

Lemma apSubVarS D D' s s' (S: Sub (s::D) D') (v: Var D s') : apSubVar S (ixS _ v) = apSubVar S.2 v.  
Proof. apply lookupS. Qed. 

Definition shiftSub D D' s : Sub D D' -> Sub D (s::D') := mapEnv (fun _ => shExp s).

Lemma apSubVarShift D D' s s' (S: Sub D D') (v: Var D s) : 
  apSubVar (shiftSub s' S) v = shExp _ (apSubVar S v). 
Proof. dependent induction v => //. by rewrite apSubVarS IHv. Qed. 

Fixpoint subAsExps D D' : Sub D' D -> Exps D D' :=
  if D' is s::D' 
  then fun S => Cons (hdSub S) (subAsExps (tlSub S))
  else fun S => Nil. 

Fixpoint expsAsSub_inner D D' (ixs : Exps D D') : Sub D' D :=
  match ixs as _ in (Exps _ D') return Sub D' D with
    | Nil => nilSub D
    | Cons s ss e ixs => consSub e (expsAsSub_inner ixs)
  end.

Global Coercion expsAsSub D D' (ixs: Exps D D') : Sub D' D := expsAsSub_inner ixs.

Fixpoint apSub D D' s (S: Sub D D') (ix: Exp D s): Exp D' s :=
  match ix with
  | VarAsExp _ v => apSubVar S v
  | AppCon op ixs => AppCon op (apSubSeq S ixs)
  end
with apSubSeq D D' ss (S: Sub D D') (ixs: Exps D ss) : Exps D' ss  :=
  if ixs is Cons _ _ ix ixs 
  then Cons (apSub S ix) (apSubSeq S ixs) 
  else Nil.

Lemma apSubAppCon D D' (S: Sub D D') op (ixs: Exps D _) : 
  apSub S (AppCon op ixs) = AppCon op (apSubSeq S ixs). 
Proof. done. Qed.

Lemma apSubSeqCons D D' (S: Sub D D') s ss (e: Exp D s) (es: Exps D ss) :
  apSubSeq S (Cons e es) = Cons (apSub S e) (apSubSeq S es).
Proof. done. Qed.

Definition liftSub D D' s (S: Sub D D') : Sub (s::D) (s::D') :=
  (VarAsExp (ixZ _ _), shiftSub s S). 

Lemma apSubVarLift D D' s s' (S: Sub D D') (v: Var D s) : 
  apSubVar (liftSub s' S) (ixS _ v) = shExp _ (apSubVar S v). 
Proof. by rewrite /liftSub/= apSubVarShift. Qed. 

Lemma apSubLiftAndSeq D D' s' (S: Sub D D') :
  (forall s (e: Exp D s), apSub (liftSub s' S) (shExp s' e) = shExp s' (apSub S e)) /\
  (forall ss (es: Exps D ss), apSubSeq (liftSub s' S) (shExpSeq s' es) = shExpSeq s' (apSubSeq S es)). 
Proof. 
apply Exp_Exps_ind => //. 
+ move => s v. by rewrite /= -apSubVarLift apRenVarShift apRenVarId. 
+ move => op es IH. by rewrite/= IH.  
+ move => s ss e IH1 es IH2. rewrite /shExp in IH1, IH2. simpl. by rewrite IH1 IH2. Qed.

Corollary apSubLift E E' s s' (S: Sub E E') (e: Exp E s) : 
  apSub (liftSub s' S) (shExp s' e) = shExp s' (apSub S e). 
Proof. by apply apSubLiftAndSeq. Qed.


Definition ScR D D' D'' (S: Sub D' D'') : Ren D D' -> Sub D D'' := 
  mapEnv (apSubVar S).

Definition RcS D D' D'' (R: Ren D' D'') : Sub D D' -> Sub D D'' :=
  mapEnv (fun _ => apRen R). 

Definition ScS D D' D'' (S: Sub D' D'') : Sub D D' -> Sub D D'' :=
  mapEnv (fun _ => apSub S). 

Fixpoint idSub (D: IxCtxt) : Sub D D := 
  if D is s::D' 
  then (liftSub s (idSub D'))
  else tt.    

Lemma liftSubId D s : liftSub _ (@idSub D) = @idSub (s::D). 
Proof. done. Qed.

Lemma apSubVarId D : forall s (v:Var D s), apSubVar (idSub _) v = v. 
Proof. dependent induction v => //. rewrite apSubVarS apSubVarShift IHv. 
by rewrite /shExp/= apRenVarShift apRenVarId. 
Qed. 

Lemma apSubId D :
  (forall s (e : Exp D s), apSub (idSub _) e = e) /\ 
  (forall ss (es: Exps D ss), apSubSeq (idSub _) es = es). 
Proof. apply Exp_Exps_ind; Rewrites liftSubId. apply apSubVarId. Qed.

Lemma apSubExtensional E E' (S S': Sub E E') : 
  (forall s (v: Var E s), apSubVar S v = apSubVar S' v) -> S = S'. 
Proof. apply envExtensional. Qed. 

Lemma apVarScR E E' E'' (S:Sub E' E'') (R:Ren E E') : 
  (forall s (v:Var E s), apSubVar (ScR S R) v = apSubVar S (apRenVar R v)).
Proof. dependent induction v => //. destruct R as [v' R]. simpl. apply IHv.  Qed. 

Lemma apScR E E' E'' (S:Sub E' E'') (R:Ren E E') : 
  (forall s (e:Exp E s), apSub (ScR S R) e = apSub S (apRen R e)) /\
  (forall ss (es:Exps E ss), apSubSeq (ScR S R) es = apSubSeq S (apRenSeq R es)).
Proof. apply Exp_Exps_ind; Rewrites apVarScR. Qed.

Lemma apVarRcS E E' E'' (R:Ren E' E'') (S:Sub E E') : 
  (forall s (v:Var E s), apSubVar (RcS R S) v = apRen R (apSubVar S v)).
Proof. dependent induction v => ///=. destruct S as [e S]. apply IHv. Qed. 

Lemma apRcS E E' E'' (R:Ren E' E'') (S:Sub E E') : 
  (forall s (e:Exp E s), apSub (RcS R S) e = apRen R (apSub S e)) /\
  (forall ss (es:Exps E ss), apSubSeq (RcS R S) es = apRenSeq R (apSubSeq S es)).
Proof. apply Exp_Exps_ind; Rewrites apVarRcS. Qed.

Lemma apVarScS E E' E'' (S:Sub E' E'') (S':Sub E E') : 
  (forall s (v:Var E s), apSubVar (ScS S S') v = apSub S (apSubVar S' v)).
Proof. dependent induction v => //. destruct S' as [e S']. simpl. apply IHv. Qed. 

Lemma apScS E E' E'' (S:Sub E' E'') (S':Sub E E') : 
  (forall s (e:Exp E s), apSub (ScS S S') e = apSub S (apSub S' e)) /\
  (forall ss (es:Exps E ss), apSubSeq (ScS S S') es = apSubSeq S (apSubSeq S' es)).
Proof. apply Exp_Exps_ind; Rewrites apVarScS. Qed.

Lemma ScS_assoc E E' E'' E''' (S1: Sub E'' E''') (S2: Sub E' E'') (S3: Sub E E') :
  ScS S1 (ScS S2 S3) = ScS (ScS S1 S2) S3.
Proof. apply apSubExtensional => s v.
rewrite !apVarScS. by rewrite (proj1 (apScS _ _)). 
Qed. 

Lemma idScS E E' (S: Sub E' E) :
  ScS (idSub E) S = S.
Proof. apply apSubExtensional => s v. rewrite apVarScS. by rewrite (proj1 (apSubId _)). 
Qed.

Lemma shiftSubDef E E' s (S: Sub E E'): shiftSub s S = RcS (shiftRen s (idRen E')) S.
Proof. apply apSubExtensional => s' v. rewrite /RcS/=. by  rewrite apSubVarShift. Qed. 

Lemma shiftApSubAndSeq D D' s' (S : Sub D D'):
  (forall s (e:Exp D s), shExp s' (apSub S e) = apSub (shiftSub s' S) e) /\
  (forall ss (es:Exps D ss), shExpSeq s' (apSubSeq S es) = apSubSeq (shiftSub s' S) es). 
Proof. apply Exp_Exps_ind => //. 
+ move => s v. dependent induction v => //. by rewrite IHv. 
+ move => op es IH. by rewrite /= -IH.
+ move => s ss e IH1 es IH2. by rewrite /= -IH1 -IH2. 
Qed. 

Corollary shiftApSub E E' s s' (S: Sub E E') (e: Exp E s) : 
  shExp s' (apSub S e) = apSub (shiftSub s' S) e. Proof.  by apply shiftApSubAndSeq. Qed. 

Lemma liftScS E : forall E' E'' s (S:Sub E' E'') (S':Sub E E'),
  liftSub s (ScS S S') = ScS (liftSub s S) (liftSub s S').
Proof. rewrite /liftSub/ScS. 
move => E' E'' s S S'.
rewrite/= /shiftSub!mapCompose. 
set m1 := (fun (s0: Srt sig) (x: Exp E' s0) => _). 
set m2 := (fun (s0: Srt sig) (x: Exp E' s0) => _). 
have: m1=m2. rewrite /m1/m2.
Require Import FunctionalExtensionality. 
apply functional_extensionality_dep => p. 
apply functional_extensionality => e.
by rewrite apSubLift.  
by move ->. 
Qed. 

Lemma ScExpsAsSub E' E'' (ixs: Exps E' E'') E (S: Sub E' E) :
expsAsSub (apSubSeq S ixs) = ScS S (expsAsSub ixs).
Proof. dependent induction ixs => ///=. by rewrite IHixs. Qed. 

(*---------------------------------------------------------------------------
   Having formalized the syntax of index expressions, we now move on to types
   ---------------------------------------------------------------------------*)

(* Well-sorted type expressions, in context *)
Inductive Ty (D: IxCtxt) :=
| TyUnit
| TyProd (t1 t2: Ty D) 
| TySum (t1 t2: Ty D)
| TyArr (t1 t2: Ty D)
| TyPrim (p: PrimType sig) (ixs: Exps D (tyArity p))
| TyAll s (t: Ty (s::D))
| TyExists s (t: Ty (s::D)).

(* Typing contexts: just a sequences of types *)
Definition Ctxt D := seq (Ty D). 

(* The action of an index substitution on types *)
Fixpoint apSubTy D D' (S: Sub D D') (t: Ty D): Ty D' :=
  match t with
  | TyUnit       => TyUnit _
  | TyProd t1 t2 => TyProd   (apSubTy S t1) (apSubTy S t2)
  | TySum  t1 t2 => TySum    (apSubTy S t1) (apSubTy S t2)
  | TyArr  t1 t2 => TyArr    (apSubTy S t1) (apSubTy S t2)
  | TyAll    s t => TyAll    (apSubTy (liftSub s S) t)
  | TyExists s t => TyExists (apSubTy (liftSub s S) t)
  | TyPrim p ixs => TyPrim   (apSubSeq S ixs)
  end.

Fixpoint apSubCtxt D D' (S: Sub D D') (G: Ctxt D) : Ctxt D' :=
  if G is t::G then apSubTy S t :: apSubCtxt S G else nil.

(* This is the operation \pi_{i:s} of the paper *)
Definition pi D s : Sub D (s::D) := shiftSub s (idSub D). 

Lemma apSubPiExpAndExps D s' :
  (forall s (e:Exp D s), apSub (shiftSub s' (idSub _)) e = apRen (shiftRen s' (idRen _)) e)/\
  (forall ss (es:Exps D ss), apSubSeq (shiftSub s' (idSub _)) es = apRenSeq (shiftRen s' (idRen _)) es).
Proof. apply Exp_Exps_ind => //. 
move => s v. by rewrite/= apSubVarShift apSubVarId. 
move => op e IH. by rewrite/= IH. 
move => s ss e IH es IH'. by rewrite /= IH IH'. 
Qed. 

Lemma apSubPi D s s' (e:Exp D s') : apSub (pi D s) e = shExp s e.
Proof. rewrite /shExp/pi. by rewrite (proj1 (apSubPiExpAndExps _ _)). Qed. 

Lemma liftSubDef E E' t (s:Sub E' E) : liftSub t s = consSub (VarAsExp (ixZ _ _)) (shiftSub _ s).
Proof. done. Qed. 

Lemma consPi D D' s e (S: Sub D D') : ScS (consSub e S) (pi D s) = S.
Proof. apply apSubExtensional => s' v. 
by rewrite apVarScS/pi apSubVarShift apSubVarId /= apRenVarShift apSubVarS/= apRenVarId. 
Qed. 

Lemma liftPi D D' s (S: Sub D D') : ScS (liftSub s S) (pi D s) = ScS (pi D' s) S.
Proof. rewrite /liftSub consPi. rewrite /pi. apply apSubExtensional => s' v. 
rewrite apSubVarShift. rewrite apVarScS. rewrite /shExp. 
by rewrite (proj1 (apSubPiExpAndExps _ _)). 
Qed. 

(*---------------------------------------------------------------------------
   Now we introduce equational theories for indices, induced by a set of
   axioms. The equational theory is lifted to types.
   ---------------------------------------------------------------------------*)

(* Well-sorted axiom, in context *)
Inductive Ax := mkAx D s (lhs: Exp D s) (rhs: Exp D s).

(* Equational theory induced by axioms *)
Inductive equiv D : forall s, seq Ax -> relation (Exp D s) :=
| EquivRefl s axs (e: Exp D s) : 
  equiv axs e e

| EquivSym s axs (e1 e2: Exp D s) : 
  equiv axs e1 e2 -> equiv axs e2 e1

| EquivTrans s axs (e1 e2 e3: Exp D s) : 
  equiv axs e1 e2 -> equiv axs e2 e3 -> equiv axs e1 e3

| EquivComp axs p (es es': Exps D _) : 
  equivSeq axs es es' -> equiv axs (AppCon p es) (AppCon p es')

| EquivByAxZ s axs D' sigma (e e':Exp D' s) : 
  equiv (mkAx e e' :: axs) (apSub sigma e) (apSub sigma e')

| EquivByAxS s ax axs (e e':Exp D s) : 
  equiv axs e e' ->
  equiv (ax :: axs) e e'

with equivSeq D : forall ss, seq Ax -> relation (Exps D ss) :=
| EquivNil axs : 
  equivSeq axs Nil Nil

| EquivCons axs s ss (e e': Exp D s) (es es': Exps D ss) : 
  equiv axs e e' -> equivSeq axs es es' -> equivSeq axs (Cons e es) (Cons e' es').

Scheme equiv_ind2 := Induction for equiv Sort Prop
with equivSeq_ind2 := Induction for equivSeq Sort Prop.

Combined Scheme equivBoth_ind from equiv_ind2, equivSeq_ind2. 

Lemma equivIsEquivalence As D s : equivalence _ (@equiv D s As).
Proof. 
split. 
move => x. apply EquivRefl. 
move => x y z. apply EquivTrans. 
move => x y. apply EquivSym. 
Qed. 

(* Equational theory lifted to types *)
Inductive equivTy D A : relation (Ty D) :=
| EquivTyRefl (t: Ty D) :
  equivTy A t t

| EquivTySym (t1 t2: Ty D) :
  equivTy A t1 t2 -> equivTy A t2 t1

| EquivTyTrans (t1 t2 t3: Ty D) : 
  equivTy A t1 t2 -> equivTy A t2 t3 -> equivTy A t1 t3

| EquivTyProd (t1 t1' t2 t2': Ty D) :
  equivTy A t1 t1' -> equivTy A t2 t2' ->
  equivTy A (TyProd t1 t2) (TyProd t1' t2')

| EquivTySum (t1 t1' t2 t2': Ty D) :
  equivTy A t1 t1' -> equivTy A t2 t2' ->
  equivTy A (TySum t1 t2) (TySum t1' t2')

| EquivTyArr (t1 t1' t2 t2': Ty D) :
  equivTy A t1 t1' -> equivTy A t2 t2' ->
  equivTy A (TyArr t1 t2) (TyArr t1' t2')

| EquivTyPrim (op: PrimType sig) (es es': Exps D _):
  equivSeq A es es' ->
  equivTy A (TyPrim (p:= op) es) (TyPrim es')

| EquivTyAll s (t t': Ty (s::D)) :
  equivTy A (D:=s::D) t t' ->
  equivTy A (TyAll t) (TyAll t')

| EquivTyExists s (t t': Ty (s::D)) :
  equivTy A (D:=s::D) t t' ->
  equivTy A (TyExists t) (TyExists t').

(*---------------------------------------------------------------------------
   Finally, we define terms
   ---------------------------------------------------------------------------*)
Definition TmVar D := Ix (T:= Ty D).

Variable A: seq Ax. 

Inductive Tm D (G: Ctxt D) : Ty D -> Type :=
| VAR t : TmVar G t -> Tm G t
| TYEQ t1 t2 : equivTy A t1 t2 -> Tm G t1 -> Tm G t2
| UNIT : Tm G (TyUnit _)
| PAIR t1 t2 : Tm G t1 -> Tm G t2 -> Tm G (TyProd t1 t2)
| PROJ1 t1 t2 : Tm G (TyProd t1 t2) -> Tm G t1
| PROJ2 t1 t2 : Tm G (TyProd t1 t2) -> Tm G t2
| INL t1 t2 : Tm G t1 -> Tm G (TySum t1 t2)
| INR t1 t2 : Tm G t2 -> Tm G (TySum t1 t2)
| CASE t1 t2 t : Tm G (TySum t1 t2) -> Tm (t1::G) t -> Tm (t2::G) t -> Tm G t
| ABS t1 t2 : Tm (t1::G) t2 -> Tm G (TyArr t1 t2)  
| APP t1 t2 : Tm G (TyArr t1 t2) -> Tm G t1 -> Tm G t2
| UNIVABS s t : Tm (D:=s::D) (apSubCtxt (pi D s) G) t -> Tm G (TyAll t)
| UNIVAPP s t e : Tm G (TyAll (s:=s) t) -> Tm G (apSubTy (consSub e (idSub _)) t)
| EXPACK s e t : Tm G (apSubTy (consSub e (idSub _)) t) -> Tm G (TyExists (s:=s) t)
| EXUNPACK s t t' : Tm G (TyExists t) -> 
                    Tm (D:=s::D) (t :: apSubCtxt (pi D s) G) (apSubTy (pi D s) t') -> Tm G t'
.

End Syntax.

Implicit Arguments AppCon [sig D].
Implicit Arguments TyPrim [sig D].

(* Some handy notation for applying expression constructors *)
Notation "c '<' x , .. , y '>'" := (AppCon c (Cons x .. (Cons y (Nil _)) .. )) : Exp_scope.
Notation "c '<>'" := (AppCon c (Nil _)) : Exp_scope.

Bind Scope Exp_scope with Exp. 
Delimit Scope Exp_scope with Exp. 

(* Some handy notation for applying type constructors *)
Notation "c '_<' x , .. , y '>'" := (TyPrim c (Cons x .. (Cons y (Nil _)) .. )) :Ty_scope.
Notation "c '_<>'" := (TyPrim c (Nil _)) : Ty_scope. 
Notation "D '|-' e '===' f" := (@mkAx _ D _ e f) (at level 80, e, f at next level).
Notation "t '-->' s" := (TyArr t s) (at level 55, right associativity) : Ty_scope.
Notation "t * s" := (TyProd t s) (at level 40, left associativity) : Ty_scope.
Notation "t + s" := (TySum t s) (at level 50, left associativity) : Ty_scope.

Notation "#0" := (VarAsExp (ixZ _ _)) : Ty_scope.
Notation "#1" := (VarAsExp (ixS _ (ixZ _ _))) : Ty_scope.
Notation "#2" := (VarAsExp (ixS _ (ixS _ (ixZ _ _)))) : Ty_scope.

Definition all sig D s (t:Ty (sig:=sig) (s::D)) := TyAll (s:=s) t.
Implicit Arguments all [sig D].

Delimit Scope Ty_scope with Ty.
Bind Scope Ty_scope with Ty.

(* This is lemma 2, part 1 *)
Lemma equivSubst sig D D' (S: Sub D D') : 
   (forall s A (e f: Exp (sig:=sig) _ s), 
    equiv A e f -> equiv A (apSub S e) (apSub S f))

/\ (forall ss A (es fs: Exps (sig:=sig) _ ss), 
    equivSeq A es fs -> equivSeq A (apSubSeq S es) (apSubSeq S fs)).
Proof.
apply equivBoth_ind.
(* EquivRefl *)
+ move => s A e. by apply: EquivRefl.
(* EquivSym *)
+ move => s A e1 e2 E1 E2. by apply: EquivSym.
(* EquivTrans *)
+ move => s A e1 e2 e3 _ E2 _ E4. by apply: EquivTrans E2 E4. 
(* EquivComp *)
+ move => A op es es' E1 E2. rewrite 2!apSubAppCon. by apply EquivComp. 
(* EquivByAxZ *)
+ move => s A D'' S' e e'. 
  rewrite -2!(proj1 (apScS S S')). by apply EquivByAxZ.       
(* EquivByAxS *)
+ move => s A As e e' E1 E2. by apply EquivByAxS. 
(* EquivNil *)
+ move => A. by apply: EquivNil.
(* EquivCons *)
+ move => A s ss e1 e2 es1 es2 E1 E2 E3 E4. rewrite 2!apSubSeqCons. by apply: EquivCons. 
Qed. 

(* This is lemma 2, part 2 *)
Lemma equivTySubst sig D A (t t': Ty (sig:=sig) D) :
  equivTy A t t' -> forall D' (S: Sub D D'), equivTy A (apSubTy S t) (apSubTy S t').
Proof.
move => E. induction E => D' S. 
(* EquivTyRefl *)
+ by apply: EquivTyRefl.
(* EquivTySym *)
+ by apply: EquivTySym.
(* EquivTyTrans *)
+ apply: EquivTyTrans => //. 
(* EquivTyProd *)
+ apply: EquivTyProd => //. 
(* EquivTySum *)
+ apply: EquivTySum => //. 
(* EquivTyArr *)
+ apply: EquivTyArr => //. 
(* EquivTyPrim *)
+ apply: EquivTyPrim. apply equivSubst => //.  
(* EquivTyAll *)
+ apply: EquivTyAll. apply IHE. 
(* EquivTyExists *)
+ apply: EquivTyExists. apply IHE. 
Qed. 


