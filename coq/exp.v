(*---------------------------------------------------------------------------
   Multi-sorted index expressions and equational theories thereon.
   (Section 3.1 from POPL'13)
   ---------------------------------------------------------------------------*)
Require Import ssreflect ssrbool ssrfun seq.
Require Import Relations Program.Equality.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "c '<' x , .. , y '>'" (right associativity, at level 30, x, y at next level).
Reserved Notation "c '<>'" (at level 2). 

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

Fixpoint catEnv T (I: T -> Type) ts ts' : Env I ts -> Env I ts' -> Env I (ts ++ ts') :=
  if ts is _::_ 
  then fun env env' => (env.1, catEnv env.2 env') 
  else fun env env' => env'. 

Lemma lookupMapEnv T (I J:T -> Type) ts (f: forall t, I t -> J t) t 
  (v: Ix ts t) (env: Env I ts):
  lookup v (mapEnv f env) = f _ (lookup v env). 
Proof. dependent induction v => //. by rewrite /= IHv.  Qed. 

Lemma mapCompose T (I J K: T -> Type) ts (f: forall t, J t -> K t) (g: forall t, I t -> J t) 
  (env: Env I ts) : mapEnv f (mapEnv g env) = mapEnv (fun s x => f _ (g _ x)) env.
Proof. induction ts => //. by rewrite /= IHts. Qed. 

Section Ren.

Variable T: Type.
Variable I: T -> Type.

Definition IxRen ts ts' := Env (Ix (T:=T) ts') ts. 

Definition apRenVar ts ts' (R: IxRen ts ts') s v : Ix ts' s := lookup v R. 
Definition nilRen ts : IxRen [::] ts := tt.
Definition consRen ts ts' t v (R: IxRen ts ts') : IxRen (t::ts) ts' := (v,R). 

Lemma apRenZ ts ts' t (R: IxRen (t::ts) ts') : apRenVar R (ixZ _ _) = R.1.  
Proof. apply lookupZ. Qed. 

Lemma apRenS ts ts' t t' (R: IxRen (t::ts) ts') (v: Ix ts t') : apRenVar R (ixS _ v) = apRenVar R.2 v.  
Proof. apply lookupS. Qed. 

Definition shiftRen ts ts' t : IxRen ts ts' -> IxRen ts (t::ts') := mapEnv (fun s => ixS _). 

Lemma apRenShift ts ts' t' (R: IxRen ts ts') t (v: Ix ts t) : 
  apRenVar (shiftRen t' R) v = ixS _ (apRenVar R v). 
Proof. dependent induction v => //. by rewrite apRenS IHv. Qed. 

Definition liftRen ts ts' t (R: IxRen ts ts'): IxRen (t::ts) (t::ts') := 
  consRen (ixZ _ _) (shiftRen t R). 

Lemma apRenLift ts ts' t t' (R: IxRen ts ts') (v: Ix ts t) : 
  apRenVar (liftRen t' R) (ixS _ v) = ixS _ (apRenVar R v). 
Proof. by rewrite /liftRen/= apRenShift. Qed. 

Fixpoint idRen ts : IxRen ts ts := 
  if ts is t::ts' 
  then (liftRen t (idRen ts'))
  else tt.    

Lemma apRenId ts : forall t (v:Ix ts t), apRenVar (idRen _) v = v. 
Proof. dependent induction v => //. by rewrite apRenS apRenShift IHv. Qed. 

Lemma apRenExtensional ts ts' (R R': IxRen ts ts') : 
  (forall t (v: Ix ts t), apRenVar R v = apRenVar R' v) -> R = R'. 
Proof. apply envExtensional. Qed. 

Definition RcR ts ts' ts'' (R: IxRen ts' ts'') : IxRen ts ts' -> IxRen ts ts'' := mapEnv (apRenVar R).

Lemma shiftRenRcR ts : forall ts' ts'' s (R:IxRen ts' ts'') (R':IxRen ts ts'),
  shiftRen s (RcR R R') = RcR (shiftRen s R) R'. 
Proof. rewrite /shiftRen /RcR. induction ts => //. 
move => ts' ts'' t R R'. 
destruct R' as [v R']. by rewrite /= IHts apRenShift. 
Qed. 

Lemma apVarRcR ts ts' ts'' (r:IxRen ts' ts'') (r':IxRen ts ts') :
  (forall t (v:Ix ts t), apRenVar (RcR r r') v = apRenVar r (apRenVar r' v)).
Proof. dependent induction v => //. destruct r' as [v' r']. apply (IHv r'). Qed. 

End Ren.

Section ExpSyntax.

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
Definition Ren (D D': IxCtxt) := IxRen D D'.

Fixpoint apRen D D' s (r: Ren D D') (ix: Exp D s): Exp D' s :=
  match ix with
  | VarAsExp _ v => VarAsExp (apRenVar r v)
  | AppCon op ixs => AppCon op (apRenSeq r ixs)
  end
with apRenSeq D D' ss (r: Ren D D') (ixs: Exps D ss) : Exps D' ss  :=
  if ixs is Cons _ _ ix ixs 
  then Cons (apRen r ix) (apRenSeq r ixs) 
  else Nil.

Definition shExp D s s' : Exp D s -> Exp (s'::D) s := apRen (shiftRen s' (idRen D)). 
Definition shExpSeq D ss s' : Exps D ss -> Exps (s'::D) ss := apRenSeq (shiftRen s' (idRen D)). 

Lemma shAppCon D (s: Srt sig) op (es: Exps D _) : shExp s (AppCon op es) = 
  AppCon op (shExpSeq s es). 
Proof. done. Qed. 

Lemma shCons D (s: Srt sig) s' ss (e: Exp D s') (es: Exps D ss) : shExpSeq s (Cons e es) = Cons (shExp s e) (shExpSeq s es). 
Proof. done. Qed. 

Lemma apRcRAndSeq E E' E'' (r:Ren E' E'') (r':Ren E E') :
  (forall s (e:Exp E s), apRen (RcR r r') e = apRen r (apRen r' e)) /\
  (forall ss (es:Exps E ss), apRenSeq (RcR r r') es = apRenSeq r (apRenSeq r' es)). 
Proof. apply Exp_Exps_ind; Rewrites apVarRcR. Qed.

Corollary apRcR E E' E'' (r:Ren E' E'') (r':Ren E E') s (e:Exp E s):
  apRen (RcR r r') e = apRen r (apRen r' e).
Proof. apply apRcRAndSeq. Qed. 


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
+ move => s v. by rewrite /= -apSubVarLift apRenShift apRenId. 
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
by rewrite /shExp/= apRenShift apRenId. 
Qed. 

Lemma apSubIdAndSeq D :
  (forall s (e : Exp D s), apSub (idSub _) e = e) /\ 
  (forall ss (es: Exps D ss), apSubSeq (idSub _) es = es). 
Proof. apply Exp_Exps_ind; Rewrites liftSubId. apply apSubVarId. Qed.

Corollary apSubId D s (e : Exp D s) : apSub (idSub _) e = e.
Proof. apply apSubIdAndSeq. Qed.

Lemma apSubExtensional E E' (S S': Sub E E') : 
  (forall s (v: Var E s), apSubVar S v = apSubVar S' v) -> S = S'. 
Proof. apply envExtensional. Qed. 

Lemma apVarScR E E' E'' (S:Sub E' E'') (R:Ren E E') : 
  (forall s (v:Var E s), apSubVar (ScR S R) v = apSubVar S (apRenVar R v)).
Proof. dependent induction v => //. destruct R as [v' R]. simpl. apply IHv.  Qed. 

Lemma apScRAndSeq E E' E'' (S:Sub E' E'') (R:Ren E E') : 
  (forall s (e:Exp E s), apSub (ScR S R) e = apSub S (apRen R e)) /\
  (forall ss (es:Exps E ss), apSubSeq (ScR S R) es = apSubSeq S (apRenSeq R es)).
Proof. apply Exp_Exps_ind; Rewrites apVarScR. Qed.

Corollary apScR  E E' E'' (S:Sub E' E'') (R:Ren E E') s (e:Exp E s) :
  apSub (ScR S R) e = apSub S (apRen R e). 
Proof. apply apScRAndSeq. Qed. 

Lemma apVarRcS E E' E'' (R:Ren E' E'') (S:Sub E E') : 
  (forall s (v:Var E s), apSubVar (RcS R S) v = apRen R (apSubVar S v)).
Proof. dependent induction v => ///=. destruct S as [e S]. apply IHv. Qed. 

Lemma apRcSAndSeq E E' E'' (R:Ren E' E'') (S:Sub E E') : 
  (forall s (e:Exp E s), apSub (RcS R S) e = apRen R (apSub S e)) /\
  (forall ss (es:Exps E ss), apSubSeq (RcS R S) es = apRenSeq R (apSubSeq S es)).
Proof. apply Exp_Exps_ind; Rewrites apVarRcS. Qed.

Corollary apRcS  E E' E'' (R:Ren E' E'') (S:Sub E E') s (e:Exp E s) :
  apSub (RcS R S) e = apRen R (apSub S e).
Proof. apply apRcSAndSeq. Qed.

Lemma apVarScS E E' E'' (S:Sub E' E'') (S':Sub E E') : 
  (forall s (v:Var E s), apSubVar (ScS S S') v = apSub S (apSubVar S' v)).
Proof. dependent induction v => //. destruct S' as [e S']. simpl. apply IHv. Qed. 

Lemma apScSAndSeq E E' E'' (S:Sub E' E'') (S':Sub E E') : 
  (forall s (e:Exp E s), apSub (ScS S S') e = apSub S (apSub S' e)) /\
  (forall ss (es:Exps E ss), apSubSeq (ScS S S') es = apSubSeq S (apSubSeq S' es)).
Proof. apply Exp_Exps_ind; Rewrites apVarScS. Qed.

Corollary apScS E E' E'' (S:Sub E' E'') (S':Sub E E') s (e:Exp E s) :
  apSub (ScS S S') e = apSub S (apSub S' e).
Proof. apply apScSAndSeq. Qed.

Lemma ScS_assoc E E' E'' E''' (S1: Sub E'' E''') (S2: Sub E' E'') (S3: Sub E E') :
  ScS S1 (ScS S2 S3) = ScS (ScS S1 S2) S3.
Proof. apply apSubExtensional => s v. rewrite !apVarScS. by rewrite apScS. Qed. 

Lemma idScS E E' (S: Sub E' E) : ScS (idSub E) S = S.
Proof. apply apSubExtensional => s v. rewrite apVarScS. by rewrite apSubId. Qed.

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
by rewrite apVarScS/pi apSubVarShift apSubVarId /= apRenShift apSubVarS/= apRenId. 
Qed. 

Lemma liftPi D D' s (S: Sub D D') : ScS (liftSub s S) (pi D s) = ScS (pi D' s) S.
Proof. rewrite /liftSub consPi. rewrite /pi. apply apSubExtensional => s' v. 
rewrite apSubVarShift. rewrite apVarScS. rewrite /shExp. by rewrite apSubPi. 
Qed. 


(*---------------------------------------------------------------------------
   Now we introduce equational theories for indices, induced by a set of
   axioms. 
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


End ExpSyntax.

Implicit Arguments AppCon [sig D].

(* Some handy notation for applying expression constructors *)
Notation "c '<' x , .. , y '>'" := (AppCon c (Cons x .. (Cons y (Nil _)) .. )) : Exp_scope.
Notation "c '<>'" := (AppCon c (Nil _)) : Exp_scope.

(* Singleton substitution *)
Notation "<< e >>" := (consSub e (idSub _)). 

Lemma apSubSingleShift sig D (s:Srt sig) (e: Exp D s) 
: (forall s' (e': Exp D s'), apSub <<e>> (shExp s e') = e') /\
  (forall ss (es: Exps D ss), apSubSeq <<e>> (shExpSeq s es) = es). 
Proof. 
apply Exp_Exps_ind => //. 
+ move => s' v. rewrite /shExp /apRen apRenShift.
rewrite /apSub.  simpl. rewrite apSubVarId. by rewrite apRenId.  
+ move => op es IH. by rewrite shAppCon apSubAppCon IH. 
+ move => s' ss e' IH es IH'. by rewrite shCons apSubSeqCons IH IH'. 
Qed. 


Lemma apScSingleVar sig E (s:Srt sig) e s' (v: Var  _ s') E' (S: Sub E E'):
  apSub S (apSubVar (consSub e (idSub _)) v) = apSub (consSub (apSub S e) (idSub _)) (apSubVar (liftSub s S) v). 
Proof. 
dependent destruction v => //. 
simpl. rewrite apSubVarId apSubVarShift. by rewrite (proj1 (apSubSingleShift _)).
Qed. 

Lemma ScSingle sig E E' (s: Srt sig) (S:Sub E E') e :
  ScS S (consSub e (idSub _)) = ScS (consSub (apSub S e) (idSub _)) (liftSub s S). 
Proof. apply apSubExtensional => s' v.
rewrite 2!apVarScS. by rewrite apScSingleVar. Qed. 

Bind Scope Exp_scope with Exp. 
Delimit Scope Exp_scope with Exp. 

Notation "#0" := (VarAsExp (ixZ _ _)). (*: Ty_scope.*)
Notation "#1" := (VarAsExp (ixS _ (ixZ _ _))). (* : Ty_scope. *)
Notation "#2" := (VarAsExp (ixS _ (ixS _ (ixZ _ _)))). (*  : Ty_scope. *)

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
  rewrite -2!apScS.  by apply EquivByAxZ.       
(* EquivByAxS *)
+ move => s A As e e' E1 E2. by apply EquivByAxS. 
(* EquivNil *)
+ move => A. by apply: EquivNil.
(* EquivCons *)
+ move => A s ss e1 e2 es1 es2 E1 E2 E3 E4. rewrite 2!apSubSeqCons. by apply: EquivCons. 
Qed. 


