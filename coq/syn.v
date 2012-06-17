Require Import ssreflect ssrbool ssrfun seq.
Require Import Relations Program.Equality.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*---------------------------- SYNTAX ------------------------------------------------------*)
Section Syntax.

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

Variable sig: SIG.

(* Index variables each have a sort *)
Definition IxCtxt := seq (Srt sig). 

(* Index variables, in context *)
Inductive IxVar : IxCtxt -> Srt sig -> Type :=
| IxZ D s : IxVar (s::D) s
| IxS D s' s : IxVar D s' -> IxVar (s::D) s'.

(* Well-sorted index expressions, in context. D is \Delta in paper *)
Inductive IxExp (D: IxCtxt) : Srt sig -> Type :=
| VarIx s : IxVar D s -> IxExp D s
| ConIx op : IxExpSeq D (opArity op).1 -> IxExp D (opArity op).2

(* Well-sorted sequences of index expressions, in context *)
with IxExpSeq (D: IxCtxt) : IxCtxt -> Type :=
| NilIx : IxExpSeq D nil
| ConsIx s ss : IxExp D s -> IxExpSeq D ss -> IxExpSeq D (s::ss).

Implicit Arguments ConIx [D].

(* Renamings and substitutions. *)
Structure Ren D D' := mkRen {
  getRen:> forall s, IxVar D s -> IxVar D' s
}. 

Structure Sub D D' := mkSub {
  getSub :> forall s, IxVar D s -> IxExp D' s
}.

Definition seqAsSub D D' (ixs: IxExpSeq D D') : Sub D' D.
refine (mkSub _) => s. 
induction ixs => v.
inversion v.  
dependent destruction v.
+ exact i. 
+ exact (IHixs v). 
Defined.

Coercion seqAsSub : IxExpSeq >-> Sub.

Program Definition liftRen D D' s (R: Ren D D') : Ren (s::D) (s::D') := 
  mkRen (fun s' v =>
  match v with
  | IxZ _ _ => IxZ _ _
  | IxS _ _ _ v' => IxS _ (R _ v')
  end).

Fixpoint apRen D D' s (r: Ren D D') (ix: IxExp D s): IxExp D' s :=
  match ix with
  | VarIx _ v => VarIx (r _ v)
  | ConIx op ixs => ConIx op (apRenSeq r ixs)
  end
with apRenSeq D D' ss (r: Ren D D') (ixs: IxExpSeq D ss) : IxExpSeq D' ss  :=
  if ixs is ConsIx _ _ ix ixs 
  then ConsIx (apRen r ix) (apRenSeq r ixs) 
  else NilIx _.

Definition shIxExp D s s' : IxExp D s -> IxExp (s'::D) s := apRen (mkRen (fun _ v => IxS _ v)).

Definition idSub D : Sub D D := mkSub (@VarIx _).

Program Definition consSub D D' s (ix: IxExp D' s) (S: Sub D D') : Sub (s::D) D' :=
  mkSub (fun s' (v: IxVar (s::D) s') =>
    match v with IxZ _ _ => ix
               | IxS _ _ _ v' => S _ v'
    end).

Definition tlSub D D' s (S: Sub (s::D) D') : Sub D D' := mkSub (fun s' v => S s' (IxS s v)).
Definition hdSub D D' s (S: Sub (s::D) D') : IxExp D' s := S s (IxZ _ _). 


Fixpoint apSub D D' s (S: Sub D D') (ix: IxExp D s): IxExp D' s :=
  match ix with
  | VarIx _ v => S _ v
  | ConIx op ixs => ConIx op (apSubSeq S ixs)
  end
with apSubSeq D D' ss (S: Sub D D') (ixs: IxExpSeq D ss) : IxExpSeq D' ss  :=
  if ixs is ConsIx _ _ ix ixs 
  then ConsIx (apSub S ix) (apSubSeq S ixs) 
  else NilIx _.

(* This is the lifting operation \sigma_{i:s} of the paper *)
Program Definition liftSub D D' s (S: Sub D D') : Sub (s::D) (s::D') :=
  mkSub (fun s' v =>
  match v with
  | IxZ _ _ => VarIx (IxZ _ _)
  | IxS _ _ _ v' => shIxExp s (S _ v')
  end).

Definition RcR D D' D'' (R: Ren D' D'') (R': Ren D D') : Ren D D'' := 
  mkRen (fun s v => R s (R' s v)).

Definition ScR D D' D'' (S: Sub D' D'') (R: Ren D D') : Sub D D'' :=
  mkSub (fun s v => S s (R s v)).

Definition RcS D D' D'' (R: Ren D' D'') (S: Sub D D') : Sub D D'' :=
  mkSub (fun s v => apRen R (S s v)).

Definition ScS D D' D'' (S: Sub D' D'') (S': Sub D D') : Sub D D'' :=
  mkSub (fun s v => apSub S (S' s v)).


(* Well-sorted type expressions, in context *)
Inductive Ty (D: IxCtxt) :=
| TyUnit
| TyProd (t1 t2: Ty D) 
| TySum (t1 t2: Ty D)
| TyArr (t1 t2: Ty D)
| TyPrim (p: PrimType sig) (ixs: IxExpSeq D (tyArity p))
| TyAll s (t: Ty (s::D))
| TyExists s (t: Ty (s::D)).

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

Definition shiftSub D D' s (S: Sub D D') : Sub D (s::D') := 
  mkSub (fun s v => apRen (mkRen (fun s => IxS _)) (S s v)). 

(* This is the operation \pi_{i:s} of the paper *)
Definition pi D s : Sub D (s::D) := shiftSub s (idSub D). 

(* Well-sorrted axiom, in context *)
Inductive Ax := mkAx D s (lhs: IxExp D s) (rhs: IxExp D s).

(* Equational theory induced by axioms *)
Inductive equiv D : forall s, seq Ax -> relation (IxExp D s) :=
| EquivRefl s axs (e: IxExp D s) : 
  equiv axs e e

| EquivSym s axs (e1 e2: IxExp D s) : 
  equiv axs e1 e2 -> equiv axs e2 e1

| EquivTrans s axs (e1 e2 e3: IxExp D s) : 
  equiv axs e1 e2 -> equiv axs e2 e3 -> equiv axs e1 e3

| EquivComp axs p (es es': IxExpSeq D _) : 
  equivSeq axs es es' -> equiv axs (ConIx p es) (ConIx p es')

| EquivByAxZ s axs D' sigma (e e':IxExp D' s) : 
  equiv (mkAx e e' :: axs) (apSub sigma e) (apSub sigma e')

| EquivByAxS s ax axs (e e':IxExp D s) : 
  equiv axs e e' ->
  equiv (ax :: axs) e e'

with equivSeq D : forall ss, seq Ax -> relation (IxExpSeq D ss) :=
| EquivNil axs : 
  equivSeq axs (NilIx _) (NilIx _)

| EquivCons axs s ss (e e': IxExp D s) (es es': IxExpSeq D ss) : 
  equiv axs e e' -> equivSeq axs es es' -> equivSeq axs (ConsIx e es) (ConsIx e' es').

End Syntax.

Implicit Arguments ConIx [sig D].
Implicit Arguments TyPrim [sig D].

