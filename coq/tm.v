(*---------------------------------------------------------------------------
   The syntax of terms
   (Section 3.2 from POPL'13)
   ---------------------------------------------------------------------------*)
Require Import ssreflect ssrbool ssrfun seq.
Require Import Relations Program.Equality Casts exp ty.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section TmSyntax.

Variable sig: SIG. 

(* Typing contexts: just a sequences of types *)
Definition Ctxt D := seq (Ty (sig:=sig) D). 

Fixpoint apSubCtxt D D' (S: Sub D D') (G: Ctxt D) : Ctxt D' :=
  if G is t::G then apSubTy S t :: apSubCtxt S G else nil.

Lemma apCtxtScS E (G: Ctxt E) : forall E' E'' (S: Sub E' E'') (S': Sub E E'),
  apSubCtxt (ScS S S') G = apSubCtxt S (apSubCtxt S' G). 
Proof. induction G => //. move => E' E'' S S'. by rewrite /= apTyScS IHG. Qed. 

Lemma apSubCtxtId D (G : Ctxt D) : apSubCtxt (idSub D) G = G.
Proof.
  induction G => /=//.
  by rewrite IHG apSubTyId.
Qed.

Lemma apSubCtxtScS D D' D'' (S : Sub D' D'') (S' : Sub D D') (G : Ctxt D) :
  apSubCtxt S (apSubCtxt S' G) = apSubCtxt (ScS S S') G.
Proof.
  induction G => /=//. 
  by rewrite IHG apSubTyScS.
Qed.


(* Finally, we define terms *)
Variable A: seq (Ax sig). 

Definition TmVar D := Ix (T:= Ty (sig:=sig) D).

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

End TmSyntax.


Fixpoint apSubTyTmVar sig D D' (S: Sub (sig:=sig) D D') (G: Ctxt D) t  (v: TmVar G t)
  : TmVar (apSubCtxt S G) (apSubTy S t)
  :=
  match v with
  | ixZ _ _ => ixZ _ _
  | ixS _ _ _ v => ixS _ (apSubTyTmVar S v)
  end.

Lemma funny {sig A D D'} (S: Sub (sig:=sig) D D') (G: Ctxt D) s (t: Ty _) e :
  Tm A (apSubCtxt S G) (apSubTy (consSub (apSub S e) (idSub _)) (apSubTy (liftSub s S) t)) =
  Tm A (apSubCtxt S G) (apSubTy S (apSubTy (consSub e (idSub _)) t)).
Proof. apply f_equal. 
rewrite -!apTyScS. 
by rewrite ScSingle. 
Qed. 

Lemma funny2 {sig A D D'} (S: Sub (sig:=sig) D D') (G: Ctxt D) s (t: Ty _) :
Tm A (apSubCtxt (liftSub s S) (apSubCtxt (pi D s) G)) (apSubTy (liftSub s S) t) = 
Tm A (apSubCtxt (pi D' s) (apSubCtxt S G)) (apSubTy (liftSub s S) t).
Proof. by rewrite -!apCtxtScS liftPi. Qed. 

Lemma funny3 {sig A D D'} (S: Sub (sig:=sig) D D') (G: Ctxt D) s (t: Ty _) (t': Ty _) :
Tm A (apSubCtxt (liftSub s S) (t :: apSubCtxt (pi D s) G))
     (apSubTy (liftSub s S) (apSubTy (pi _ s) t')) =
Tm A (apSubTy (liftSub s S) t :: apSubCtxt (pi _ s) (apSubCtxt S G))
     (apSubTy (pi _ s) (apSubTy S t')).
Proof. rewrite -apTyScS liftPi apTyScS. simpl.  
by rewrite -apCtxtScS liftPi apCtxtScS.    
Qed. 

Fixpoint apSubTyTm {sig A D D'} (S: Sub (sig:=sig) D D') (G: Ctxt D) (t: Ty D) (M: Tm A G t)
  :=
  match M in Tm _ _ t return Tm A (apSubCtxt S G) (apSubTy S t) with
  | VAR _ v => VAR _ (apSubTyTmVar S v)
  | TYEQ t1 t2 eq M => TYEQ (equivTySubst eq S) (apSubTyTm S M)
  | UNIT => UNIT _ _
  | PAIR t1 t2 M1 M2 => PAIR (apSubTyTm S M1) (apSubTyTm S M2)
  | PROJ1 t1 t2 M => PROJ1 (apSubTyTm S M)
  | PROJ2 t1 t2 M => PROJ2 (apSubTyTm S M)
  | INL t1 t2 M => INL _ (apSubTyTm S M)
  | INR t1 t2 M => INR _ (apSubTyTm S M)
  | CASE t1 t2 t M M1 M2 => CASE (apSubTyTm S M) (apSubTyTm S M1) (apSubTyTm S M2)
  | ABS t1 t2 M => ABS (apSubTyTm S M)
  | APP t1 t2 M1 M2 => APP (apSubTyTm S M1) (apSubTyTm S M2)
  | UNIVAPP s t e M => (UNIVAPP (apSub S e) (apSubTyTm S M)) :? (funny S G t e)
  | EXPACK s e t M => EXPACK (apSubTyTm S M :? (sym_equal (funny S G t e)))
  | UNIVABS s t M => UNIVABS (apSubTyTm (liftSub s S) M :? funny2 _ _ _)
  | EXUNPACK s t t' M1 M2 => EXUNPACK (apSubTyTm S M1) (apSubTyTm (liftSub s S) M2 :? funny3 _ _ _ _)
  end.

Notation "##0" := (VAR _ (ixZ _ _)).
Notation "##1" := (VAR _ (ixS _ (ixZ _ _))).
Notation "##2" := (VAR _ (ixS _ (ixS _ (ixZ _ _)))).
Notation "##3" := (VAR _ (ixS _ (ixS _ (ixS _ (ixZ _ _))))).
Notation "##4" := (VAR _ (ixS _ (ixS _ (ixS _ (ixS _ (ixZ _ _)))))).
Notation "##5" := (VAR _ (ixS _ (ixS _ (ixS _ (ixS _ (ixS _ (ixZ _ _))))))).
Notation "##6" := (VAR _ (ixS _ (ixS _ (ixS _ (ixS _ (ixS _ (ixS _ (ixZ _ _)))))))).


Definition TmRen sig (D:IxCtxt sig) (G G': Ctxt (sig:=sig) D) := IxRen G G'.  

Fixpoint apSubTmRen sig D D' G G' (S: Sub D D') : 
  TmRen (sig:=sig) G G' -> TmRen (apSubCtxt S G) (apSubCtxt S G') :=
  if G is t::G''
  then fun R => (apSubTyTmVar S R.1, apSubTmRen S R.2) 
  else fun R => tt.

Fixpoint apTmRenTm sig A D G G' (t: Ty (sig:=sig) D) (R: TmRen G G') (M: Tm A G t) : Tm A G' t
  :=
  match M with
  | VAR _ v => VAR _ (apRenVar R v)
  | TYEQ t1 t2 eq M => TYEQ eq (apTmRenTm R M)
  | UNIT => UNIT _ _
  | PAIR t1 t2 M1 M2 => PAIR (apTmRenTm R M1) (apTmRenTm R M2)
  | PROJ1 t1 t2 M => PROJ1 (apTmRenTm R M)
  | PROJ2 t1 t2 M => PROJ2 (apTmRenTm R M)
  | INL t1 t2 M => INL _ (apTmRenTm R M)
  | INR t1 t2 M => INR _ (apTmRenTm R M)
  | APP t1 t2 M1 M2 => APP (apTmRenTm R M1) (apTmRenTm R M2)
  | CASE t1 t2 t M M1 M2 => 
    CASE (apTmRenTm R M) (apTmRenTm (liftRen t1 R) M1) (apTmRenTm (liftRen t2 R) M2)
  | ABS t1 t2 M => ABS (apTmRenTm (liftRen t1 R) M)
  | UNIVAPP s t e M => UNIVAPP e (apTmRenTm R M)
  | EXPACK s e t M => EXPACK (apTmRenTm R M)
  | EXUNPACK s t t' M1 M2 => 
    EXUNPACK (apTmRenTm R M1) (apTmRenTm (liftRen t (apSubTmRen (pi D s) R)) M2)
  | UNIVABS s t M => UNIVABS (apTmRenTm (apSubTmRen (pi D s) R) M)
  end.

Definition shTmTm sig A D (G: Ctxt (sig:=sig) D) t t' : Tm A G t -> Tm A (t'::G) t := 
  apTmRenTm (shiftRen t' (idRen G)). 

Fixpoint shTmBy sig A D (G: Ctxt (sig:=sig) D) t G' : Tm A G t -> Tm A (G'++G) t :=
  if G' is t'::G' 
  then fun M => shTmTm t' (shTmBy G' M)
  else fun M => M.
  

