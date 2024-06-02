(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Extension of real functions
  author    : ZhengPu Shi
  date      : 2023.03
  
  reference :
  1. Lecture from Prof. Chen (my supervisor)

  remark    :

 *)

Require Export RExt.
Require Export FuncExt.
Open Scope Rfun_scope.
Open Scope R_scope.


(* ######################################################################### *)
(** * Basic real functions *)


(* ======================================================================= *)
(** ** Real arithmetic functions *)

(* Coq.Reals.Ranalysis1.plus_fct
   Rfun_scope, Delimiting key is F
   "x / y" := (div_fct x y)
   "x - y" := (minus_fct x y)
   "x + y" := (plus_fct x y)
   "x * y" := (mult_fct x y)
   "/ x" := (inv_fct x)
   "- x" := (opp_fct x) *)

Notation faddR := plus_fct.
Notation foppR := opp_fct.
(* Notation fsubR := minus_fct. *)
Notation fsubR f g := (faddR f (foppR g)).
Notation fmulR := mult_fct.
Notation finvR := inv_fct.
(* Notation fdivR := div_fct. *)
Notation fdivR f g := (fmulR f (finvR g)).

Infix "+f" := faddR : Rfun_scope.
Infix "-f" := fsubR : Rfun_scope.
Infix "*f" := fmulR : Rfun_scope.
Infix "/f" := fdivR : Rfun_scope.
Infix "/f" := fdivR : Rfun_scope.
Notation "-f g" := (foppR g) : Rfun_scope.
Notation "/f g" := (finvR g) : Rfun_scope.

Lemma faddR_ok : forall (u v : R -> R) (x : R), (u +f v) x = (u x + v x)%R. auto. Qed.
Lemma foppR_ok : forall (v : R -> R) (x : R), (-f v) x = (- v x)%R. auto. Qed.
Lemma fsubR_ok : forall (u v : R -> R) (x : R), (u -f v) x = (u x - v x)%R. auto. Qed.
Lemma fmulR_ok : forall (u v : R -> R) (x : R), (u *f v) x = (u x * v x)%R. auto. Qed.
Lemma finvR_ok : forall (v : R -> R) (x : R), (/f v) x = (/ v x)%R. auto. Qed.
Lemma fdivR_ok : forall (u v : R -> R) (x : R), (u /f v) x = (u x / v x)%R. auto. Qed.

(* ======================================================================= *)
(** ** Real constant functions *)
Definition fcnstR (C : R) : R -> R := fun _ => C.
Definition fzeroR : R -> R := fcnstR R0.
Definition foneR : R -> R := fcnstR R1.
Definition fidR : R -> R := fun x => x.
(* Notation "0" := fzeroR : Rfun_scope. *)
(* Notation "1" := foneR : Rfun_scope. *)

Hint Unfold
  faddR foppR fmulR finvR
  fcnstR fzeroR foneR fidR : Rfun.

Lemma faddR_0_l : forall f, fzeroR +f f = f.
Proof. intros. apply feq_iff; intros; autounfold with Rfun; ring. Qed.

Lemma faddR_0_r : forall f, f +f fzeroR = f.
Proof. intros. apply feq_iff; intros; autounfold with Rfun; ring. Qed.

Lemma faddR_opp_l : forall f, - f +f f = fzeroR.
Proof. intros. apply feq_iff; intros; autounfold with Rfun; ring. Qed.

Lemma faddR_opp_r : forall f, f +f -f f = fzeroR.
Proof. intros. apply feq_iff; intros; autounfold with Rfun; ring. Qed.

Lemma fmulR_1_l : forall f, foneR *f f = f.
Proof. intros. apply feq_iff; intros; autounfold with Rfun; ring. Qed.

Lemma fmulR_1_r : forall f, f *f foneR = f.
Proof. intros. apply feq_iff; intros; autounfold with Rfun; ring. Qed.

Lemma fmulR_inv_l : forall f, (forall x, f x <> 0)%R -> /f f *f f = foneR.
Proof. intros. apply feq_iff; intros. autounfold with Rfun. field. auto. Qed.

Lemma fmulR_inv_r : forall f, (forall x, f x <> 0)%R -> f *f /f f = foneR.
Proof. intros. apply feq_iff; intros. autounfold with Rfun. field. auto. Qed.


(* ======================================================================= *)
(** ** Scalar multiplication of real function *)

Definition fcmulR (c : R) (f : R -> R) := fun x => (c * f x)%R.
Infix "c*" := fcmulR : Rfun_scope.

Lemma fcmulR_ok : forall (c : R) (u : R -> R) (x : R), (c c* u) x = (c * u x)%R.
Proof. auto. Qed.

(** Properties for real function scalar multiplication *)
Lemma fcmulR_assoc1 : forall (c d : R) (u : R -> R), c c* (d c* u) = (c * d) c* u.
Proof. intros. apply feq_iff; intros. rewrite !fcmulR_ok. ring. Qed.

Lemma fcmulR_assoc2 : forall (c : R) (u v : R -> R), c c* (u *f v) = (c c* u) *f v.
Proof.
  intros. apply feq_iff; intros. rewrite ?fmulR_ok, ?fcmulR_ok, ?fmulR_ok. ring.
Qed.

(** Multiply with a natural number, i.e., sum the function by n times:
    fnmul f 0 := fun x => 0
    fnmul f 1 := f
    fnmul f 2 := f + f, i.e., fun x => f x + f x
    ...
    fnmul f (S n) := fun x => f x + (fnmul f n) *)
Fixpoint fnmulR (n : nat) (f : R -> R) : R -> R :=
  match n with
  | O => fun x => 0%R
  | S O => f
  | S n' => faddR f (fnmulR n' f)
  end.


(* ######################################################################### *)
(** * Algebraic structures *)

(** equality is equivalence relation: Equivalence (@eq (R -> R)) *)
Hint Resolve eq_equivalence : Rfun.

(** operations are well-defined. Eg: Proper (eq ==> eq ==> eq) faddR *)

Lemma faddR_wd : Proper (eq ==> eq ==> eq) faddR.
Proof. simp_proper. intros; subst; auto. Qed.

Lemma foppR_wd : Proper (eq ==> eq) foppR.
Proof. simp_proper. intros; subst; auto. Qed.

Lemma fmulR_wd : Proper (eq ==> eq ==> eq) fmulR.
Proof. simp_proper. intros; subst; auto. Qed.

Lemma finvR_wd : Proper (eq ==> eq) finvR.
Proof. simp_proper. intros; subst; auto. Qed.

Hint Resolve
  faddR_wd foppR_wd
  fmulR_wd finvR_wd
  : Rfun.

(** Associative *)

#[export] Instance faddR_Assoc : Associative faddR.
Proof. constructor; intros. autounfold with Rfun; apply feq_iff; intros; ring. Qed.

#[export] Instance fmulR_Assoc : Associative fmulR.
Proof. constructor; intros. autounfold with Rfun; apply feq_iff; intros; ring. Qed.

Hint Resolve
  faddR_Assoc
  fmulR_Assoc
  : Rfun.

(** Commutative *)

#[export] Instance faddR_Comm : Commutative faddR.
Proof. constructor; intros. autounfold with Rfun; apply feq_iff; intros; ring. Qed.

#[export] Instance fmulR_Comm : Commutative fmulR.
Proof. constructor; intros. autounfold with Rfun; apply feq_iff; intros; ring. Qed.

Hint Resolve
  faddR_Comm
  fmulR_Comm
  : Rfun.

(** Identity Left/Right *)
#[export] Instance faddR_IdL : IdentityLeft faddR fzeroR.
Proof. constructor; intros. autounfold with Rfun; apply feq_iff; intros; ring. Qed.

#[export] Instance faddR_IdR : IdentityRight faddR fzeroR.
Proof. constructor; intros. autounfold with Rfun; apply feq_iff; intros; ring. Qed.

#[export] Instance fmulR_IdL : IdentityLeft fmulR foneR.
Proof. constructor; intros. autounfold with Rfun; apply feq_iff; intros; ring. Qed.

#[export] Instance fmulR_IdR : IdentityRight fmulR foneR.
Proof. constructor; intros. autounfold with Rfun; apply feq_iff; intros; ring. Qed.

Hint Resolve
  faddR_IdL faddR_IdR
  fmulR_IdL fmulR_IdR
  : Rfun.

(** Inverse Left/Right *)

#[export] Instance faddR_InvL : InverseLeft faddR fzeroR foppR.
Proof. constructor; intros. autounfold with Rfun; apply feq_iff; intros; ring. Qed.

#[export] Instance faddR_InvR : InverseRight faddR fzeroR foppR.
Proof. constructor; intros. autounfold with Rfun; apply feq_iff; intros; ring. Qed.

Hint Resolve faddR_InvL faddR_InvR : Rfun.

(** Distributive *)

#[export] Instance fmulR_add_DistrL : DistrLeft faddR fmulR.
Proof. constructor; intros. autounfold with Rfun; apply feq_iff; intros; ring. Qed.

#[export] Instance fmulR_add_DistrR : DistrRight faddR fmulR.
Proof. constructor; intros. autounfold with Rfun; apply feq_iff; intros; ring. Qed.

Hint Resolve
  fmulR_add_DistrL
  fmulR_add_DistrR
  : Rfun.

(** Semigroup *)

#[export] Instance faddR_SGroup : SGroup faddR.
Proof. constructor; auto with Rfun. Qed.

#[export] Instance fmulR_SGroup : SGroup fmulR.
Proof. constructor; auto with Rfun. Qed.

Hint Resolve
  faddR_SGroup
  fmulR_SGroup
  : Rfun.

(** Abelian semigroup *)

#[export] Instance faddR_ASGroup : ASGroup faddR.
Proof. constructor; auto with Rfun. Qed.

#[export] Instance fmulR_ASGroup : ASGroup fmulR.
Proof. constructor; auto with Rfun. Qed.

Hint Resolve
  faddR_ASGroup
  fmulR_ASGroup
  : Rfun.

Goal forall x1 x2 y1 y2 a b c, x1 + a + b + c + x2 = y1 + c + (b + a) + y2.
Proof. intros. pose proof faddR_ASGroup. asgroup. Abort.

(** Monoid *)
  
#[export] Instance faddR_Monoid : Monoid faddR fzeroR.
Proof. constructor; auto with Rfun. Qed.

#[export] Instance fmulR_Monoid : Monoid fmulR foneR.
Proof. constructor; auto with Rfun. Qed.

Hint Resolve
  faddR_Monoid
  fmulR_Monoid
  : Rfun.

(** Abelian monoid *)
  
#[export] Instance faddR_AMonoid : AMonoid faddR fzeroR.
Proof. constructor; auto with Rfun. Qed.
  
#[export] Instance fmulR_AMonoid : AMonoid fmulR foneR.
Proof. constructor; auto with Rfun. Qed.

Hint Resolve faddR_AMonoid fmulR_AMonoid : Rfun.

(** Group *)

#[export] Instance faddR_Group : Group faddR fzeroR foppR.
Proof. constructor; auto with Rfun. Qed.

Hint Resolve faddR_Group : Rfun.

(** AGroup *)

#[export] Instance faddR_AGroup : AGroup faddR fzeroR foppR.
Proof. constructor; auto with Rfun. Qed.

Hint Resolve faddR_AGroup : Rfun.

(** Ring *)

#[export] Instance Rfun_Ring : Ring faddR fzeroR foppR fmulR foneR.
Proof. constructor; auto with Rfun. Qed.

Hint Resolve Rfun_Ring : Rfun.

(** ARing *)

#[export] Instance Rfun_ARing : ARing faddR fzeroR foppR fmulR foneR.
Proof. constructor; auto with Rfun. Qed.

Hint Resolve Rfun_ARing : Rfun.

Section test.
  Add Ring ring_inst : (make_ring_theory Rfun_ARing).

  Goal forall u v w : R -> R, u -f v *f (u -f w) = w *f v -f u *f v +f u.
  Proof. intros. ring. Qed.
End test.

(** Field *)

#[export] Instance Rfun_Field : Field faddR fzeroR foppR fmulR foneR finvR.
Proof.
  constructor; auto with Rfun.
  2:{ intro. cbv in H.
      rewrite fun_eq_iff_forall_eq in H. specialize (H R0). lra. }
  1:{ intros. apply fmulR_inv_l.
      cbv in H.
      (* tips, THIS IS NOT PROVABLE. WE KNOW "exist", BUT NEED "forall"
         f : R -> R,
         f <> (fun _ : R => R0)
         ---------------------------
         forall x : R, f x <> R0
       *)
Abort.


(* ######################################################################### *)
(** * Instances for ElementType *)
   
Module ElementTypeRFun <: ElementType.
  Add Ring ring_inst : (make_ring_theory Rfun_ARing).
  
  Definition A : Type := R -> R.
  Definition Azero : A := fzeroR.
  Hint Unfold A Azero : A.

  Lemma AeqDec : Dec (@eq A).
  Proof. constructor. intros a b.
         (* rewrite (functional_extensionality a b). *)
  Admitted.
End ElementTypeRFun.

Module MonoidElementTypeRFun <: MonoidElementType.
  Include ElementTypeRFun.
  
  Definition Aadd := faddR.
  Hint Unfold Aadd : A.
  
  Infix "+" := Aadd : A_scope.

  #[export] Instance Aadd_AMonoid : AMonoid Aadd Azero.
  Proof. intros. repeat constructor; intros; autounfold with A; ring. Qed.
End MonoidElementTypeRFun.

Module RingElementTypeRFun <: RingElementType.
  Include MonoidElementTypeRFun.
  
  Definition Aone : A := foneR.
  Definition Aopp := foppR.
  Definition Amul := fmulR.
  Hint Unfold Aone Aadd Aopp Amul : A.
  
  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := Asub : A_scope.
  
  #[export] Instance ARing : ARing Aadd Azero Aopp Amul Aone.
  Proof.
    repeat constructor; intros;  autounfold with A;
      apply functional_extensionality; intros; cbv; ring.
  Qed.
  
  Add Ring Ring_inst : (make_ring_theory ARing).
End RingElementTypeRFun.
