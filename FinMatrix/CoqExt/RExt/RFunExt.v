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
  1. we won't use notations such as {+,-,*,/} in Reals at scope Rfun_scope (%F),
     instead, we use {+f, -f, *f, /f, c*} in scope RFun_scope (%R).
 *)

Require Export RExt.
Require Export FuncExt.

Declare Scope RFun_scope.
Delimit Scope RFun_scope with F.
Open Scope RFun_scope.


(* ######################################################################### *)
(** * Basic real functions *)

(* ======================================================================= *)
(** ** Real arithmetic functions *)

Notation fadd := plus_fct.
Notation fopp := opp_fct.
(* Notation fsub := minus_fct. *)
Notation fsub f g := (fadd f (fopp g)).
Notation fmul := mult_fct.
Notation finv := inv_fct.
(* Notation fdiv := div_fct. *)
Notation fdiv f g := (fmul f (finv g)).

(** Scalar multiplication of real function *)
Definition fcmul (c : R) (f : R -> R) := fun x => c * f x.


Infix "+f" := fadd : RFun_scope.
Infix "-f" := fsub : RFun_scope.
Infix "*f" := fmul : RFun_scope.
Infix "/f" := fdiv : RFun_scope.
Infix "/f" := fdiv : RFun_scope.
Notation "-f g" := (fopp g) : RFun_scope.
Notation "/f g" := (finv g) : RFun_scope.
Infix "c*" := fcmul : RFun_scope.


(* ======================================================================= *)
(** ** Real constant functions *)

Definition fcnst (C : R) : R -> R := fun _ => C.
Definition fzero : R -> R := fcnst R0.
Definition fone : R -> R := fcnst R1.
(* Definition fid : R -> R := fun x => x. *)
(* Notation "0" := fzero : RFun_scope. *)
(* Notation "1" := fone : RFun_scope. *)


(* ======================================================================= *)
(** ** Properties of real functions *)


Hint Unfold fadd fopp fmul finv fcnst fzero fone : RFun.

Lemma fadd_ok : forall (u v : R -> R) (x : R), (u +f v) x = u x + v x. intros. auto. Qed.
Lemma fopp_ok : forall (v : R -> R) (x : R), (-f v) x = - v x. auto. Qed.
Lemma fsub_ok : forall (u v : R -> R) (x : R), (u -f v) x = u x - v x. auto. Qed.
Lemma fmul_ok : forall (u v : R -> R) (x : R), (u *f v) x = u x * v x. auto. Qed.
Lemma finv_ok : forall (v : R -> R) (x : R), (/f v) x = / v x. auto. Qed.
Lemma fdiv_ok : forall (u v : R -> R) (x : R), (u /f v) x = u x / v x. auto. Qed.
Lemma fcmul_ok : forall (c : R) (u : R -> R) (x : R), (c c* u) x = c * u x. auto. Qed.


(* ======================================================================= *)
(** ** Automation for real functions *)

(** A useful tactic for converting function equality to value equality *)
Ltac feq :=
  intros;
  let x := fresh "x" in
  extensionality x;
  repeat (rewrite ?fadd_ok,?fopp_ok,?fsub_ok,?fmul_ok,?finv_ok,?fdiv_ok, ?fcmul_ok);
  autounfold with RFun;
  ra.
  (* try unfold fzero; *)
  (* try unfold fcnst. *)


(* ======================================================================= *)
(** ** Additional properties for real functions *)

Lemma fadd_0_l : forall f, fzero +f f = f. feq. Qed.
Lemma fadd_0_r : forall f, f +f fzero = f. feq. Qed.
Lemma fadd_opp_l : forall f, -f f +f f = fzero. feq. Qed.
Lemma fadd_opp_r : forall f, f +f -f f = fzero. feq. Qed.
Lemma fmul_1_l : forall f, fone *f f = f. feq. Qed.
Lemma fmul_1_r : forall f, f *f fone = f. feq. Qed.
Lemma fmul_inv_l : forall f, (forall x, f x <> 0) -> /f f *f f = fone. feq. Qed.
Lemma fmul_inv_r : forall f, (forall x, f x <> 0) -> f *f /f f = fone. feq. Qed.

Lemma fcmul_assoc1 : forall (c d : R) (u : R -> R), c c* (d c* u) = (c * d) c* u. feq. Qed.
Lemma fcmul_assoc2 : forall (c : R) (u v : R -> R), c c* (u *f v) = (c c* u) *f v. feq. Qed.

(* ======================================================================= *)
(** ** Multiply real function with a natural number *)

(** Multiply with a natural number, i.e., sum the function by n times:
    fnmul f 0 := fun x => 0
    fnmul f 1 := f
    fnmul f 2 := f + f, i.e., fun x => f x + f x
    ...
    fnmul f (S n) := fun x => f x + (fnmul f n) *)
Fixpoint fnmul (n : nat) (f : R -> R) : R -> R :=
  match n with
  | O => fun x => 0
  | S O => f
  | S n' => fadd f (fnmul n' f)
  end.


(* ######################################################################### *)
(** * Algebraic structures *)

(** equality is equivalence relation: Equivalence (@eq (R -> R)) *)
Hint Resolve eq_equivalence : Rfun.

(** operations are well-defined. Eg: Proper (eq ==> eq ==> eq) fadd *)

Lemma fadd_wd : Proper (eq ==> eq ==> eq) fadd.
Proof. simp_proper. intros; subst; auto. Qed.

Lemma fopp_wd : Proper (eq ==> eq) fopp.
Proof. simp_proper. intros; subst; auto. Qed.

Lemma fmul_wd : Proper (eq ==> eq ==> eq) fmul.
Proof. simp_proper. intros; subst; auto. Qed.

Lemma finv_wd : Proper (eq ==> eq) finv.
Proof. simp_proper. intros; subst; auto. Qed.

Hint Resolve
  fadd_wd fopp_wd
  fmul_wd finv_wd
  : Rfun.

(** Associative *)

#[export] Instance fadd_Assoc : Associative fadd.
Proof. constructor; intros. feq. Qed.

#[export] Instance fmul_Assoc : Associative fmul.
Proof. constructor; intros. feq. Qed.

Hint Resolve
  fadd_Assoc
  fmul_Assoc
  : Rfun.

(** Commutative *)

#[export] Instance fadd_Comm : Commutative fadd.
Proof. constructor; intros. feq. Qed.

#[export] Instance fmul_Comm : Commutative fmul.
Proof. constructor; intros. feq. Qed.

Hint Resolve
  fadd_Comm
  fmul_Comm
  : Rfun.

(** Identity Left/Right *)
#[export] Instance fadd_IdL : IdentityLeft fadd fzero.
Proof. constructor; intros. feq. Qed.

#[export] Instance fadd_IdR : IdentityRight fadd fzero.
Proof. constructor; intros. feq. Qed.

#[export] Instance fmul_IdL : IdentityLeft fmul fone.
Proof. constructor; intros. feq. Qed.

#[export] Instance fmul_IdR : IdentityRight fmul fone.
Proof. constructor; intros. feq. Qed.

Hint Resolve
  fadd_IdL fadd_IdR
  fmul_IdL fmul_IdR
  : Rfun.

(** Inverse Left/Right *)

#[export] Instance fadd_InvL : InverseLeft fadd fzero fopp.
Proof. constructor; intros. feq. Qed.

#[export] Instance fadd_InvR : InverseRight fadd fzero fopp.
Proof. constructor; intros. feq. Qed.

Hint Resolve fadd_InvL fadd_InvR : Rfun.

(** Distributive *)

#[export] Instance fmul_add_DistrL : DistrLeft fadd fmul.
Proof. constructor; intros. feq. Qed.

#[export] Instance fmul_add_DistrR : DistrRight fadd fmul.
Proof. constructor; intros. feq. Qed.

Hint Resolve
  fmul_add_DistrL
  fmul_add_DistrR
  : Rfun.

(** Semigroup *)

#[export] Instance fadd_SGroup : SGroup fadd.
Proof. constructor; auto with Rfun. Qed.

#[export] Instance fmul_SGroup : SGroup fmul.
Proof. constructor; auto with Rfun. Qed.

Hint Resolve
  fadd_SGroup
  fmul_SGroup
  : Rfun.

(** Abelian semigroup *)

#[export] Instance fadd_ASGroup : ASGroup fadd.
Proof. constructor; auto with Rfun. Qed.

#[export] Instance fmul_ASGroup : ASGroup fmul.
Proof. constructor; auto with Rfun. Qed.

Hint Resolve
  fadd_ASGroup
  fmul_ASGroup
  : Rfun.

Goal forall x1 x2 y1 y2 a b c, x1 + a + b + c + x2 = y1 + c + (b + a) + y2.
Proof. intros. pose proof fadd_ASGroup. asgroup. Abort.

(** Monoid *)
  
#[export] Instance fadd_Monoid : Monoid fadd fzero.
Proof. constructor; auto with Rfun. Qed.

#[export] Instance fmul_Monoid : Monoid fmul fone.
Proof. constructor; auto with Rfun. Qed.

Hint Resolve
  fadd_Monoid
  fmul_Monoid
  : Rfun.

(** Abelian monoid *)
  
#[export] Instance fadd_AMonoid : AMonoid fadd fzero.
Proof. constructor; auto with Rfun. Qed.
  
#[export] Instance fmul_AMonoid : AMonoid fmul fone.
Proof. constructor; auto with Rfun. Qed.

Hint Resolve fadd_AMonoid fmul_AMonoid : Rfun.

(** Group *)

#[export] Instance fadd_Group : Group fadd fzero fopp.
Proof. constructor; auto with Rfun. Qed.

Hint Resolve fadd_Group : Rfun.

(** AGroup *)

#[export] Instance fadd_AGroup : AGroup fadd fzero fopp.
Proof. constructor; auto with Rfun. Qed.

Hint Resolve fadd_AGroup : Rfun.

(** Ring *)

#[export] Instance Rfun_Ring : Ring fadd fzero fopp fmul fone.
Proof. constructor; auto with Rfun. Qed.

Hint Resolve Rfun_Ring : Rfun.

(** ARing *)

#[export] Instance Rfun_ARing : ARing fadd fzero fopp fmul fone.
Proof. constructor; auto with Rfun. Qed.

Hint Resolve Rfun_ARing : Rfun.

Section test.
  Add Ring ring_inst : (make_ring_theory Rfun_ARing).

  Goal forall u v w : R -> R, u -f v *f (u -f w) = w *f v -f u *f v +f u.
  Proof. intros. ring. Qed.
End test.

(** Field *)

#[export] Instance Rfun_Field : Field fadd fzero fopp fmul fone finv.
Proof.
  constructor; auto with Rfun.
  2:{ intro. cbv in H.
      rewrite fun_eq_iff_forall_eq in H. specialize (H R0). lra. }
  1:{ intros. apply fmul_inv_l.
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
  Definition Azero : A := fzero.
  Hint Unfold A Azero : A.

  Lemma AeqDec : Dec (@eq A).
  Proof. constructor. intros a b.
         (* rewrite (functional_extensionality a b). *)
  Admitted.
End ElementTypeRFun.

Module MonoidElementTypeRFun <: MonoidElementType.
  Include ElementTypeRFun.
  
  Definition Aadd := fadd.
  Hint Unfold Aadd : A.
  
  Infix "+" := Aadd : A_scope.

  #[export] Instance Aadd_AMonoid : AMonoid Aadd Azero.
  Proof. intros. repeat constructor; intros; autounfold with A; ring. Qed.
End MonoidElementTypeRFun.

Module RingElementTypeRFun <: RingElementType.
  Include MonoidElementTypeRFun.
  
  Definition Aone : A := fone.
  Definition Aopp := fopp.
  Definition Amul := fmul.
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
