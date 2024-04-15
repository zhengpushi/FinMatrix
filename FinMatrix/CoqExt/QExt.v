(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : extension for Q (rational number).
  author    : ZhengPu Shi
  date      : 2022.04
*)


Require Export PositiveExt ZExt.
Require Export QArith Qround.
Require Export Hierarchy.  
Open Scope Q.


(* ######################################################################### *)
(** ** Mathematical structures *)

(* Global Instance Comm_QAdd : Commutative Qplus Qeq. *)
(* constructor. intros; ring. Qed. *)

(* Global Instance Comm_QMul : Commutative Qmult Qeq. *)
(* constructor. intros; ring. Qed. *)

(** *** well-defined  *)
Hint Resolve
  Qplus_comp Qopp_comp Qminus_comp Qmult_comp Qinv_comp Qdiv_comp (* Q *)
  : wd.

#[export] Instance Q_eq_Dec : Dec (@eq Q).
Proof.
  constructor. intros. destruct a as [p1 q1], b as [p2 q2].
  destruct (Aeqdec p1 p2), (Aeqdec q1 q2); subst; auto.
  all: right; intro; inversion H; easy.
Defined.

#[export] Instance Q_le_Dec : Dec Qle.
Proof.
  constructor. intros. destruct (Qlt_le_dec b a); auto.
  right. intro. apply Qle_not_lt in H. easy.
Defined.

#[export] Instance Q_lt_Dec : Dec Qlt.
Proof.
  constructor. intros. destruct (Qlt_le_dec a b); auto.
  right. intro. apply Qle_not_lt in q. easy.
Defined.

(* n <= n *)
Lemma Q_le_refl : forall n : Q, n <= n.
Proof. apply Qle_refl. Qed.

Section test.
  Goal forall a b : Q, {a = b} + {a <> b}.
  Proof. intros. apply Aeqdec. Abort.
End test.


(* ######################################################################### *)
(** ** Convertion between Q and other types *)

(** Z to Q *)
Definition Z2Q (z : Z) : Q := inject_Z z.

(** nat to Q *)
Definition nat2Q (n : nat) : Q := Z2Q (Z.of_nat n).

(** Q to Z *)
Definition Q2Z_ceiling (q : Q) : Z := Qceiling q.
Definition Q2Z_floor (q : Q) : Z := Qfloor q.


(* ######################################################################### *)
(** * Properties for Qeqb and Qeq *)

(** This axiom just for convenient printing and parsing, LIMITED USE IT.
  
  For example, 3#2 and 6#4 is equivalent, but they are not the same.
  We mainly use this axiom to ensure 3#2 = 6#4, but not to say 3=6 and 2=4.
  
  Be careful for use of any axiom!!
*)
(* Axiom Qeq_iff_eq : forall (a b : Q), Qeq a b <-> a = b. *)

(* Lemma Qneq_iff_neq : forall (a b : Q), ~(Qeq a b) <-> a <> b. *)
(* Proof. *)
(*   intros. split; intros. *)
(*   - intro. apply Qeq_iff_eq in H0. easy. *)
(*   - intro. apply Qeq_iff_eq in H0. easy. *)
(* Qed. *)

(* Lemma Qeqdec : forall q1 q2 : Q, {q1 = q2} + {q1 <> q2}. *)
(* Proof. *)
(*   intros a b. *)
(*   destruct (Qeq_dec a b) as [H|H] eqn : E1. *)
(*   - left. apply Qeq_iff_eq. auto. *)
(*   - right. intro. apply Qeq_iff_eq in H0. auto. *)
(* Defined. *)

Definition Qeqb := Qeq_bool.

Infix     "=="          := Qeq            : Q_scope.
(* Notation  "a ~= b"      := (~(a == b))    : Q_scope. *)
Infix     "=?"          := Qeqb           : Q_scope.

(** Reflection of (==) and (=?) *)
Lemma Qeqb_true_iff_equiv : forall x y, x =? y = true <-> x == y.
Proof.
  apply Qeq_bool_iff.
Qed.

Lemma Qeqb_false_iff_equiv : forall x y, x =? y = false <-> ~ x == y.
Proof. 
  intros; split; intros.
  - intro. apply Qeqb_true_iff_equiv in H0. rewrite H in H0. easy.
  - destruct (Qeqb x y) eqn:E1; auto. apply Qeqb_true_iff_equiv in E1. easy.
Qed.

(* Lemma Qeqb_true_iff : forall x y, x =? y = true <-> x = y. *)
(* Proof. *)
(*   intros; split; intros. *)
(*   - apply Qeq_iff_eq. apply Qeqb_true_iff_equiv. auto. *)
(*   - apply Qeq_iff_eq in H. apply Qeqb_true_iff_equiv. auto. *)
(* Qed. *)

(* Lemma Qeqb_false_iff : forall x y, x =? y = false <-> x <> y. *)
(* Proof.  *)
(*   intros; split; intros. *)
(*   - intro. apply Qeq_iff_eq in H0. apply Qeqb_false_iff_equiv in H. easy. *)
(*   - apply Qeqb_false_iff_equiv. apply Qneq_iff_neq. auto. *)
(* Qed. *)

(** (==) is equivalence relation *)
Lemma Qeq_equiv : equivalence _ Qeq.
Proof.
  split;intro;intros;try easy. rewrite H;try easy.
Qed.


(* ######################################################################### *)
(** ** Instance of classes which defined in HierarchySetoid *)

(* Global Instance Ring_Q : Ring Qplus 0 Qopp Qmult 1 Qeq. *)
(* Proof. *)
(*   repeat constructor; intros; try ring; *)
(*     try apply Qplus_Qeq_proper; *)
(*     try apply Qmult_Qeq_proper; *)
(*     try apply Qopp_Qeq_proper; *)
(*     try apply Qeq_equiv. *)
(* Defined. *)

(* Global Instance Field_Q : Field Qplus 0 Qopp Qmult 1 Qinv Qeq. *)
(* Proof. *)
(*   repeat constructor; intros; try field; auto; *)
(*     try apply Qplus_Qeq_proper; *)
(*     try apply Qmult_Qeq_proper; *)
(*     try apply Qopp_Qeq_proper; *)
(*     try apply Qinv_Qeq_proper; *)
(*     try apply Qeq_equiv. *)
(*   easy. *)
(* Defined. *)


(* ######################################################################### *)
(** ** Others *)

(** This is needed by field_theory (EQ version, original is equiv version) *)
(* Lemma Qmult_inv_l_EQ : forall p : Q, p <> 0 -> /p * p = 1. *)
(* Proof. *)
(*   intros. apply Qeq_iff_eq. rewrite Qmult_comm. *)
(*   apply Qmult_inv_r. apply Qneq_iff_neq. auto. *)
(* Qed. *)
 

(** ** sqrt of Q *)

(** A very rough algorithm for square root of rational number *)
Definition Qsqrt (q : Q) := Qmake (Z.sqrt (Qnum q)) (Pos.sqrt (Qden q)).

(* Example *)
(* Compute Qsqrt 1.21. *)

