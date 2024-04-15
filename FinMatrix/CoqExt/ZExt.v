(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : extension for Z.
  author    : ZhengPu Shi
  date      : 2022.04
*)

Require Export ZArith.
Require Export Hierarchy.  
Open Scope Z.


(* ######################################################################### *)
(** * Mathematical Structure *)

(** *** well-defined *)
Hint Resolve
  Z.add_wd Z.opp_wd Z.sub_wd Z.mul_wd (* Z *)
  : wd.

#[export] Instance Z_eq_Dec : Dec (@eq Z).
Proof. constructor. apply Z.eq_dec. Defined.

#[export] Instance Z_le_Dec : Dec Z.le.
Proof. constructor. intros. destruct (Z_le_gt_dec a b); auto. Defined.

#[export] Instance Z_lt_Dec : Dec Z.lt.
Proof. constructor. intros. destruct (Z_lt_le_dec a b); auto. right. lia. Defined.

(* n <= n *)
Lemma Z_le_refl : forall n : Z, n <= n.
Proof. intros. lia. Qed.

Lemma Z_zero_le_sqr : forall a : Z, 0 <= a * a.
Proof. intros. apply Z.square_nonneg. Qed.

Lemma Z_add_le_compat : forall a1 b1 a2 b2 : Z, a1 <= a2 -> b1 <= b2 -> a1 + b1 <= a2 + b2.
Proof. intros. lia. Qed.

Lemma Z_add_eq_0_reg_l : forall a b : Z, 0 <= a -> 0 <= b -> a + b = 0 -> a = 0.
Proof. intros. lia. Qed.

#[export] Instance Z_Order : Order Z.lt Z.le Z.ltb Z.leb.
Proof.
  constructor; intros; try lia. apply Z_dec'.
  apply Z.ltb_spec0. apply Z.leb_spec0.
Qed.


Section test.
  Goal forall a b : Z, {a = b} + {a <> b}.
  Proof. intros. apply Aeqdec. Abort.
End test.


(* ######################################################################### *)
(** * Conversion between Z and other types *)
Definition nat2Z (n : nat) : Z := Z.of_nat n.
Definition Z2nat (z : Z) : nat := Z.to_nat z.


(* ######################################################################### *)
(** * Properties for Zeqb and Zeq *)

Definition Zeqb := Z.eqb.

Infix     "=?"          := Zeqb           : Z_scope.

(** Reflection of (=) and (=?) *)
Lemma Zeqb_true_iff : forall x y, x =? y = true <-> x = y.
Proof.
  apply Z.eqb_eq.
Qed.

Lemma Zeqb_false_iff : forall x y, x =? y = false <-> x <> y.
Proof.
  apply Z.eqb_neq.
Qed.


(* ######################################################################### *)
(** * Other properties *)

(** Boolean equality of Zadd satisfy right cancelling rule *)
Lemma Zadd_eqb_cancel_r : forall (z1 z2 a : Z),
  (z1 + a =? z2 + a)%Z = (z1 =? z2)%Z.
Proof.
  intros.
  remember (z1 =? z2)%Z as b1 eqn : H1.
  remember (z1 + a =? z2 + a)%Z as b2 eqn : H2.
  destruct b1,b2; auto.
  - apply eq_sym in H1,H2. apply Z.eqb_eq in H1. apply Z.eqb_neq in H2.
    subst. auto.
  - apply eq_sym in H1,H2. apply Z.eqb_neq in H1. apply Z.eqb_eq in H2.
    apply Z.add_cancel_r in H2. apply H1 in H2. easy.
Qed.
