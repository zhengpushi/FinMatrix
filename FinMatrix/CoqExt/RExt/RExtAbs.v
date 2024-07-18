(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Simplify the expressions about Rabs.
  author    : Zhengpu Shi
  date      : 2021.05

  remark    :
 *)

Require Export RExtBase RExtBool.

Notation "| r |" := (Rabs r) : R_scope.


(* ======================================================================= *)
(** ** Basic automation *)

Hint Rewrite
  Rabs_R0             (* |0| = 0 *)
  Rabs_Ropp           (* |-x| = |x| *)
  Rabs_Rabsolu        (* | |x| | = |x| *)
  : R.

Hint Resolve
  Rabs_pos            (* 0 <= |x| *)
  sqrt_pos            (* 0 <= sqrt x *)
  Rabs_right          (* r >= 0 -> |r| = r *)
  Rabs_pos_eq         (* 0 <= r -> |r| = r *)
  Rabs_left           (* r < 0 -> |r| = - r *)
  Rabs_left1          (* r <= 0 -> |r| = - r *)
  Rabs_no_R0          (* r <> 0 -> |r| <> 0 *)
  : R.


(* ======================================================================= *)
(** ** Additional properties *)

(* Tips, solve symmetry problems. Such as : r = |r| *)

(** 0 <= r -> r = |r| *)
Lemma Rabs_right_sym : forall r : R, 0 <= r -> r = |r|.
Proof. intros; symmetry; ra. Qed.
Hint Resolve Rabs_right_sym : R.

(** r < 0 -> - r = |r| *)
Lemma Rabs_left_sym : forall r : R, r < 0 -> - r = |r|.
Proof. intros; symmetry; ra. Qed.
Hint Resolve Rabs_left_sym : R.

(** r <= 0 -> - r = |r| *)
Lemma Rabs_left1_sym : forall r : R, r <= 0 -> - r = |r|.
Proof. intros; symmetry; ra. Qed.
Hint Resolve Rabs_left1_sym : R.

(** 0 <= r -> | -r | = r *)
Lemma Rabs_neg_l : forall r, 0 <= r -> | -r | = r.
Proof. ra. Qed.
Hint Resolve Rabs_neg_l : R.

(** r < 0 -> | -r| = -r *)
Lemma Rabs_neg_r : forall r, r < 0 -> | -r| = -r.
Proof. ra. Qed.
Hint Resolve Rabs_neg_r : R.


(** 0 <= r -> | r | = r *)
Lemma Rabs_pos_imply : forall r, 0 <= r -> | r | = r.
Proof. ra. Qed.

(** | r | = r -> 0 <= r *)
Lemma Rabs_pos_if : forall r, | r | = r -> 0 <= r.
Proof.
  intros.
  bdestruct (r <=? 0); auto; ra.
  apply Rabs_left1 in H0.
  assert (r = 0); lra.
Qed.
Hint Resolve Rabs_pos_if : R.

(** r <= 0 ->  | r | = - r *)
Lemma Rabs_neg_imply : forall r, r <= 0 -> | r | = - r.
Proof. ra. Qed.
Hint Resolve Rabs_neg_imply : R.

(** | r | = - r -> r <= 0 *)
Lemma Rabs_neg_if : forall r, | r | = - r -> r <= 0.
Proof.
  intros. bdestruct (r <=? 0); ra.
  bdestruct (r =? 0); ra.
  assert (r > 0); ra.
  rewrite Rabs_right in H; ra.
Qed.
Hint Resolve Rabs_neg_if : R.

(** |a| <= b -> - b <= a <= b *)
Lemma Rabs_le_rev : forall a b : R, |a| <= b -> - b <= a <= b.
Proof.
  intros. bdestruct (a <? 0).
  - assert (|a| = -a); ra.
  - assert (|a| = a); ra.
    apply Rabs_pos_imply; ra.
Qed.

(** 0 < r -> r / | r | = 1 *)
Lemma Rdiv_abs_gt0 : forall r, 0 < r -> r / | r | = 1.
Proof. intros. rewrite Rabs_right; ra. Qed.
Hint Resolve Rdiv_abs_gt0 : R.

(** r < 0 -> r / | r | = -1 *)
Lemma Rdiv_abs_lt0 : forall r, r < 0 -> r / | r | = -1.
Proof. intros. rewrite Rabs_left; ra. Qed.
Hint Resolve Rdiv_abs_lt0 : R.

(** 0 < r -> | r | = 1 -> r = 1 *)
Lemma Rabs_gt0_eq1 : forall r : R, 0 < r -> | r | = 1 -> r = 1.
Proof. intros. unfold Rabs in H0. destruct (Rcase_abs); lra. Qed.

(** r < 0 -> | r | = 1 -> r = - 1 *)
Lemma Rabs_lt0_eq_n1 : forall r : R, r < 0 -> | r | = 1 -> r = -1.
Proof. intros. unfold Rabs in H0. destruct (Rcase_abs); lra. Qed.


(* ======================================================================= *)
(** ** Extra automation *)

