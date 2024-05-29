(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Simplify the expressions about Rabs.
  author    : ZhengPu Shi
  date      : 2021.05

  remark    :
 *)

Require Export RExtBase.

Notation "| r |" := (Rabs r) : R_scope.


(* ======================================================================= *)
(** ** Basic automation *)

#[export] Hint Rewrite
  Rabs_R0             (* |0| = 0 *)
  Rabs_Ropp           (* |-x| = |x| *)
  Rabs_Rabsolu        (* | |x| | = |x| *)
  : R.

#[export] Hint Resolve
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

(** r >= 0 -> r = |r| *)
Lemma Rabs_right_sym : forall r : R, r >= 0 -> r = |r|.
Proof. intros; symmetry; ra. Qed.

(** 0 <= r -> r = |r| *)
Lemma Rabs_pos_eq_sym : forall x : R, 0 <= x -> x = |x|.
Proof. intros; symmetry; ra. Qed.

(** r < 0 -> - r = |r| *)
Lemma Rabs_left_sym : forall r : R, r < 0 -> - r = |r|.
Proof. intros; symmetry; ra. Qed.

(** r <= 0 -> - r = |r| *)
Lemma Rabs_left1_sym : forall r : R, r <= 0 -> - r = |r|.
Proof. intros; symmetry; ra. Qed.

#[export] Hint Resolve
  Rabs_right_sym
  Rabs_pos_eq_sym
  Rabs_left_sym
  Rabs_left1_sym
  : R.

(** 0 <= r -> | -r | = r *)
Lemma Rabs_neg_l : forall r, 0 <= r -> | -r | = r.
Proof. ra. Qed.
#[export] Hint Resolve Rabs_neg_l : R.

(** r < 0 -> | -r| = -r *)
Lemma Rabs_neg_r : forall r, r < 0 -> | -r| = -r.
Proof. ra. Qed.
#[export] Hint Resolve Rabs_neg_r : R.



(* ======================================================================= *)
(** ** Extra automation *)

