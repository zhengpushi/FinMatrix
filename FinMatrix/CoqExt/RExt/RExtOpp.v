(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Simplify the expressions about Ropp and Rminus.
  author    : Zhengpu Shi
  date      : 2021.05

  remark    :
 *)

Require Export RExtBase.


(* ======================================================================= *)
(** ** Basic automation *)

Hint Rewrite
  Ropp_0              (* - 0 = 0 *)
  Rminus_0_r          (* r - 0 = r *)
  Ropp_involutive     (* - - r = r *)
  Rplus_opp_r         (* r + - r = 0 *)
  Rplus_opp_l         (* - r + r = 0 *)
  Rminus_diag         (* r - r = 0 *)
  Ropp_mult_distr_r_reverse     (* r1 * - r2 = - (r1 * r2) *)
  Ropp_mult_distr_l_reverse     (* - r1 * r2 = - (r1 * r2) *)
  Rdiv_opp_l          (* - x / y = - (x / y) *)
  Rdiv_opp_r          (* x / - y = - (x / y) *)
  : R.


(* ======================================================================= *)
(** ** Additional properties *)

(** r1 - (- r2) = r1 + r2 *)
Lemma Rsub_opp r1 r2 : r1 - (- r2) = r1 + r2.
Proof. ra. Qed.
Hint Rewrite Rsub_opp : R.

(** (- r)² = r² *)
Lemma Rsqr_opp : forall r : R, (- r)² = r².
Proof. intros. rewrite <- Rsqr_neg. auto. Qed.
Hint Rewrite Rsqr_opp : R.

(** - ((- r) * r) = r² *)
Lemma Ropp_Rmul_Ropp_l : forall (r : R), - ((- r) * r) = r².
Proof. intros. cbv. ring. Qed.
Hint Rewrite Ropp_Rmul_Ropp_l : R.

(** - (r * (- r)) = r² *)
Lemma Ropp_Rmul_Ropp_r : forall (r : R), - (r * (- r)) = r².
Proof. intros. cbv. ring. Qed.
Hint Rewrite Ropp_Rmul_Ropp_r : R.

(** (- 1) * r = - r *)
Lemma Rmult_neg1_l : forall r : R, (- 1) * r = - r.
Proof. intros. lra. Qed.
Hint Rewrite Rmult_neg1_l : R.

(** r * (- 1) = - r *)
Lemma Rmult_neg1_r : forall r : R, r * (- 1) = - r.
Proof. intros. lra. Qed.
Hint Rewrite Rmult_neg1_r : R.

(* ======================================================================= *)
(** ** Extra automation *)
