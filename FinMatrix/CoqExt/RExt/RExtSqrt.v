(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Simplify the expressions about sqrt.
  author    : Zhengpu Shi
  date      : 2021.05

  remark    :
 *)

Require Export RExtBase RExtBool RExtPlus RExtOpp RExtMult RExtInv RExtSqr RExtAbs.


(* ======================================================================= *)
(** ** Basic automation *)

Hint Rewrite
  sqrt_0              (* sqrt 0 = 0 *)
  sqrt_1              (* sqrt 1 = 1 *)
  sqrt_Rsqr_abs       (* sqrt x² = |x| *)
  sqrt_inv            (* sqrt (/ x) = / sqrt x *)
  : R.

Hint Resolve
  sqrt_lt_R0          (* 0 < x -> 0 < sqrt x *)
  sqrt_neg_0          (* x <= 0 -> sqrt x = 0 *)
  sqrt_sqrt           (* 0 <= x -> sqrt x * sqrt x = x *)
  sqrt_pow2           (* 0 <= x -> sqrt (x ^ 2) = x *)
  sqrt_Rsqr           (* 0 <= x -> sqrt x² = x *)
  sqrt_square         (* 0 <= x -> sqrt (x * x) = x *)
  pow2_sqrt           (* 0 <= x -> (sqrt x) ^ 2 = x *)
  Rsqr_sqrt           (* 0 <= x -> (sqrt x)² = x *)
  : R.

(* sqrt_inj            (* 0 <= x -> 0 <= y -> sqrt x = sqrt y -> x = y *) *)


(* ======================================================================= *)
(** ** Additional properties *)

(** *** About sqrt with 0 *)

(** sqrt R0 = 0 *)
Lemma sqrt_R0 : sqrt R0 = 0.
Proof. rewrite R0_eq_0. ra. Qed.
Hint Rewrite sqrt_R0 : R.

(** r = 0 -> sqrt r = 0 *)
Lemma sqrt_0_eq0 : forall r, r = 0 -> sqrt r = 0.
Proof. intros. rewrite H. ra. Qed.
Hint Resolve sqrt_0_eq0 : R.

(** r < 0 -> sqrt r = 0 *)
Lemma sqrt_lt0_eq_0 : forall r, r < 0 -> sqrt r = 0.
Proof. ra. Qed.
Hint Resolve sqrt_lt0_eq_0 : R.

(** 0 < sqrt x -> 0 < x *)
Lemma sqrt_gt0_imply_gt0 : forall (x : R), 0 < sqrt x -> 0 < x.
Proof.
  ra. replace 0 with (sqrt 0) in H; auto with R.
  apply sqrt_lt_0_alt in H; auto.
Qed.
Hint Resolve sqrt_gt0_imply_gt0 : R.

(** 0 < sqrt x -> 0 <= x *)
Lemma sqrt_gt0_imply_ge0 : forall (x : R), 0 < sqrt x -> 0 <= x.
Proof. ra. apply Rlt_le. apply sqrt_gt0_imply_gt0; auto. Qed.
Hint Resolve sqrt_gt0_imply_ge0 : R.

(** sqrt x = 0 -> x <= 0 *)
Lemma sqrt_eq0_imply : forall r, sqrt r = 0 -> r <= 0.
Proof.
  ra. bdestruct (r <=? 0); ra.
  apply Rnot_le_lt in H0. apply sqrt_lt_R0 in H0. ra.
Qed.
Hint Resolve sqrt_eq0_imply : R.

(** x <= 0 -> sqrt x = 0 *)
Lemma sqrt_eq0_if : forall r, r <= 0 -> sqrt r = 0.
Proof. ra. Qed.
Hint Resolve sqrt_eq0_if : R.

(** sqrt x = 0 <-> x <= 0 *)
Lemma sqrt_eq0_iff : forall r, sqrt r = 0 <-> r <= 0.
Proof. ra. Qed.

(** sqrt x <> 0 -> x > 0 *)
Lemma sqrt_neq0_imply : forall r, sqrt r <> 0 -> r > 0.
Proof. intros. rewrite sqrt_eq0_iff in H. lra. Qed.
Hint Resolve sqrt_neq0_imply : R.

(** x > 0 -> sqrt x <> 0 *)
Lemma sqrt_neq0_if : forall r, r > 0 -> sqrt r <> 0.
Proof. intros. rewrite sqrt_eq0_iff. lra. Qed.
Hint Resolve sqrt_neq0_if : R.

(** sqrt x <> 0 <-> x > 0 *)
Lemma sqrt_neq0_iff : forall r, sqrt r <> 0 <-> r > 0.
Proof. ra. Qed.


(** *** About sqrt with 1 *)

(** sqrt R1 = 1 *)
Lemma sqrt_R1 : sqrt R1 = 1.
Proof. rewrite R1_eq_1. ra. Qed.
Hint Rewrite sqrt_R1 : R.

(** sqrt x = 1 -> x = 1 *)
Lemma sqrt_eq1_imply_eq1 : forall (x : R), sqrt x = 1 -> x = 1.
Proof.
  ra.
  assert ((sqrt x)² = 1); ra. rewrite <- H0.
  apply eq_sym. apply Rsqr_sqrt.
  assert (0 < sqrt x); ra.
Qed.
Hint Resolve sqrt_eq1_imply_eq1 : R.

(* ToDo: last lemma cannot solve this goal, it is just a symmetry works *)
Section problem.
  Goal forall a1 a2, sqrt (a1² + a2²) = R1 -> R1 = a1² + a2².
  Proof. intros. ra. symmetry. ra. Abort.
End problem.

(* Thus, we added another lemma *)

(** sqrt x = 1 -> 1 = x *)
Lemma sqrt_eq1_imply_eq1_sym : forall (x : R), sqrt x = 1 -> 1 = x.
Proof. symmetry. ra. Qed.
Hint Resolve sqrt_eq1_imply_eq1_sym : R.


(** x = 1 -> sqrt x = 1 *)
Lemma sqrt_eq1_if_eq1 : forall (x : R), x = 1 -> sqrt x = 1.
Proof. ra. subst; ra. Qed.
Hint Resolve sqrt_eq1_if_eq1 : R.

(** sqrt x = 1 <-> x = 1 *)
Lemma sqrt_eq1_iff : forall (x : R), sqrt x = 1 <-> x = 1.
Proof. ra. Qed.


(** *** About sqrt with Rsqr *)

(** sqrt (r * r) = |r| *)
Lemma sqrt_sqr_abs : forall r, sqrt (r * r) = |r|.
Proof. ra. Qed.
Hint Rewrite sqrt_sqr_abs : R.

(** 0 <= r1 -> 0 <= r2 -> ( √ r1 * √ r2)² = r1 * r2 *)
Lemma Rsqr_sqrt_sqrt r1 r2 : 0 <= r1 -> 0 <= r2 -> (sqrt r1 * sqrt r2)² = r1 * r2.
Proof. ra. rewrite !Rsqr_sqrt; ra. Qed.
Hint Resolve Rsqr_sqrt_sqrt : R.

(** sqrt (r1² + r2²) = 0 -> r1 = 0 /\ r2 = 0 *)
Lemma Rsqrt_plus_sqr_eq0_imply : forall r1 r2 : R, sqrt (r1² + r2²) = 0 -> r1 = 0 /\ r2 = 0.
Proof. ra; intros. apply sqrt_eq_0 in H; ra. Qed.
Hint Resolve Rsqrt_plus_sqr_eq0_imply : R.

(** r1 = 0 /\ r2 = 0 -> sqrt (r1² + r2²) = 0 *)
Lemma Rsqrt_plus_sqr_eq0_if : forall r1 r2 : R, r1 = 0 /\ r2 = 0 -> sqrt (r1² + r2²) = 0.
Proof. ra. Qed.
Hint Resolve Rsqrt_plus_sqr_eq0_if : R.

(** sqrt (r1² + r2²) = 0 <-> r1 = 0 /\ r2 = 0 *)
Lemma Rsqrt_plus_sqr_eq0_iff : forall r1 r2 : R, sqrt (r1² + r2²) = 0 <-> r1 = 0 /\ r2 = 0.
Proof. ra. Qed.

(** 0 <= (sqrt r1) * (sqrt r2) *)
Lemma Rmult_sqrt_sqrt_ge0 : forall r1 r2 : R, 0 <= (sqrt r1) * (sqrt r2).
Proof. ra. apply Rmult_le_pos; ra. Qed.
Hint Resolve Rmult_sqrt_sqrt_ge0 : R.

(** 0 <= (sqrt r1) + (sqrt r2) *)
Lemma Rplus_sqrt_sqrt_ge0 : forall r1 r2 : R, 0 <= (sqrt r1) + (sqrt r2).
Proof. ra. apply Rplus_le_le_0_compat; ra. Qed.
Hint Resolve Rplus_sqrt_sqrt_ge0 : R.

(** r1 <> 0 -> sqrt (r1² + r2²) <> 0 *)
Lemma Rsqr_plus_sqr_neq0_l : forall r1 r2, r1 <> 0 -> sqrt (r1² + r2²) <> 0.
Proof. ra. rewrite Rsqrt_plus_sqr_eq0_iff. ra. Qed.
Hint Resolve Rsqr_plus_sqr_neq0_l : R.

(** r2 <> 0 -> sqrt (r1² + r2²) <> 0 *)
Lemma Rsqr_plus_sqr_neq0_r : forall r1 r2, r2 <> 0 -> sqrt (r1² + r2²) <> 0.
Proof. ra. rewrite Rsqrt_plus_sqr_eq0_iff. ra. Qed.
Hint Resolve Rsqr_plus_sqr_neq0_r : R.

(** /(sqrt (1+(b/a)²)) = abs(a) / sqrt(a*a + b*b) *)
Lemma Rinv_sqrt_plus_1_sqr_div_a_b (a b : R) : a <> 0 ->
  (/ (sqrt (1+(b/a)²)) = |a| / sqrt(a*a + b*b)).
Proof.
  intros.
  replace (1 + (b/a)²) with ((a*a + b*b) / (|a|*|a|)).
  - rewrite sqrt_div_alt; ra. split; ra.
  - ra. destruct (Rcase_abs a).
    + replace (|a|) with (-a); ra.
    + replace (|a|) with a; ra.
Qed.


(* ======================================================================= *)
(** ** Extra automation *)
