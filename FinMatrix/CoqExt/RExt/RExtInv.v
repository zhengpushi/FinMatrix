(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Simplify the expressions about Rinv and Rdiv.
  author    : Zhengpu Shi
  date      : 2021.05

  remark    :
 *)

Require Export RExtBase.


(* ======================================================================= *)
(** ** Basic automation *)

Hint Rewrite
  (* Rinv *)
  Rinv_1            (* / 1 = 1 *)
  Rdiv_plus_distr   (* (a + b) / c = a / c + b / c *)
  Rsqr_div'         (* (x / y)² = x² / y² *)
  Rdiv_mult_l_l     (* r <> 0 -> (r * r1) / (r * r2) = r1 / r2 *)
  Rdiv_mult_r_r     (* r <> 0 -> (r1 * r) / (r2 * r) = r1 / r2 *)
  : R.

Hint Rewrite
     <- Rdiv_def    (* r1 / r2 = r1 * / r2 *)
  : R.


Hint Resolve
  (* Rinv *)
  Rinv_neq_0_compat   (* r <> 0 -> / r <> 0 *)
  Rinv_0_lt_compat    (* 0 < r -> 0 < / r *)
  Rinv_lt_0_compat    (* r < 0 -> / r < 0 *)
  (* Rdiv *)
  Rdiv_lt_0_compat    (* 0 < a -> 0 < b -> 0 < a / b *)
  : R.

(* ======================================================================= *)
(** ** Additional properties *)

(** / R1 = 1 *)
Lemma Rinv_R1 : / R1 = 1.
Proof. ra. Qed.
Hint Rewrite Rinv_R1 : R.

(** a / 1 = a *)
Lemma Rdiv_1 : forall a, a / 1 = a.
Proof. ra. Qed.
Hint Rewrite Rdiv_1 : R.

(** 0 / a = 0 *)
Lemma Rdiv_0_eq0 : forall a : R, a <> 0 -> 0 / a = 0.
Proof. ra. Qed.
Hint Rewrite Rdiv_0_eq0 : R.

(** (r1 * r2) * / (r1 * r3) = r2 * / r3  *)
Lemma Rinv_ab_simpl_a : forall r1 r2 r3,
    r1 <> 0 -> r3 <> 0 -> (r1 * r2) * / (r1 * r3) = r2 * / r3.
Proof. ra. Qed.
Hint Rewrite Rinv_ab_simpl_a : R.

(** (r1 * r2) * / (r3 * r2) = r1 * / r3 *)
Lemma Rinv_ab_simpl_b : forall r1 r2 r3,
    r2 <> 0 -> r3 <> 0 -> (r1 * r2) * / (r3 * r2) = r1 * / r3.
Proof. ra. Qed.
Hint Rewrite Rinv_ab_simpl_b : R.

(** r <> 0 -> 1 / r <> 0 *)
Lemma Rdiv_1_neq_0_compat : forall r : R, r <> 0 -> 1 / r <> 0.
Proof. ra. pose proof (Rinv_neq_0_compat r H). ra. Qed.
Hint Resolve Rdiv_1_neq_0_compat : R.


(* ======================================================================= *)
(** ** Extra automation *)
