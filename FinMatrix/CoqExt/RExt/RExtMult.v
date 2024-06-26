(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Simplify the expressions about Rmult.
  author    : Zhengpu Shi
  date      : 2021.05

  remark    :
 *)

Require Export RExtBase.


(* ======================================================================= *)
(** ** Basic automation *)

Hint Rewrite
  Rplus_0_l           (* 0 + r = r *)
  Rplus_0_r           (* r + 0 = r *)
  Rmult_0_l           (* 0 * r = 0 *)
  Rmult_0_r           (* r * 0 = 0 *)
  Rmult_1_l           (* 1 * r = r *)
  Rmult_1_r           (* r * 1 = r *)
  Rdiv_1_l            (* 1 / r = / r *)
  Rdiv_1_r            (* r / 1 = r *)
  : R.

Hint Resolve
  Rmult_lt_0_compat   (* 0 < r1 -> 0 < r2 -> 0 < r1 * r2 *)
  : R.


(* ======================================================================= *)
(** ** Additional properties *)

(** a * b = a * c -> b <> c -> a = 0 *)
Lemma Rmult_eq_reg_l_rev : forall a b c : R, a * b = a * c -> b <> c -> a = 0.
Proof. ra. Qed.

(** a * c = b * c -> a <> b -> c = 0 *)
Lemma Rmult_eq_reg_r_rev : forall c a b : R, a * c = b * c -> a <> b -> c = 0.
Proof. ra. Qed.

(** b <> 0 -> a * b = b -> a = 1 *)
Lemma Rmult_eq_r_reg : forall a b : R, b <> 0 -> a * b = b -> a = 1.
Proof.
  intros. replace b with (1 * b)%R in H0 at 2 by lra.
  apply Rmult_eq_reg_r in H0; auto.
Qed.

(** a <> 0 -> a * b = a -> b = 1 *)
Lemma Rmult_eq_l_reg : forall a b : R, a <> 0 -> a * b = a -> b = 1.
Proof.
  intros. replace a with (a * 1)%R in H0 at 2 by lra.
  apply Rmult_eq_reg_l in H0; auto.
Qed.

(** c <> 0 -> a * c = b -> a = b / c *)
Lemma Rmult_imply_Rdiv : forall a b c : R, c <> 0 -> a * c = b -> a = b / c.
Proof. intros. rewrite <- H0. field. auto. Qed.

