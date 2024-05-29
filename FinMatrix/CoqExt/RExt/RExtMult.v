(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Simplify the expressions about Rmult.
  author    : ZhengPu Shi
  date      : 2021.05

  remark    :
 *)

Require Export RExtBase.


(* ======================================================================= *)
(** ** Basic automation *)

#[export] Hint Rewrite
  Rplus_0_l           (* 0 + r = r *)
  Rplus_0_r           (* r + 0 = r *)
  Rmult_0_l           (* 0 * r = 0 *)
  Rmult_0_r           (* r * 0 = 0 *)
  Rmult_1_l           (* 1 * r = r *)
  Rmult_1_r           (* r * 1 = r *)
  : R.

#[export] Hint Resolve
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
