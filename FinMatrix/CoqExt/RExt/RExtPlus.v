(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Simplify the expressions about Rplus.
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
  : R.

(* Hint Resolve *)
(*   : R. *)


(* ======================================================================= *)
(** ** Additional properties *)

(** a = 0 -> b = 0 -> a + b = 0 *)
Lemma Rplus_eq0_if_both0 : forall a b : R, a = 0 -> b = 0 -> a + b = 0.
Proof. intros. subst. lra. Qed.
Hint Resolve Rplus_eq0_if_both0 : R.

(** 0 <= a -> 0 <= b -> a + b = 0 -> b = 0 *)
Lemma Rplus_eq_0_r : forall a b : R, 0 <= a -> 0 <= b -> a + b = 0 -> b = 0.
Proof. intros. lra. Qed.
