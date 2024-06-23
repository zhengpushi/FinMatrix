(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : extension for Positive.
  author    : Zhengpu Shi
  date      : 2023.12
*)

Require Export Numbers.BinNums.
Require Export PArith.BinPos.
(* Import Pos.   (* too many things I needn't, such that `eq` is strange. *) *)
Require Export NatExt.

Open Scope positive_scope.


(* ######################################################################### *)
(** * Mathematical Structure *)

#[export] Instance positive_eq_Dec : Dec (Pos.eq).
Proof. constructor. apply Pos.eq_dec. Defined.

#[export] Instance positive_le_Dec : Dec Pos.le.
Proof.
  constructor. intros. unfold Pos.le.
  destruct (a ?= b); auto. left; easy. left; easy.
Defined.

#[export] Instance positive_lt_Dec : Dec Pos.lt.
Proof.
  constructor. intros. unfold Pos.lt.
  destruct (a ?= b); auto. right; easy. right; easy.
Defined.

Section test.
  Goal forall a b : positive, {a = b} + {a <> b}.
  Proof. intros. apply Aeqdec. Abort.
End test.
