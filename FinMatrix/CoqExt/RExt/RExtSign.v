(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Sign function
  author    : Zhengpu Shi
  date      : 2021.05

  remark    :

 *)

Require Export RExtBase RExtBool RExtMult RExtAbs RExtLt.


(* ======================================================================= *)
(** ** Basic automation *)

(* Hint Rewrite *)
(*   : R. *)


(* ======================================================================= *)
(** ** Definition of sign *)

(** sign x = 
    1   if x>0
    0   if x=0
    -1  if x<0
 *)
Definition sign : R -> R :=
  fun x => if x >? 0 then 1 else (if x =? 0 then 0 else -1).


(* ======================================================================= *)
(** ** Additional properties *)


(** x = 0 -> sign x = 0 *)
Lemma sign_eq0 : forall x, x = 0 -> sign x = 0.
Proof.
  intros. unfold sign. bdestruct (0 <? x); ra. bdestruct (x =? 0); ra.
Qed.

(** x > 0 -> sign x = 1 *)
Lemma sign_gt0 : forall x, x > 0 -> sign x = 1.
Proof. intros. unfold sign. bdestruct (x >? 0); ra. Qed.

(** x < 0 -> sign x = - 1 *)
Lemma sign_lt0 : forall x, x < 0 -> sign x = -1.
Proof.
  intros. unfold sign. bdestruct (x >? 0); ra. bdestruct (x =? 0); ra.
Qed.

(** (sign x) * x = |x| *)
Lemma sign_mul_eq_abs : forall x, ((sign x) * x)%R = Rabs x.
Proof.
  intros. unfold sign. bdestruct (0 <? x); ra.
  bdestruct (x =? 0); subst; ra. rewrite Rabs_left1; ra.
Qed.

(** (sign x) * |x| = x *)
Lemma sign_mul_abs_eq : forall x, ((sign x) * (Rabs x))%R = x.
Proof.
  intros. unfold sign. bdestruct (0 <? x); ra.
  bdestruct (x =? 0); ra. rewrite Rabs_left1; ra.
Qed.
