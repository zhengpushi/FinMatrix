(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : bool comparison for R type.
  author    : Zhengpu Shi
  date      : 2021.05

  remark    :
 *)

Require Export Basic RExtBase.


(* ######################################################################### *)
(** * Reqb,Rleb,Rltb: Boolean comparison of R *)

Definition Reqb (r1 r2 : R) : bool := if Req_dec_T r1 r2 then true else false.
Definition Rleb (r1 r2 : R) : bool := if Rle_lt_dec r1 r2 then true else false.
Definition Rltb (r1 r2 : R) : bool := if Rlt_le_dec r1 r2 then true else false.
Infix "=?"  := Reqb : R_scope.
Notation "x >? y"  := (Rltb y x) : R_scope.
Notation "x >=? y" := (Rleb y x) : R_scope.
Infix "<?"  := Rltb : R_scope.
Infix "<=?" := Rleb : R_scope.
    
Lemma Reqb_reflect : forall x y : R, reflect (x = y) (x =? y).
Proof. intros. unfold Reqb. destruct Req_dec_T; constructor; auto. Qed.
Hint Resolve Reqb_reflect : bdestruct.

Lemma Rltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof. intros. unfold Rltb. destruct Rlt_le_dec; constructor; lra. Qed.
Hint Resolve Rltb_reflect : bdestruct.

Lemma Rleb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof. intros. unfold Rleb. destruct Rle_lt_dec; constructor; lra. Qed.
Hint Resolve Rleb_reflect : bdestruct.

(** Automaticaly destruct boolean operation of R type *)
Ltac autoRbool :=
  repeat
    match goal with
    | H:context [?x =? ?y] |- _ => bdestruct (x =? y)
    | H:context [?x <? ?y] |- _ => bdestruct (x <? y)
    | H:context [?x <=? ?y] |- _ => bdestruct (x <=? y)
    | |- context [?x =? ?y] => bdestruct (x =? y)
    | |- context [?x <? ?y] => bdestruct (x <? y)
    | |- context [?x <=? ?y] => bdestruct (x <=? y)
    | H:context [Req_dec_T  ?x ?y] |- _ => destruct (Req_dec_T  x y)
    | H:context [Rlt_le_dec ?x ?y] |- _ => destruct (Rlt_le_dec x y)
    | H:context [Rle_lt_dec ?x ?y] |- _ => destruct (Rle_lt_dec x y)
    | |- context [Req_dec_T  ?x ?y] => destruct (Req_dec_T  x y)
    | |- context [Rlt_le_dec ?x ?y] => destruct (Rlt_le_dec x y)
    | |- context [Rle_lt_dec ?x ?y] => destruct (Rle_lt_dec x y)
    end.

Lemma Reqb_true : forall x y, x =? y = true <-> x = y.
Proof. intros. autoRbool; lra. Qed.

Lemma Reqb_false : forall x y, x =? y = false <-> x <> y.
Proof. intros. autoRbool; lra. Qed.

Lemma Reqb_refl : forall r, r =? r = true.
Proof. intros. autoRbool; lra. Qed.

Lemma Reqb_comm : forall r1 r2, (r1 =? r2) = (r2 =? r1).
Proof. intros. autoRbool; lra. Qed.

Lemma Reqb_trans : forall r1 r2 r3, r1 =? r2 = true ->
  r2 =? r3 = true -> r1 =? r3 = true.
Proof. intros. autoRbool; lra. Qed.

(* x <=? x = true *)
Lemma Rleb_refl : forall x : R, x <=? x = true.
Proof. intros. autoRbool; lra. Qed.

(* (x <=? - y) = (-x >=? y) *)
Lemma Rleb_opp_r : forall x y : R, (x <=? - y) = (- x >=? y).
Proof. intros. autoRbool; lra. Qed.

(* (- x <=? y) = (x >=? - y) *)
Lemma Rleb_opp_l : forall x y : R, (- x <=? y) = (x >=? - y).
Proof. intros. autoRbool; lra. Qed.

(** (a - b <? 0) = (0 <? b - a) *)
Lemma Rminus_ltb0_comm : forall a b : R, (a - b <? 0) = (0 <? b - a).
Proof. intros. autoRbool; lra. Qed.
  
(** (a - b >? 0) = (0 >? b - a) *)
Lemma Rminus_gtb0_comm : forall a b : R, (a - b >? 0) = (0 >? b - a).
Proof. intros. autoRbool; lra. Qed.
