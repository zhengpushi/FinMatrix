(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : bool comparison for R type.
  author    : ZhengPu Shi
  date      : 2021.05

  remark    :
 *)

Require Export RExtBase RExtStruct.


(* ######################################################################### *)
(** * Reqb,Rleb,Rltb: Boolean comparison of R *)

Definition Reqb (r1 r2 : R) : bool := Acmpb Req_Dec r1 r2.
Definition Rleb (r1 r2 : R) : bool := Acmpb Rle_Dec r1 r2.
Definition Rltb (r1 r2 : R) : bool := Acmpb Rlt_Dec r1 r2.
Infix "=?"  := Reqb : R_scope.
Infix "<=?" := Rleb : R_scope.
Infix "<?"  := Rltb : R_scope.
Infix ">?"  := (fun x y => y <? x) : R_scope.
Infix ">=?" := (fun x y => y <=? x) : R_scope.

Lemma Reqb_true : forall x y, x =? y = true <-> x = y.
Proof. apply Acmpb_true. Qed.

Lemma Reqb_false : forall x y, x =? y = false <-> x <> y.
Proof. apply Acmpb_false. Qed.
    
Lemma Reqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros. unfold Reqb,Acmpb. destruct dec; constructor; auto.
Qed.
#[export] Hint Resolve Reqb_reflect : bdestruct.

Lemma Reqb_refl : forall r, r =? r = true.
Proof. intros. unfold Reqb,Acmpb. destruct dec; auto. Qed.

Lemma Reqb_comm : forall r1 r2, (r1 =? r2) = (r2 =? r1).
Proof. intros. unfold Reqb,Acmpb. destruct dec,dec; auto. lra. Qed.

Lemma Reqb_trans : forall r1 r2 r3, r1 =? r2 = true ->
  r2 =? r3 = true -> r1 =? r3 = true.
Proof. intros. unfold Reqb,Acmpb in *. destruct dec,dec,dec; auto. lra. Qed.

Lemma Rltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof. intros. unfold Rltb,Acmpb in *. destruct dec; auto; constructor; lra. Qed.
#[export] Hint Resolve Rltb_reflect : bdestruct.

Lemma Rleb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof. intros. unfold Rleb,Acmpb in *. destruct dec; auto; constructor; lra. Qed.
#[export] Hint Resolve Rleb_reflect : bdestruct.

(* x <=? x = true *)
Lemma Rleb_refl : forall x : R, x <=? x = true.
Proof. intros. bdestruct (x <=? x); auto; lra. Qed.

(* (x <=? - y) = (-x >=? y) *)
Lemma Rleb_opp_r : forall x y : R, (x <=? - y) = (- x >=? y).
Proof. intros. bdestruct (x <=? -y); bdestruct (-x >=? y); lra. Qed.

(* (- x <=? y) = (x >=? - y) *)
Lemma Rleb_opp_l : forall x y : R, (- x <=? y) = (x >=? - y).
Proof. intros. bdestruct (- x <=? y); bdestruct (x >=? -y); lra. Qed.

(** (a - b <? 0) = (0 <? b - a) *)
Lemma Rminus_ltb0_comm : forall a b : R, (a - b <? 0) = (0 <? b - a).
Proof. intros. unfold Rltb,Acmpb. destruct dec,dec; auto; lra. Qed.
  
(** (a - b >? 0) = (0 >? b - a) *)
Lemma Rminus_gtb0_comm : forall a b : R, (a - b >? 0) = (0 >? b - a).
Proof. intros. unfold Rltb,Acmpb. destruct dec,dec; auto; lra. Qed.

