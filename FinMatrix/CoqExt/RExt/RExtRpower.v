(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Simplify the expressions about Rpower.
  author    : Zhengpu Shi
  date      : 2021.05

  remark    :
  1. Definition of Rpower
     x ^ y = Rpower x y := exp (y * ln x)

     a^n       = a * a * ... * a    (* there are n numbers *)
     a^0       = 1 (a ≠ 0)
     a^(-n)    = 1 / a^n (a ≠ 0)
     a^(m/n)   = n√ a^m  (a > 0)
     a^(-m/n)  = 1 / n√ a^m  (a > 0)

 *)

Require Export RExtBase.


(* ======================================================================= *)
(** ** Basic automation *)

Hint Rewrite
  Rpower_O            (* Rpower x 0 = 1 *)
  Rpower_1            (* power x 1 = x *) 
  : R.

(* ======================================================================= *)
(** ** Additional properties *)


Fact Rpower_add : forall a x y,
    a > 0 -> Rpower a (x + y) = (Rpower a x) * (Rpower a y).
Admitted.

Fact Rpower_sub : forall a x y,
    a > 0 -> Rpower a (x - y) = (Rpower a x) / (Rpower a y).
Admitted.

Fact Rpower_mul : forall a x y,
    a > 0 -> Rpower a (x * y) = Rpower (Rpower a x) y.
Admitted.

Fact Rpower_div : forall a b x,
    a > 0 /\ b > 0 -> Rpower (a/b) x = (Rpower a x) / (Rpower b x).
Admitted.

Lemma Rpower_neq0 x y : x <> 0 -> Rpower x y <> 0.
Proof.
Abort.

Lemma Rpower_gt0 : forall x y, 0 < Rpower x y.
Proof. intros. lazy [Rpower]. apply exp_pos. Qed.

Lemma Rpower_1 : forall x, 0 < x -> Rpower x 1 = x.
Proof. intros. rewrite Rpower_1; auto. Qed.

Lemma Rpower_n1 : forall x, Rpower x (-1) = (/ x)%R.
Admitted.

Lemma Rpower_2 : forall x, Rpower x 2 = x * x.
Admitted.

Lemma Rpower_3 : forall x, Rpower x 3 = x * x * x.
Admitted.

Lemma Rpower_inv2 : forall x, Rpower x (/2) = sqrt x.
Admitted.

(* Note, the condition "0 < b" is too strong!! *)
Lemma Rpower_inv3 : forall a b : R, 0 < b -> b ^ 3 = a -> Rpower a (/3) = b.
Proof.
  intros. rewrite <- H0. rewrite <- Rpower_pow; try lra.
  rewrite Rpower_mult. rewrite <- Rpower_1; auto. f_equal. cbv. lra.
Qed.

Lemma Rpower_inv4 : forall a b : R, 0 < b -> b ^ 4 = a -> Rpower a (/4) = b.
Proof.
  intros. rewrite <- H0. rewrite <- Rpower_pow; try lra.
  rewrite Rpower_mult. rewrite <- Rpower_1; auto. f_equal. cbv. lra.
Qed.

Lemma Rpower_invn : forall (n : nat) (a b : R),
    (0 < n)%nat -> 0 < b -> b ^ n = a -> Rpower a (/ (IZR (Z.of_nat n))) = b.
Proof.
  intros. rewrite <- H1. rewrite <- Rpower_pow; try lra.
  rewrite Rpower_mult. rewrite <- Rpower_1; auto. f_equal.
  rewrite <- INR_IZR_INZ. apply Rmult_inv_r.
  apply Rgt_not_eq. apply lt_0_INR. auto.
Qed.

(** Rpower (powerRZ r z) (/ IZR z) = r *)
Lemma Rpower_powerRZ_inv : forall (r : R) (z : Z),
    (z <> 0)%Z -> 0 < r -> Rpower (powerRZ r z) (/ IZR z) = r.
Proof.
  intros. rewrite powerRZ_Rpower; auto.
  rewrite Rpower_mult. rewrite Rmult_inv_r. ra. apply not_0_IZR. auto.
Qed.

(** powerRZ (Rpower r (/ IZR z)) z = r *)
Lemma powerRZ_Rpower_inv : forall (r : R) (z : Z),
    (z <> 0)%Z -> 0 < r -> powerRZ (Rpower r (/ IZR z)) z = r.
Proof.
  intros. rewrite powerRZ_Rpower.
  - rewrite Rpower_mult. rewrite Rmult_inv_l. ra. apply not_0_IZR. auto.
  - apply Rpower_gt0.
Qed.
