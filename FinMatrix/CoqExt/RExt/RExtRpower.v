(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Simplify the expressions about Rpower.
  author    : ZhengPu Shi
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

#[export] Hint Rewrite
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

Lemma Rpower_1_eq : forall x, 0 < x -> Rpower x 1 = x.
Proof. intros. rewrite Rpower_1; auto. Qed.

Lemma Rpower_n1_eq : forall x, Rpower x (-1) = (/ x)%R.
Admitted.

Lemma Rpower_2_eq : forall x, Rpower x 2 = x * x.
Admitted.

Lemma Rpower_3_eq : forall x, Rpower x 3 = x * x * x.
Admitted.

Lemma Rpower_1_2_eq : forall x, Rpower x (1/2) = sqrt x.
Admitted.

