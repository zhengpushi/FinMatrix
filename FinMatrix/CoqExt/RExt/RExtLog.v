(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Logarithmic function 对数函数
  author    : Zhengpu Shi
  date      : 2021.05

  remark    :

 *)

Require Export RExtBase.


(* ======================================================================= *)
(** ** Basic automation *)

(* Hint Rewrite *)
(*   : R. *)


(* ======================================================================= *)
(** ** Definition of Rlog *)


(** log_a x, denoted as {Rlog a x} *)
Definition Rlog (a x : R) : R := ln x / ln a.

(** log_e x, denoted as {Rln x} *)
Definition Rln (x : R) : R := ln x.

(** log_10 x, denoted as {Rlg x} *)
Definition Rlg (x : R) : R := Rlog 10 x.


(* ======================================================================= *)
(** ** Additional properties *)

(* Axiom domain_of_Rlog : forall (a : R), *)
(*     (a > 0 /\ a <> 1) -> domain_of (Rlog a) = (fun x => x > 0). *)
(* Fact range_of_Rlog (a : R) : range_of (Rlog a) = allR. Admitted. *)

(** 特殊函数值 *)
Fact Rlog_a_1 (a : R) : Rlog a 1 = 0.
Proof. unfold Rlog. rewrite ln_1. field. Admitted.

Fact Rlog_a_a (a : R) : Rlog a a = 1. Admitted.
Fact Rln_1 : ln 1 = 0. Admitted.
Fact Rln_e : let e := 2.71828 in ln e = 1. Admitted.

(** 常用公式 *)
Fact Rln_mul : forall a x y, Rlog a (x * y) = (Rlog a x) + (Rlog a y). Admitted.
Fact Rln_div : forall a x y, Rlog a (x / y) = (Rlog a x) - (Rlog a y). Admitted.
Fact Rln_Rpower : forall a x y, Rlog a (Rpower x y) = y * (Rlog a x). Admitted.
Fact Rln_chgbottom : forall a b x, Rlog a x = (Rlog b x) / (Rlog b a). Admitted.
Fact fexpR_Rln : forall x, exp (ln x) = x. Admitted.
Fact Rln_fexpR : forall x, ln (exp x) = x. Admitted.

Fact Rln_eq1 : forall u v : R, Rpower u v = exp (ln (Rpower u v)).
Proof. intros. rewrite fexpR_Rln. auto. Qed.
Fact Rln_eq2 : forall u v : R, Rpower u v = exp (v * ln u).
Proof. intros. Admitted.


