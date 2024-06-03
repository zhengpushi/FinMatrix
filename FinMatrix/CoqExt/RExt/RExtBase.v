(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : extension for Coq.Reals.
  author    : ZhengPu Shi
  date      : 2021.05

  remark    :
 *)

Require Export Basic Hierarchy.
Require Export Reals Lia Lra.
Open Scope R_scope.


(* ======================================================================= *)
(** ** Basic automation *)

#[export] Hint Unfold
  Rminus        (* a - b = a + - b *)
  Rdiv          (* a / b = a * / b *)
  (* Rsqr          (* r² = r * r *) *)
  : R.

#[global] Opaque 
  PI exp sqrt Rpower ln
  sin cos tan asin atan acos
  up
.

#[export] Hint Resolve
  Rlt_0_1             (* 0 < 1 *)
  PI_RGT_0            (* PI > 0 *)
  Rabs_pos            (* 0 <= |x| *)
  Rgt_not_eq          (* r1 > r2 -> r1 <> r2 *)
  Rlt_not_eq          (* r1 < r2 -> r1 <> r2 *)
  : R.


(** R Automation *)
Ltac ra :=
  intros;
  (* we always prefer "A -> B; B -> A" instead of "A <-> B" *)
  try match goal with | |- _ <-> _ => split; intros end;
  (* first, try solve it (DONT'T unfold,rewrite ANYTHING) *)
  auto with R;
  try (unfold Rsqr in *; lra);
  try (unfold Rsqr in *; nra);
  try (unfold Rsqr in *; field; auto with R);
  (* next, rewrite it and try to solve it *)
  autorewrite with R in *; auto with R;
  (* next, unify thes expressions: use "a + -b; a * /b" instead of "a - b; a / b" *)
  (* autounfold with R; auto with R; *)
  (* finally, try to solve it again *)
  try (unfold Rsqr in *; lra);
  try (unfold Rsqr in *; nra);
  try (unfold Rsqr in *; field; auto with R)
.


(* ======================================================================= *)
(** ** Additional properties *)

(** R0 = 0 *)
Lemma R0_eq_0 : R0 = 0.
Proof. auto. Qed.
#[export] Hint Rewrite R0_eq_0 : R.

(** R1 = 1 *)
Lemma R1_eq_1 : R1 = 1.
Proof. auto. Qed.
#[export] Hint Rewrite R1_eq_1 : R.

(** 0 <> 1 *)
Lemma zero_neq_1 : 0 <> 1.
Proof. lra. Qed.
#[export] Hint Resolve R1_eq_1 : R.

(** a * b = a -> a = 0 \/ (a <> 0 /\ b = 1) *)
Lemma Rmult_ab_eq_a_imply : forall a b, a * b = a -> a = 0 \/ (a <> 0 /\ b = 1).
Proof. ra. Qed.

(** a * b = b -> b = 0 \/ (b <> 0 /\ a = 1) *)
Lemma Rmult_ab_eq_b_imply : forall a b, a * b = b -> b = 0 \/ (b <> 0 /\ a = 1).
Proof. ra. Qed.


(* ======================================================================= *)
(** ** Extra automation *)

Section test.
  Variable a b c d e f g : R.
End test.
  
