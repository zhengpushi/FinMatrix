(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Simplify the expressions about Rsqr.
  author    : Zhengpu Shi
  date      : 2021.05

  remark    :
  1. There are several ways to represent square. For example:
    way         explanation
    --------    -------------------------------
    Rmult x x   original definition
    x * x       notation for "Rmult x x"
    Rsqr x      defined as "x * x"
    x²          notation for "Rsqr x"
    pow x 2     a recursive function
    x ^ 2       notation for "pow x 2"

    I want to know which way is better? By "Search" for standard library, I got:
        x * x has 9,  x ^ 2 has 14,   x² has 100.
    Thus,
    i. we should mainly use x², and other ways could be converted to this way,
    2. the lost lemmas would be provided by us.

    Another question, the lra tactic is working well on "x * x" and "pow x 2",
    but not working on "x²".
    So, we use "try (unfold Rsqr in *; lra)" insead of "try lra".
    In addition, using the tactics ring and field also need to unfold Rsqr.

    In conclusion, there are two cases:
    1. when use "ring,field,lra", write: unfold Rsqr in *; ring.
    2. other cases, write: autorewrite with R; auto with R.
 *)

Require Import Reals Lra.
Module about_Rsqr.
  Open Scope R_scope.

  (* statistics on which one is the most popular *)
  (* Search (?a * ?a). (* 10 items *) *)
  (* Search (_²). (* 96 items *) *)
  (* Search (_ ^ 2). (* 14 items *) *)

  (* Problem: ring can't handle Rsqr *)
  Goal forall a b : R, (a * b)² = a² * b². intros. unfold Rsqr. ring. Qed.

  (* Problem: lra can't handle Rsqr *)
  Goal forall a b : R, (a * b)² = a² * b². intros. unfold Rsqr. lra. Qed.

  (* Problem: lra and ring do well on pow (a fixpoin function) *)
  Goal forall a b : R, (a * b) ^ 2 = a ^ 2 * b ^ 2. intros. ring. Qed.
  
End about_Rsqr.

Require Export RExtBase.
Require Export RExtBool RExtPlus RExtMult.


(* ======================================================================= *)
(** ** Basic automation *)

Hint Rewrite
  Rsqr_0              (* 0² = 0 *)
  Rsqr_1              (* 1² = 1 *)
  Rsqr_mult           (* (x * y)² = x² * y² *)
  Rsqr_inv'           (* (/ x)² = / x² *)
  : R.

Hint Resolve
  Rle_0_sqr           (* 0 <= r² *)
  Rsqr_pos_lt         (* x <> 0 -> 0 < x² *)
  Rplus_sqr_eq_0      (* r1² + r2² = 0 -> r1 = 0 /\ r2 = 0 *)
  : R.


(* ======================================================================= *)
(** ** Convert between x², x^n, and x*x *)

(** r * r = r² *)
Lemma xx_Rsqr x : x * x = x².
Proof. auto. Qed.
(* We prefer x², except when using ring or field tactic. *)
Hint Rewrite xx_Rsqr : R.

(** r ^ 2 = r² *)
Lemma Rpow2_Rsqr r : r ^ 2 = r².
Proof. unfold Rsqr. ring. Qed.
Hint Rewrite Rpow2_Rsqr : R.

(** r ^ 4 = (r²)² *)
Lemma Rpow4_Rsqr_Rsqr r : r ^ 4 = r²².
Proof. unfold Rsqr. ring. Qed.
Hint Rewrite Rpow4_Rsqr_Rsqr : R.

(** r ^ 4 = (r ^ 2) ^ 2 *)
Lemma Rpow4_Rsqr_Rsqr' : forall r : R, r ^ 4 = (r ^ 2) ^ 2.
Proof. intros. lra. Qed.

(** r² = 1 -> r = 1 \/ r = -1 *)
Lemma Rsqr_eq1 : forall r : R, r² = 1 -> r = 1 \/ r = -1.
Proof.
  intros. replace 1 with 1² in H; [|cbv;ring].
  apply Rsqr_eq_abs_0 in H. rewrite Rabs_R1 in H.
  bdestruct (r <? 0).
  - apply Rabs_left in H0. lra.
  - rewrite Rabs_right in H; auto. lra.
Qed.

(** x <= 0 -> y <= 0 -> x² = y² -> x = y *)
Lemma Rsqr_inj_neg : forall x y : R, x <= 0 -> y <= 0 -> x² = y² -> x = y.
Proof.
  intros. replace x with (- -x)%R; try lra.
  apply Rsqr_eq in H1; try lra.
Qed.

(** 0 <= r * r *)
Lemma Rsqr_ge0 : forall r, 0 <= r * r.
Proof. ra. Qed.
Hint Resolve Rsqr_ge0 : R.

(** r <> 0 -> r² <> 0 *)
Lemma Rsqr_neq0_if : forall r, r <> 0 -> r² <> 0.
Proof. ra. Qed.
Hint Resolve Rsqr_neq0_if : R.


(* ======================================================================= *)
(** ** Additional properties *)

(** R0² = 0 *)
Lemma Rsqr_R0 : R0² = 0.
Proof. rewrite <- Rsqr_0. auto. Qed.
Hint Rewrite Rsqr_R0 : R.

(** (R1)² = 1 *)
Lemma Rsqr_R1 : (R1)² = 1.
Proof. ra. Qed.
Hint Rewrite Rsqr_R1 : R.

(* -------------------------------------------- *)
(** *** r1² + r2² *)

(** r1² + r2² = 0 -> r1 = 0 /\ r2 = 0 *)
Lemma Rplus2_sqr_eq0_imply : forall r1 r2, r1² + r2² = 0 -> r1 = 0 /\ r2 = 0.
Proof. ra. Qed.
Hint Resolve Rplus2_sqr_eq0_imply : R.

(** r1 = 0 /\ r2 = 0 -> r1² + r2² = 0 *)
Lemma Rplus2_sqr_eq0_if : forall r1 r2, r1 = 0 /\ r2 = 0 -> r1² + r2² = 0.
Proof. ra. Qed.
Hint Resolve Rplus2_sqr_eq0_if : R.

(** r1 = 0 /\ r2 = 0 <-> r1² + r2² = 0 *)
Lemma Rplus2_sqr_eq0 : forall r1 r2, r1 = 0 /\ r2 = 0 <-> r1² + r2² = 0.
Proof. ra. Qed.
(* Tips, "iff" lemmas is for manually rewriting, not for automation *)

(** r1² + r2² = 0 -> r1 = 0 *)
Lemma Rplus2_sqr_eq0_l : forall r1 r2, r1² + r2² = 0 -> r1 = 0.
Proof. ra.  Qed.
Hint Resolve Rplus2_sqr_eq0_l : R.

(** r1² + r2² = 0 -> r2 = 0 *)
Lemma Rplus2_sqr_eq0_r : forall r1 r2, r1² + r2² = 0 -> r2 = 0.
Proof. ra. Qed.
Hint Resolve Rplus2_sqr_eq0_r : R.

(** r1² + r2² <> 0 -> r1 <> 0 \/ r2 <> 0 *)
Lemma Rplus2_sqr_neq0_imply : forall r1 r2, r1² + r2² <> 0 -> r1 <> 0 \/ r2 <> 0.
Proof. intros. rewrite <- Rplus2_sqr_eq0 in H. tauto. Qed.
Hint Resolve Rplus2_sqr_neq0_imply : R.

(** r1 <> 0 \/ r2 <> 0 -> r1² + r2² <> 0 *)
Lemma Rplus2_sqr_neq0_if : forall r1 r2, r1 <> 0 \/ r2 <> 0 -> r1² + r2² <> 0.
Proof. intros. rewrite <- Rplus2_sqr_eq0. tauto. Qed.
Hint Resolve Rplus2_sqr_neq0_if : R.

(** r1 <> 0 \/ r2 <> 0 <-> r1² + r2² <> 0 *)
Lemma Rplus2_sqr_neq0 : forall r1 r2, r1² + r2² <> 0 <-> r1 <> 0 \/ r2 <> 0.
Proof. ra. Qed.

(** 0 < r1 -> 0 < r2 -> r1 < r2 -> r1² < r2² *)
Lemma Rsqr_mono_gt0 : forall r1 r2, 0 < r1 -> 0 < r2 -> r1 < r2 -> r1² < r2².
Proof. ra. Qed.


(* -------------------------------------------- *)
(** *** r1² + r2² + r3² *)

(** r1² + r2² + r3² = 0 <-> r1 = 0 /\ r2 = 0 /\ r3 = 0 *)
Lemma Rplus3_sqr_eq0 : forall r1 r2 r3 : R,
  r1² + r2² + r3² = 0 <-> r1 = 0 /\ r2 = 0 /\ r3 = 0.
Proof. ra. Qed.

(** r1² + r2² + r3² <> 0 <-> r1 <> 0 \/ r2 <> 0 \/ r3 <> 0 *)
Lemma Rplus3_sqr_neq0 : forall r1 r2 r3 : R,
  r1² + r2² + r3² <> 0 <-> r1 <> 0 \/ r2 <> 0 \/ r3 <> 0.
Proof. ra. Qed.

(* -------------------------------------------- *)
(** *** r1² + r2² + r3² + r4² *)

(** r1² + r2² + r3² + r4² = 0 <-> r1 = 0 /\ r2 = 0 /\ r3 = 0 /\ r4 = 0 *)
Lemma Rplus4_sqr_eq0 : forall r1 r2 r3 r4 : R,
  r1² + r2² + r3² + r4² = 0 <-> r1 = 0 /\ r2 = 0 /\ r3 = 0 /\ r4 = 0.
Proof. ra. Qed.

(** r1² + r2² + r3² + r4² <> 0 <-> r1 <> 0 \/ r2 <> 0 \/ r3 <> 0 \/ r4 <> 0 *)
Lemma Rplus4_sqr_neq0 : forall r1 r2 r3 r4 : R,
  r1² + r2² + r3² + r4² <> 0 <-> r1 <> 0 \/ r2 <> 0 \/ r3 <> 0 \/ r4 <> 0.
Proof. ra. Qed.


(* ======================================================================= *)
(** ** Extra automation *)

(* Ltac *)
(* Rsqr_eq_0           (* x² = 0 -> x = 0 *) *)
(*   Rsqr_inj            (* 0 <= x -> 0 <= y -> x² = y² -> x = y *) *)
