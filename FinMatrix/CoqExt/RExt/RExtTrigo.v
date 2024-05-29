(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Simplify the expressions about trigonometric function
  author    : ZhengPu Shi
  date      : 2021.05

  remark    :
 *)

Require Export RExtBase RExtSqr RExtBool.


(* ======================================================================= *)
(** ** Basic automation *)

#[export] Hint Rewrite
  (* sin,cos *)
  sin_0         (* sin 0 = 0 *)
  cos_0         (* cos 0 = 1 *)
  sin_PI        (* sin PI = 0 *)
  cos_PI        (* cos PI = -1 *)
  sin_PI2       (* sin (PI / 2) = 1 *)
  cos_PI2       (* cos (PI / 2) = 0 *)
  cos_neg       (* cos (- x) = cos x *)
  sin_neg       (* sin (- x) = - sin x *)
  sin2_cos2     (* (sin x)² + (cos x)² = 1 *)
  neg_sin       (* sin (x + PI) = - sin x *)
  neg_cos       (* cos (x + PI) = - cos x *)
  sin_PI_x      (* sin (PI - x) = sin x *)
  Rtrigo_facts.cos_pi_minus (* cos (PI - x) = - cos x *)
  cos_plus      (* cos (x + y) = cos x * cos y - sin x * sin y *)
  cos_minus     (* cos (x - y) = cos x * cos y + sin x * sin y *)
  sin_plus      (* sin (x + y) = sin x * cos y + cos x * sin y *)
  sin_minus     (* sin (x - y) = sin x * cos y - cos x * sin y *)
  sin2_cos2     (* (sin x)² + (cos x)² = 1 *)

  (* tan,ctan *)

  (* asin,acos,atan *)
  acos_0        (* acos 0 = PI/2 *)
  acos_1        (* acos 1 = 0 *)
  atan_0        (* atan 0 = 0 *)
  asin_opp      (* asin (-x) = - asin x *)
  acos_opp      (* acos (-x) = PI - acos x *)
  atan_opp      (* atan (-x) = - atan x *)
  : R.

(* atan_tan      (* - (PI/2) < x < PI/2 -> atan (tan x) = x *) *)
(* asin_sin      (* - (PI/2) < x < PI/2 -> asin (sin x) = x *) *)
(* acos_cos      (* 0 <= x <= PI -> acos (cos x) = x *) *)

#[export] Hint Resolve
  PI2_RGT_0      (* 0 < PI / 2 *)
  _PI2_RLT_0     (* - (PI / 2) < 0 *)
  : R.


(* ======================================================================= *)
(** ** Additional properties *)

(** *** About sin and cos *)

(** sin (r + PI) = - (cos r) *)
Lemma sin_plus_PI : forall r, sin (r + PI) = - (sin r).
Proof. ra. Qed.

(** cos (r + PI) = - (cos r) *)
Lemma cos_plus_PI : forall r, cos (r + PI) = - (cos r).
Proof. ra. Qed.

(** sin (r - PI) = - (sin r) *)
Lemma sin_sub_PI : forall r, sin (r - PI) = - (sin r).
Proof. ra. Qed.
#[export] Hint Rewrite sin_sub_PI : R.

(** cos (r - PI) = - (cos r) *)
Lemma cos_sub_PI : forall r, cos (r - PI) = - (cos r).
Proof. ra. Qed.
#[export] Hint Rewrite cos_sub_PI : R.

(**  sin (- (PI/2)) = -1 *)
Lemma sin_PI2_neg : sin (- (PI/2)) = -1.
Proof. ra. Qed.
#[export] Hint Rewrite sin_PI2_neg : R.

(** cos (- (PI/2)) = 0 *)
Lemma cos_PI2_neg : cos (- (PI/2)) = 0.
Proof. ra. Qed.
#[export] Hint Rewrite cos_PI2_neg : R.

(** (cos x)² + (sin x)² = 1 *)
Lemma cos2_sin2 : forall x : R, (cos x)² + (sin x)² = 1.
Proof. intros. rewrite Rplus_comm. ra. Qed.
#[export] Hint Rewrite cos2_sin2 : R.

(* Simplify equations such as:

   a * (sin x)² + a * (cos x)²
   (sin x)² * a + a * (cos x)²
   a * (sin x)² + (cos x)² * a
   (sin x)² * a + (cos x)² * a

   a * (cos x)² + a * (sin x)²
   (cos x)² * a + a * (sin x)²
   a * (cos x)² + (sin x)² * a
   (cos x)² * a + (sin x)² * a
 *)
Section x_sin2_x_cos2.
  Variable x a : R.
  Lemma x_sin2_plus_x_cos2 : a * (sin x)² + a * (cos x)² = a. rewrite sin2; ra. Qed.
  Lemma sin2_x_plus_x_cos2 : (sin x)² * a + a * (cos x)² = a. rewrite sin2; ra. Qed.
  Lemma x_sin2_plus_cos2_x : a * (sin x)² + (cos x)² * a = a. rewrite sin2; ra. Qed.
  Lemma sin2_x_plus_cos2_x : (sin x)² * a + (cos x)² * a = a. rewrite sin2; ra. Qed.

  Lemma x_cos2_plus_x_sin2 : a * (cos x)² + a * (sin x)² = a. rewrite cos2; ra. Qed.
  Lemma cos2_x_plus_x_sin2 : (cos x)² * a + a * (sin x)² = a. rewrite cos2; ra. Qed.
  Lemma x_cos2_plus_sin2_x : a * (cos x)² + (sin x)² * a = a. rewrite cos2; ra. Qed.
  Lemma cos2_x_plus_sin2_x : (cos x)² * a + (sin x)² * a = a. rewrite cos2; ra. Qed.
End x_sin2_x_cos2.
#[export] Hint Rewrite
  x_sin2_plus_x_cos2 sin2_x_plus_x_cos2 x_sin2_plus_cos2_x sin2_x_plus_cos2_x
  x_cos2_plus_x_sin2 cos2_x_plus_x_sin2 x_cos2_plus_sin2_x cos2_x_plus_sin2_x
  : R.

(** - PI / 2 < r < PI / 2 -> cos r <> 0 *)
Lemma cos_neg0 : forall r : R, - PI / 2 < r < PI / 2 -> cos r <> 0.
Proof. intros. assert (0 < cos r); ra. apply cos_gt_0; ra. Qed.


(** *** About atan *)

(** sin r * / cos r = tan r *)
Lemma Rtan_rw : forall r : R, sin r * / cos r = tan r.
Proof. auto. Qed.
#[export] Hint Rewrite Rtan_rw : R.

(* In the proof of atan2, we need to simplify the expression such as
   tan ((a * b) / (a * c)) *)

(** atan (k * a) (k * b) = atan a b *)
Lemma atan_ka_kb : forall a b k : R,
    b <> 0 -> k <> 0 -> atan ((k * a) / (k * b)) = atan (a/b).
Proof. intros. f_equal. field. ra. Qed.

(** atan (a * k) (b * k) = atan a b *)
Lemma atan_ak_bk : forall a b k : R,
    b <> 0 -> k <> 0 -> atan ((a * k) /(b * k)) = atan (a/b).
Proof. intros. f_equal. field. ra. Qed.

(** 0 < atan x < π/2 *)
Lemma atan_bound_gt0 : forall x, x > 0 -> 0 < atan x < PI/2.
Proof.
  intros. split.
  - rewrite <- atan_0. apply atan_increasing; ra.
  - pose proof (atan_bound x); ra.
Qed.

(** -π/2 < atan x < 0 *)
Lemma atan_bound_lt0 : forall x, x < 0 -> - PI / 2 < atan x < 0.
Proof.
  intros. split.
  - pose proof (atan_bound x); ra.
  - rewrite <- atan_0. apply atan_increasing; ra.
Qed.

(** 0 <= atan x < π/2 *)
Lemma atan_bound_ge0 : forall x, x >= 0 -> 0 <= atan x < PI/2.
Proof.
  intros. bdestruct (x =? 0); subst; ra.
  assert (x > 0); ra. pose proof (atan_bound_gt0 x H1); ra.
Qed.

(** -π/2 < atan x <= 0 *)
Lemma atan_bound_le0 : forall x, x <= 0 -> - PI / 2 < atan x <= 0.
Proof.
  intros. bdestruct (x =? 0); subst; ra.
  - assert (PI > 0); ra.
  - assert (x < 0); ra. pose proof (atan_bound_lt0 x H1); ra.
Qed.

