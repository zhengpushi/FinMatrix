(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Simplify the expressions about trigonometric function
  author    : Zhengpu Shi
  date      : 2021.05

  remark    :

  reference :
  1. https://en.wikipedia.org/wiki/Inverse_trigonometric_functions

 *)

Require Export RExtBase RExtPlus RExtMult RExtSqr RExtOpp RExtInv RExtSqrt RExtBool.


(* ======================================================================= *)
(** ** Basic automation *)

Hint Rewrite
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

Hint Resolve
  PI2_RGT_0      (* 0 < PI / 2 *)
  _PI2_RLT_0     (* - (PI / 2) < 0 *)
  : R.


(* ======================================================================= *)
(** ** Convert between degree and radian *)

Definition deg2rad (d : R) : R := d * (PI / 180).  (* 1 degree = 0.01745.. rad *)
Definition rad2deg (r : R) : R := r * (180 / PI).  (* 1 rad = 27.29578.. degree *)


(* ======================================================================= *)
(** ** Trigonometric functions about sin and cos *)

(** *** 和差公式 *)
Fact sin_add : forall x y, sin (x + y) = sin x * cos y + cos x * sin y. Admitted.
Fact sin_sub : forall x y, sin (x - y) = sin x * cos y - cos x * sin y. Admitted.
Fact cos_add : forall x y, cos (x + y) = cos x * cos y - sin x * sin y. Admitted.
Fact cos_sub : forall x y, cos (x - y) = cos x * cos y + sin x * sin y. Admitted.

(** *** 倍角公式 *)
Fact sin_2a : forall x, sin (2 * x) = 2 * sin x * cos x. Admitted.
Fact cos_2a : forall x, cos (2 * x) = (cos x)² - (sin x)². Admitted.
Fact cos_2a' : forall x, cos (2 * x) = 1 - 2 * (sin x)². Admitted.
Fact cos_2a'' : forall x, cos (2 * x) = 2 * (cos x)² - 1. Admitted.

(** *** 关于平方和的公式 *)
Fact sin2_eq : forall x, (sin x)² = 1 - (cos x)². Admitted.
Fact cos2_eq : forall x, (cos x)² = 1 - (sin x)². Admitted.
Fact sin2_add_cos2 : forall x, (sin x)² + (cos x)² = 1. Admitted.

(** *** 积化和差 *)
Fact sin_cos : forall x y, sin x * cos y = (1/2) * (sin (x + y) + sin (x - y)). Admitted.
Fact cos_cos : forall x y, cos x * cos y = (1/2) * (cos (x + y) + cos (x - y)). Admitted.
Fact sin_sin : forall x y, sin x * sin y = (1/2) * (cos (x - y) - cos (x + y)). Admitted.

(** *** 和差化积 *)
Fact sin_add_sin : forall x y, sin x + sin y = 2 * sin ((x+y)/2) * cos ((x-y)/2).
Admitted.
Fact sin_sub_sin : forall x y, sin x - sin y = 2 * sin ((x-y)/2) * cos ((x+y)/2).
Admitted.
Fact cos_add_cos : forall x y, cos x + cos y = 2 * cos ((x+y)/2) * cos ((x-y)/2).
Admitted.
Fact cos_sub_cos : forall x y, cos x - cos y = -2 * sin ((x+y)/2) * sin ((x-y)/2).
Admitted.

(** *** 诱导公式 *)

(** sin (r + PI) = - (cos r) *)
Lemma sin_plus_PI : forall r, sin (r + PI) = - (sin r).
Proof. ra. Qed.

(** cos (r + PI) = - (cos r) *)
Lemma cos_plus_PI : forall r, cos (r + PI) = - (cos r).
Proof. ra. Qed.

(** sin (r - PI) = - (sin r) *)
Lemma sin_sub_PI : forall r, sin (r - PI) = - (sin r).
Proof. ra. Qed.
Hint Rewrite sin_sub_PI : R.

(** cos (r - PI) = - (cos r) *)
Lemma cos_sub_PI : forall r, cos (r - PI) = - (cos r).
Proof. ra. Qed.
Hint Rewrite cos_sub_PI : R.

(**  sin (- (PI/2)) = -1 *)
Lemma sin_PI2_neg : sin (- (PI/2)) = -1.
Proof. ra. Qed.
Hint Rewrite sin_PI2_neg : R.

(** cos (- (PI/2)) = 0 *)
Lemma cos_PI2_neg : cos (- (PI/2)) = 0.
Proof. ra. Qed.
Hint Rewrite cos_PI2_neg : R.

(** (cos x)² + (sin x)² = 1 *)
Lemma cos2_sin2 : forall x : R, (cos x)² + (sin x)² = 1.
Proof. intros. rewrite Rplus_comm. ra. Qed.
Hint Rewrite cos2_sin2 : R.

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
Hint Rewrite
  x_sin2_plus_x_cos2 sin2_x_plus_x_cos2 x_sin2_plus_cos2_x sin2_x_plus_cos2_x
  x_cos2_plus_x_sin2 cos2_x_plus_x_sin2 x_cos2_plus_sin2_x cos2_x_plus_sin2_x
  : R.

(** - PI / 2 < r -> r < PI / 2 -> cos r <> 0 *)
Lemma cos_neg0 : forall r : R, - PI / 2 < r -> r < PI / 2 -> cos r <> 0.
Proof. intros. assert (0 < cos r); ra. apply cos_gt_0; ra. Qed.
Hint Resolve cos_neg0 : R.

(** *** 特殊三角函数值 *)

Fact sin_0 : sin 0 = 0. Proof. apply sin_0. Qed.
Fact sin_R0 : sin R0 = 0. Proof. apply sin_0. Qed.
Fact sin_PI6 : sin (PI / 6) = 1 / 2. Admitted.
Fact sin_PI4 : sin (PI / 4) = (sqrt 2) / 2. Admitted.
Fact sin_PI3 : sin (PI / 3) = (sqrt 3) / 2. Admitted.
Fact sin_PI2 : sin (PI / 2) = 1. Admitted.
Fact sin_2PI3 : sin (2 * PI / 3) = (sqrt 3) / 2. Admitted.
Fact sin_3PI4 : sin (3 * PI / 4) = (sqrt 2) / 2. Admitted.
Fact sin_5PI6 : sin (5 * PI / 6) = 1 / 2. Admitted.
Fact sin_PI : sin PI = 0. Admitted.
Fact sin_3PI2 : sin (3 * PI / 2) = -1. Admitted.
Fact sin_2PI : sin (2 * PI) = 0. Admitted.

Hint Rewrite
  sin_0 sin_R0 sin_PI6 sin_PI4 sin_PI3 sin_PI2 sin_2PI3 sin_3PI4 sin_5PI6
  sin_PI sin_3PI2 sin_2PI
  : R.

Fact cos_0 : cos 0 = 1. Proof. apply cos_0. Qed.
Fact cos_R0 : cos R0 = 1. Proof. apply cos_0. Qed.
Fact cos_PI6 : cos (PI / 6) = (sqrt 3) / 2. Admitted.
Fact cos_PI4 : cos (PI / 4) = (sqrt 2) / 2. Admitted.
Fact cos_PI3 : cos (PI / 3) = 1 / 2. Admitted.
Fact cos_PI2 : cos (PI / 2) = 0. Admitted.
Fact cos_2PI3 : cos (2 * PI / 3) = - 1 / 2. Admitted.
Fact cos_3PI4 : cos (3 * PI / 4) = - (sqrt 2) / 2. Admitted.
Fact cos_5PI6 : cos (5 * PI / 6) = - (sqrt 3) / 2. Admitted.
Fact cos_PI : cos PI = -1. Admitted.
Fact cos_3PI2 : cos (3 * PI / 2) = 0. Admitted.
Fact cos_2PI : cos (2 * PI) = 1. Admitted.

Hint Rewrite
  cos_0 cos_R0 cos_PI6 cos_PI4 cos_PI3 cos_PI2 cos_2PI3 cos_3PI4 cos_5PI6
  cos_PI cos_3PI2 cos_2PI
  : R.

(** *** 诱导公式 *)
Fact sin_PI2_sub : forall x, sin (PI/2 - x) = cos x. Admitted.
Fact sin_PI2_add : forall x, sin (PI/2 + x) = cos x. Admitted.
Fact sin_PI_sub : forall x, sin (PI - x) = sin x. Admitted.
Fact sin_PI_add : forall x, sin (PI + x) = - sin x. Admitted.
Fact sin_3PI2_sub : forall x, sin (3 * PI / 2 - x) = - cos x. Admitted.
Fact sin_3PI2_add : forall x, sin (3 * PI / 2 + x) = - cos x. Admitted.
Fact sin_2PI_add : forall x, sin (2 * PI + x) = sin x. Admitted.

Fact cos_PI2_sub : forall x, cos (PI/2 - x) = sin x. Admitted.
Fact cos_PI2_add : forall x, cos (PI/2 + x) = - sin x. Admitted.
Fact cos_PI_sub : forall x, cos (PI - x) = - cos x. Admitted.
Fact cos_PI_add : forall x, cos (PI + x) = - cos x. Admitted.
Fact cos_3PI2_sub : forall x, cos (3 * PI / 2 - x) = - sin x. Admitted.
Fact cos_3PI2_add : forall x, cos (3 * PI / 2 + x) = sin x. Admitted.
Fact cos_2PI_add : forall x, cos (2 * PI + x) = cos x. Admitted.

(** *** 周期性 *)

(** Periodicity of sin over Z type. Note std-lib support it over nat type:
    sin (x + 2 * IZR k * PI) = sin x *)
Lemma sin_period_Z : forall (x:R) (k:Z), sin (x + 2 * IZR k * PI) = sin x.
Proof.
  intros x k. induction k.
  - (* use "sin_period" *)
    replace 0 with (INR 0); auto. apply sin_period.
  - (* use "sin_period" *)
    replace (Z.pos p) with (Z.of_nat (Pos.to_nat p)).
    + rewrite <- INR_IZR_INZ. apply sin_period.
    + apply positive_nat_Z.
  - replace (Z.neg p) with (- (Z.of_nat (Pos.to_nat p)))%Z.
    + rewrite Ropp_Ropp_IZR.
      rewrite <- INR_IZR_INZ.
      rewrite <- Ropp_mult_distr_r.
      rewrite Ropp_mult_distr_l_reverse.
      induction (Pos.to_nat p).
      * replace (x + - (2 * INR 0 * PI)) with x; auto.
        replace (INR 0) with 0; auto; ring.
      * replace (x + - (2 * INR (S n) * PI)) with
          (x - (2 * INR n * PI) - 2 * PI).
        { rewrite sin_minus; rewrite !sin_2PI,!cos_2PI. ring_simplify; auto. }
        { rewrite S_INR. ring. }
    + rewrite positive_nat_Z. auto.
Qed.

(** Periodicity of cos over Z type. Note std-lib support it over nat type:
    cos (x + 2 * IZR k * PI) = cos x *)
Lemma cos_period_Z : forall (x:R) (k:Z), cos (x + 2 * IZR k * PI) = cos x.
Proof.
  intros x k. induction k.
  - (* use "cos_period" *)
    replace 0 with (INR 0); auto. apply cos_period.
  - (* use "cos_period" *)
    replace (Z.pos p) with (Z.of_nat (Pos.to_nat p)).
    + rewrite <- INR_IZR_INZ. apply cos_period.
    + apply positive_nat_Z.
  - (* convert "Zneg" to "opp (Z.of_nat)", then induction *)
    replace (Z.neg p) with (- (Z.of_nat (Pos.to_nat p)))%Z.
    + rewrite Ropp_Ropp_IZR.
      rewrite <- INR_IZR_INZ.
      rewrite <- Ropp_mult_distr_r.
      rewrite Ropp_mult_distr_l_reverse.
      induction (Pos.to_nat p).
      * replace (x + - (2 * INR 0 * PI)) with x; auto.
        replace (INR 0) with 0; auto; ring.
      * replace (x + - (2 * INR (S n) * PI)) with
          (x - (2 * INR n * PI) - 2 * PI).
        { rewrite cos_minus. rewrite !sin_2PI,!cos_2PI. ring_simplify; auto. }
        { rewrite S_INR. ring. }
    + rewrite positive_nat_Z. auto.
Qed.

(** sin x = 1 -> x = 2kπ + π/2 *)
Lemma sin_1_period : forall (x : R) (k : nat), sin x = 1 -> x = 2 * INR k * PI + PI/2.
Admitted.

(** cos x = 1 -> x = 2kπ *)
Lemma cos_1_period : forall (x : R) (k : Z), cos x = 1 -> x = 2 * IZR k * PI.
Admitted.

(** cos x = -1 -> x = 2kπ + π *)
Lemma cos_neg1_period : forall (x : R) (k : Z), cos x = -1 -> x = 2 * IZR k * PI + PI.
Admitted.

(** cos x = 0 -> x = kπ + π/2 *)
Lemma cos_0_period : forall (x : R) (k : Z), cos x = 0 -> x = IZR k * PI + PI/2.
Admitted.

(** -π/2 <= x -> x <= π/2 -> sin x = 1 -> x = π/2 *)
Lemma sin_eq1_imply : forall (x : R), -PI/2 <= x -> x <= PI/2 -> sin x = 1 -> x = PI/2.
Proof. intros. apply (sin_1_period x 0) in H1. ra. Qed.


(* ======================================================================= *)
(** ** Trigonometric functions about tan and cot *)

(** *** 缺失了的函数 *)
Definition cot (x : R) : R := / (tan x).

(** *** 基本关系 *)
Fact tan_cot : forall x, (tan x) * (cot x) = 1. Admitted.
Fact tan_eq : forall x, tan x = (sin x) / (cos x). Admitted.
Fact cot_eq : forall x, cot x = (cos x) / (sin x). Admitted.

(** *** 和差公式 *)
Fact tan_add : forall x y, tan (x + y) = (tan x + tan y) / (1 - tan x * tan y). Admitted.
Fact tan_sub : forall x y, tan (x - y) = (tan x - tan y) / (1 + tan x * tan y). Admitted.
Fact cot_add : forall x y, cot (x + y) = (cot x * cot y - 1) / (cot x + cot y). Admitted.
Fact cot_sub : forall x y, cot (x - y) = (cot x * cot y + 1) / (cot x - cot y). Admitted.

(** *** 倍角公式 *)
Fact tan_2a : forall x, tan (2 * x) = (2 * tan x) / (1 - (tan x)²). Admitted.
Fact cot_2a : forall x, cot (2 * x) = ((cot x)² - 1) / (2 * cot x). Admitted.

(** *** 特殊三角函数值 *)
Fact tan_0 : tan 0 = 1. Admitted.
Fact tan_PI6 : tan (PI / 6) = (sqrt 3) / 3. Admitted.
Fact tan_PI4 : tan (PI / 4) = 1. Admitted.
Fact tan_PI3 : tan (PI / 3) = sqrt 3. Admitted.
(* Fact tan_PI2 : tan (PI / 2) = inf. Admitted. *)
Fact tan_2PI3 : tan (2 * PI / 3) = - (sqrt 3). Admitted.
Fact tan_3PI4 : tan (3 * PI / 4) = - 1. Admitted.
Fact tan_5PI6 : tan (5 * PI / 6) = - (sqrt 3) / 3. Admitted.
Fact tan_PI : tan PI = 0. Admitted.
(* Fact tan_3PI2 : tan (3 * PI / 2) = inf. Admitted. *)
Fact tan_2PI : tan (2 * PI) = 0. Admitted.

(* Fact cot_0 : cot 0 = inf. Admitted. *)
Fact cot_PI6 : cot (PI / 6) = (sqrt 3). Admitted.
Fact cot_PI4 : cot (PI / 4) = 1. Admitted.
Fact cot_PI3 : cot (PI / 3) = (sqrt 3) / 3. Admitted.
Fact cot_PI2 : cot (PI / 2) = 0. Admitted.
Fact cot_2PI3 : cot (2 * PI / 3) = - (sqrt 3) / 3. Admitted.
Fact cot_3PI4 : cot (3 * PI / 4) = - 1. Admitted.
Fact cot_5PI6 : cot (5 * PI / 6) = - (sqrt 3). Admitted.
(* Fact cot_PI : cot PI = inf. Admitted. *)
Fact cot_3PI2 : cot (3 * PI / 2) = 0. Admitted.
(* Fact cot_2PI : cot (2 * PI) = inf. Admitted. *)

(** *** 诱导公式 *)
Fact tan_PI2_add : forall x, tan (PI/2 + x) = - cot x. Admitted.
Fact tan_PI2_sub : forall x, tan (PI/2 - x) = cot x. Admitted.
Fact tan_PI_add : forall x, tan (PI + x) = tan x. Admitted.
Fact tan_PI_sub : forall x, tan (PI - x) = - tan x. Admitted.
Fact tan_add_PI : forall x, tan (x + PI) = tan x. Admitted.
Fact tan_sub_PI : forall x, tan (x - PI) = tan x. Admitted.
Fact tan_3PI2_add : forall x, tan (3 * PI / 2 + x) = - cot x. Admitted.
Fact tan_3PI2_sub : forall x, tan (3 * PI / 2 - x) = cot x. Admitted.
Fact tan_2PI_add : forall x, tan (2 * PI + x) = tan x. Admitted.

Hint Rewrite
  tan_PI2_sub
  tan_PI2_add
  tan_PI_add
  tan_PI_sub
  tan_add_PI
  tan_sub_PI
  tan_3PI2_add
  tan_3PI2_sub
  tan_2PI_add
  : R.

Fact cot_PI2_add : forall x, cot (PI/2 + x) = - tan x. Admitted.
Fact cot_PI2_sub : forall x, cot (PI/2 - x) = tan x. Admitted.
Fact cot_PI_add : forall x, cot (PI + x) = cot x. Admitted.
Fact cot_PI_sub : forall x, cot (PI - x) = - cot x. Admitted.
Fact cot_3PI2_add : forall x, cot (3 * PI / 2 + x) = - tan x. Admitted.
Fact cot_3PI2_sub : forall x, cot (3 * PI / 2 - x) = tan x. Admitted.
Fact cot_2PI_add : forall x, cot (2 * PI + x) = cot x. Admitted.

Hint Rewrite
  cot_PI2_sub
  cot_PI2_add
  cot_PI_add
  cot_PI_sub
  cot_3PI2_add
  cot_3PI2_sub
  cot_2PI_add
  : R.


(* ======================================================================= *)
(** ** Trigonometric functions about asin and acos *)


(* ======================================================================= *)
(** ** Trigonometric functions about atan and acot *)

(** sin r / cos r = tan r *)
Lemma tan_rw : forall r : R, sin r / cos r = tan r.
Proof. auto. Qed.
Hint Rewrite tan_rw : R.

(** *** 缺失了的函数 *)
Parameter acot : R -> R.

(** *** 诱导公式 *)

(** 0 < a -> 0 < b -> sin (atan (a / b)) = a / sqrt (a*a + b*b) *)
Lemma sin_atan : forall a b : R,
    0 < a -> 0 < b -> sin (atan (a / b)) = a / (sqrt (a * a + b * b)).
Proof.
  intros. rewrite sin_atan. ra.
  replace (1 + a² / b²) with ((a² + b²) * (/ b²)) by ra.
  rewrite sqrt_mult_alt; ra.
  replace (| b|) with b; ra.
Qed.

(** 0 < a -> 0 < b -> cos (atan (a / b)) = b / sqrt (a*a + b*b) *)
Lemma cos_atan : forall a b : R,
    0 < a -> 0 < b -> cos (atan (a / b)) = b / (sqrt (a * a + b * b)).
Proof.
  intros. rewrite cos_atan. ra.
  replace (1 + a² / b²) with ((a² + b²) * (/ b²)) by ra.
  rewrite sqrt_mult_alt; ra.
  replace (| b|) with b; ra.
Qed.

(* ======================================================================= *)
(** ** Trigonometric functions about sec and csc *)

Definition sec (x : R) : R := / (cos x).
Definition csc (x : R) : R := / (sin x).

Fact sin_csc : forall x, (sin x) * (csc x) = 1. Admitted.
Fact cos_sec : forall x, (cos x) * (sec x) = 1. Admitted.

(** *** 关于平方和的公式 *)
Fact sec2_eq : forall x, (sec x)² = 1 - (tan x)². Admitted.
Fact csc2_eq : forall x, (csc x)² = 1 - (cot x)². Admitted.
Fact sec2_sub_tan2 : forall x, (sec x)² - (tan x)² = 1. Admitted.
Fact csc2_sub_cot2 : forall x, (csc x)² - (cot x)² = 1. Admitted.

(* ======================================================================= *)
(** ** Additional properties for asin, acos, atan, and acot *)

(* Fact asin_0 : asin 0 = 0. Admitted. *)
Fact asin_1_2 : asin (1 / 2) = PI / 6. Admitted.
Fact asin_sqrt2_2 : asin ((sqrt 2) / 2) = PI / 4. Admitted.
Fact asin_sqrt3_2 : asin ((sqrt 3) / 2) = PI / 3. Admitted.
(* Fact asin_1 : asin 1 = PI / 2. Admitted. *)


(* Fact acos_0 : acos 0 = (PI / 2). Admitted. *)
Fact acos_1_2 : acos (1 / 2) = PI / 3. Admitted.
Fact acos_sqrt2_2 : acos ((sqrt 2) / 2) = PI / 4. Admitted.
Fact acos_sqrt3_2 : acos ((sqrt 3) / 2) = PI / 2. Admitted.
(* Fact acos_1 : acos 1 = 0. Admitted. *)
Fact acos_neg1 : acos (-1) = PI. Admitted.
Hint Rewrite
  acos_neg1
  : R.

(** acos is injective in its domain *)
Lemma acos_inj : forall x1 x2 : R,
    -1 <= x1 <= 1 -> -1 <= x2 <= 1 -> acos x1 = acos x2 -> x1 = x2.
Proof.
  intros. rewrite <- cos_acos; auto.
  rewrite <- H1. rewrite cos_acos; auto.
Qed.


(* Fact atan_0 : atan 0 = 0. Admitted. *)
Fact atan_sqrt3_3 : atan ((sqrt 3) / 3) = PI / 6. Admitted.
(* Fact atan_1 : atan 1 = PI. Admitted. *)
Fact atan_sqrt3 : atan (sqrt 3) = PI / 3. Admitted.

(* (* In the proof of atan2, we need to simplify the expression such as *)
(*    atan ((a * b) / (a * c)) *) *)
(* Section atan_ab_ac. *)

(*   (** atan ((k * a) / (k * b)) = atan (a / b) *) *)
(*   Lemma atan_ka_kb : forall a b k : R, *)
(*       b <> 0 -> k <> 0 -> atan ((k * a) / (k * b)) = atan (a/b). *)
(*   Proof. intros. f_equal. field. ra. Qed. *)

(*   (** atan ((a * k) / (b * k)) = atan (a / b) *) *)
(*   Lemma atan_ak_bk : forall a b k : R, *)
(*       b <> 0 -> k <> 0 -> atan ((a * k) / (b * k)) = atan (a/b). *)
(*   Proof. intros. f_equal. field. ra. Qed. *)
(* End atan_ab_ac. *)

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
  assert (x < 0); ra. pose proof (atan_bound_lt0 x H1); ra.
Qed.

(* x < 0 -> acos x = atan ((sqrt (1-x²) / x) + PI *)
Lemma acos_atan_neg: forall x : R,
    x < 0 -> acos x = atan (sqrt (1 - x²) / x) + PI.
Proof.
  intros. replace x with (- (-x))%R; ra.
  ring_simplify.
  pose proof (acos_atan (-x)). ra.
Qed.


Fact acot_0 : acot 0 = PI / 2. Admitted.
Fact acot_sqrt3_3 : acot ((sqrt 3) / 3) = PI / 6. Admitted.
Fact acot_1 : acot 1 = PI. Admitted.
Fact acot_sqrt3 : acot (sqrt 3) = PI / 3. Admitted.

