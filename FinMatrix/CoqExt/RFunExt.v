(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Extension of real functions
  author    : ZhengPu Shi
  date      : 2023.03
  
  reference :
  1. Lecture from Prof. Chen (my supervisor)

  remark    :

 *)

Require Export RExt.
Require Export FuncExt.
Open Scope R_scope.
Open Scope Rfun_scope.


(* ######################################################################### *)
(** * Basic real functions *)

(** 取整函数 *)
(* Check R2Z_floor. *)
(* Check R2Z_ceiling. *)

(* ======================================================================= *)
(** ** Sign function *)
Definition sign : R -> R :=
  fun x => if x >? 0 then 1 else (if x =? 0 then 0 else -1).

(** x = 0 -> sign x = 0 *)
Lemma sign_eq0 : forall x, x = 0 -> sign x = 0.
Proof.
  intros. unfold sign. bdestruct (0 <? x); try lra. bdestruct (x =? 0); try lra.
Qed.

(** x > 0 -> sign x = 1 *)
Lemma sign_gt0 : forall x, x > 0 -> sign x = 1.
Proof. intros. unfold sign. bdestruct (x >? 0); auto. lra. Qed.

(** x < 0 -> sign x = - 1 *)
Lemma sign_lt0 : forall x, x < 0 -> sign x = -1.
Proof.
  intros. unfold sign. bdestruct (x >? 0); try lra. bdestruct (x =? 0); try lra.
Qed.

(** (sign x) * x = |x| *)
Lemma sign_mul_eq_abs : forall x, ((sign x) * x)%R = Rabs x.
Proof.
  intros. unfold sign. destruct (Rltb_reflect 0 x).
  + rewrite Rabs_right; lra.
  + rewrite Rabs_left1; try lra. destruct (Reqb_reflect x 0); try lra.
Qed.

(** (sign x) * |x| = x *)
Lemma sign_mul_abs_eq : forall x, ((sign x) * (Rabs x))%R = x.
Proof.
  intros. unfold sign. destruct (Rltb_reflect 0 x).
  + rewrite Rabs_right; lra.
  + rewrite Rabs_left1; try lra. destruct (Reqb_reflect x 0); try lra.
Qed.

(* ======================================================================= *)
(** ** Real arithmetic functions *)

(* Coq.Reals.Ranalysis1.plus_fct
   Rfun_scope, Delimiting key is F
   "x / y" := (div_fct x y)
   "x - y" := (minus_fct x y)
   "x + y" := (plus_fct x y)
   "x * y" := (mult_fct x y)
   "/ x" := (inv_fct x)
   "- x" := (opp_fct x) *)

Notation faddR := plus_fct.
Notation foppR := opp_fct.
(* Notation fsubR := minus_fct. *)
Notation fsubR f g := (faddR f (foppR g)).
Notation fmulR := mult_fct.
Notation finvR := inv_fct.
(* Notation fdivR := div_fct. *)
Notation fdivR f g := (fmulR f (finvR g)).

Infix "-" := fsubR : Rfun_scope.
Infix "/" := fdivR : Rfun_scope.

Lemma faddR_ok : forall (u v : R -> R) (x : R), (u + v) x = (u x + v x)%R. auto. Qed.
Lemma foppR_ok : forall (v : R -> R) (x : R), (- v) x = (- v x)%R. auto. Qed.
Lemma fsubR_ok : forall (u v : R -> R) (x : R), (u - v) x = (u x - v x)%R. auto. Qed.
Lemma fmulR_ok : forall (u v : R -> R) (x : R), (u * v) x = (u x * v x)%R. auto. Qed.
Lemma finvR_ok : forall (v : R -> R) (x : R), (/ v) x = (/ v x)%R. auto. Qed.
Lemma fdivR_ok : forall (u v : R -> R) (x : R), (u / v) x = (u x / v x)%R. auto. Qed.

(* ======================================================================= *)
(** ** Real constant functions *)
Definition fcnstR (C : R) : R -> R := fun _ => C.
Definition fzeroR : R -> R := fcnstR R0.
Definition foneR : R -> R := fcnstR R1.
Definition fidR : R -> R := fun x => x.
Notation "0" := fzeroR : Rfun_scope.
Notation "1" := foneR : Rfun_scope.

Hint Unfold
  faddR foppR fmulR finvR
  fcnstR fzeroR foneR fidR : Rfun.

Lemma faddR_0_l : forall f, 0 + f = f.
Proof. intros. apply feq_iff; intros; autounfold with Rfun; ring. Qed.

Lemma faddR_0_r : forall f, f + 0 = f.
Proof. intros. apply feq_iff; intros; autounfold with Rfun; ring. Qed.

Lemma faddR_opp_l : forall f, - f + f = 0.
Proof. intros. apply feq_iff; intros; autounfold with Rfun; ring. Qed.

Lemma faddR_opp_r : forall f, f + - f = 0.
Proof. intros. apply feq_iff; intros; autounfold with Rfun; ring. Qed.

Lemma fmulR_1_l : forall f, 1 * f = f.
Proof. intros. apply feq_iff; intros; autounfold with Rfun; ring. Qed.

Lemma fmulR_1_r : forall f, f * 1 = f.
Proof. intros. apply feq_iff; intros; autounfold with Rfun; ring. Qed.

Lemma fmulR_inv_l : forall f, (forall x, f x <> 0)%R -> / f * f = 1.
Proof. intros. apply feq_iff; intros. autounfold with Rfun. field. auto. Qed.

Lemma fmulR_inv_r : forall f, (forall x, f x <> 0)%R -> f * / f = 1.
Proof. intros. apply feq_iff; intros. autounfold with Rfun. field. auto. Qed.


(* ======================================================================= *)
(** ** Scalar multiplication of real function *)

Definition fcmul (c : R) (f : R -> R) := fun x => (c * f x)%R.
Infix "\.*" := fcmul : Rfun_scope.

Lemma fcmul_ok : forall (c : R) (u : R -> R) (x : R), (c \.* u) x = (c * u x)%R.
Proof. auto. Qed.

(** Properties for real function scalar multiplication *)
Lemma fcmul_assoc1 : forall (c d : R) (u : R -> R), c \.* (d \.* u) = (c * d) \.* u.
Proof. intros. apply feq_iff; intros. rewrite !fcmul_ok. ring. Qed.

Lemma fcmul_assoc2 : forall (c : R) (u v : R -> R), c \.* (u * v) = (c \.* u) * v.
Proof.
  intros. apply feq_iff; intros. rewrite ?fmulR_ok, ?fcmul_ok, ?fmulR_ok. ring.
Qed.

(** Multiply with a natural number, i.e., sum the function by n times:
    fnmul f 0 := fun x => 0
    fnmul f 1 := f
    fnmul f 2 := f + f, i.e., fun x => f x + f x
    ...
    fnmul f (S n) := fun x => f x + (fnmul f n) *)
Fixpoint fnmul (n : nat) (f : R -> R) : R -> R :=
  match n with
  | O => fun x => 0%R
  | S O => f
  | S n' => faddR f (fnmul n' f)
  end.


(* ######################################################################### *)
(** * Algebraic structures *)

(** equality is equivalence relation: Equivalence (@eq (R -> R)) *)
Hint Resolve eq_equivalence : Rfun.

(** operations are well-defined. Eg: Proper (eq ==> eq ==> eq) faddR *)

Lemma faddR_wd : Proper (eq ==> eq ==> eq) faddR.
Proof. simp_proper. intros; subst; auto. Qed.

Lemma foppR_wd : Proper (eq ==> eq) foppR.
Proof. simp_proper. intros; subst; auto. Qed.

Lemma fmulR_wd : Proper (eq ==> eq ==> eq) fmulR.
Proof. simp_proper. intros; subst; auto. Qed.

Lemma finvR_wd : Proper (eq ==> eq) finvR.
Proof. simp_proper. intros; subst; auto. Qed.

Hint Resolve
  faddR_wd foppR_wd
  fmulR_wd finvR_wd
  : Rfun.

(** Associative *)

#[export] Instance faddR_Assoc : Associative faddR.
Proof. constructor; intros. autounfold with Rfun; apply feq_iff; intros; ring. Qed.

#[export] Instance fmulR_Assoc : Associative fmulR.
Proof. constructor; intros. autounfold with Rfun; apply feq_iff; intros; ring. Qed.

Hint Resolve
  faddR_Assoc
  fmulR_Assoc
  : Rfun.

(** Commutative *)

#[export] Instance faddR_Comm : Commutative faddR.
Proof. constructor; intros. autounfold with Rfun; apply feq_iff; intros; ring. Qed.

#[export] Instance fmulR_Comm : Commutative fmulR.
Proof. constructor; intros. autounfold with Rfun; apply feq_iff; intros; ring. Qed.

Hint Resolve
  faddR_Comm
  fmulR_Comm
  : Rfun.

(** Identity Left/Right *)
#[export] Instance faddR_IdL : IdentityLeft faddR 0.
Proof. constructor; intros. autounfold with Rfun; apply feq_iff; intros; ring. Qed.

#[export] Instance faddR_IdR : IdentityRight faddR 0.
Proof. constructor; intros. autounfold with Rfun; apply feq_iff; intros; ring. Qed.

#[export] Instance fmulR_IdL : IdentityLeft fmulR 1.
Proof. constructor; intros. autounfold with Rfun; apply feq_iff; intros; ring. Qed.

#[export] Instance fmulR_IdR : IdentityRight fmulR 1.
Proof. constructor; intros. autounfold with Rfun; apply feq_iff; intros; ring. Qed.

Hint Resolve
  faddR_IdL faddR_IdR
  fmulR_IdL fmulR_IdR
  : Rfun.

(** Inverse Left/Right *)

#[export] Instance faddR_InvL : InverseLeft faddR 0 foppR.
Proof. constructor; intros. autounfold with Rfun; apply feq_iff; intros; ring. Qed.

#[export] Instance faddR_InvR : InverseRight faddR 0 foppR.
Proof. constructor; intros. autounfold with Rfun; apply feq_iff; intros; ring. Qed.

Hint Resolve faddR_InvL faddR_InvR : Rfun.

(** Distributive *)

#[export] Instance fmulR_add_DistrL : DistrLeft faddR fmulR.
Proof. constructor; intros. autounfold with Rfun; apply feq_iff; intros; ring. Qed.

#[export] Instance fmulR_add_DistrR : DistrRight faddR fmulR.
Proof. constructor; intros. autounfold with Rfun; apply feq_iff; intros; ring. Qed.

Hint Resolve
  fmulR_add_DistrL
  fmulR_add_DistrR
  : Rfun.

(** Semigroup *)

#[export] Instance faddR_SGroup : SGroup faddR.
Proof. constructor; auto with Rfun. Qed.

#[export] Instance fmulR_SGroup : SGroup fmulR.
Proof. constructor; auto with Rfun. Qed.

Hint Resolve
  faddR_SGroup
  fmulR_SGroup
  : Rfun.

(** Abelian semigroup *)

#[export] Instance faddR_ASGroup : ASGroup faddR.
Proof. constructor; auto with Rfun. Qed.

#[export] Instance fmulR_ASGroup : ASGroup fmulR.
Proof. constructor; auto with Rfun. Qed.

Hint Resolve
  faddR_ASGroup
  fmulR_ASGroup
  : Rfun.

Goal forall x1 x2 y1 y2 a b c, x1 + a + b + c + x2 = y1 + c + (b + a) + y2.
Proof. intros. pose proof faddR_ASGroup. asgroup. Abort.

(** Monoid *)
  
#[export] Instance faddR_Monoid : Monoid faddR 0.
Proof. constructor; auto with Rfun. Qed.

#[export] Instance fmulR_Monoid : Monoid fmulR 1.
Proof. constructor; auto with Rfun. Qed.

Hint Resolve
  faddR_Monoid
  fmulR_Monoid
  : Rfun.

(** Abelian monoid *)
  
#[export] Instance faddR_AMonoid : AMonoid faddR 0.
Proof. constructor; auto with Rfun. Qed.
  
#[export] Instance fmulR_AMonoid : AMonoid fmulR 1.
Proof. constructor; auto with Rfun. Qed.

Hint Resolve faddR_AMonoid fmulR_AMonoid : Rfun.

(** Group *)

#[export] Instance faddR_Group : Group faddR 0 foppR.
Proof. constructor; auto with Rfun. Qed.

Hint Resolve faddR_Group : Rfun.

(** AGroup *)

#[export] Instance faddR_AGroup : AGroup faddR 0 foppR.
Proof. constructor; auto with Rfun. Qed.

Hint Resolve faddR_AGroup : Rfun.

(** Ring *)

#[export] Instance Rfun_Ring : Ring faddR 0 foppR fmulR 1.
Proof. constructor; auto with Rfun. Qed.

Hint Resolve Rfun_Ring : Rfun.

(** ARing *)

#[export] Instance Rfun_ARing : ARing faddR 0 foppR fmulR 1.
Proof. constructor; auto with Rfun. Qed.

Hint Resolve Rfun_ARing : Rfun.

Section test.
  Add Ring ring_inst : (make_ring_theory Rfun_ARing).

  Goal forall u v w : R -> R, u - v * (u - w) = w * v - u * v + u.
  Proof. intros. ring. Qed.
End test.

(** Field *)

#[export] Instance Rfun_Field : Field faddR 0 foppR fmulR 1 finvR.
Proof.
  constructor; auto with Rfun.
  2:{ intro. cbv in H.
      rewrite fun_eq_iff_forall_eq in H. specialize (H R0). lra. }
  1:{ intros. apply fmulR_inv_l.
      cbv in H.
      (* tips, THIS IS NOT PROVABLE. WE KNOW "exist", BUT NEED "forall"
         f : R -> R,
         f <> (fun _ : R => R0)
         ---------------------------
         forall x : R, f x <> R0
       *)
Abort.


(* ######################################################################### *)
(** * Basic Elementary Functions 基本初等函数 *)

Open Scope R_scope.

(* ======================================================================= *)
(** ** Power function 幂函数 *)

(* fpowerR x a = x ^ a *)
Definition fpowerR (x a : R) : R := (Rpower x a).

Fact fpowerR_1_eq : forall x, 0 < x -> fpowerR x 1 = x.
Proof. intros. rewrite Rpower_1; auto. Qed.
Fact fpowerR_n1_eq : forall x, fpowerR x (-1) = (/ x)%R. Admitted.

Fact fpowerR_2_eq : forall x, fpowerR x 2 = x * x. Admitted.
Fact fpowerR_3_eq : forall x, fpowerR x 3 = x * x * x. Admitted.
Fact fpowerR_1_2_eq : forall x, fpowerR x (1/2) = sqrt x. Admitted.

(* ======================================================================= *)
(** ** Exponential function 指数函数 *)

(* fexpR a x = a ^ x *)
Definition fexpR (a x : R) : R := Rpower a x.

(* Axiom domain_of_fexpR : forall (a : R), (a > 0 /\ a <> 1) -> domain_of (fexpR a) = allR. *)
(* Fact range_of_fexpR (a : R) : range_of (fexpR a) = fun x => x > 0. Admitted. *)

Fact fexpR_add : forall a x y,
    a > 0 -> fexpR a (x + y) = (fexpR a x) * (fexpR a y).
Admitted.

Fact fexpR_sub : forall a x y,
    a > 0 -> fexpR a (x - y) = (fexpR a x) / (fexpR a y).
Admitted.

Fact fexpR_mul : forall a x y,
    a > 0 -> fexpR a (x * y) = fexpR (fexpR a x) y.
Admitted.

Fact fexpR_div : forall a b x,
    a > 0 /\ b > 0 -> fexpR (a/b) x = (fexpR a x) / (fexpR b x).
Admitted.

(* ======================================================================= *)
(** ** Logarithmic function 对数函数 *)

(* flogR a x = log_a x *)
Definition flogR (a x : R) : R := ln x / ln a.

(* flnR x = log_e x *)
Definition flnR (x : R) : R := ln x.

(* flgR x = log_10 x *)
Definition flg (x : R) : R := flogR 10 x.

(* Axiom domain_of_flogR : forall (a : R), *)
(*     (a > 0 /\ a <> 1) -> domain_of (flogR a) = (fun x => x > 0). *)
(* Fact range_of_flogR (a : R) : range_of (flogR a) = allR. Admitted. *)

(** 特殊函数值 *)
Fact flogR_a_1 (a : R) : flogR a 1 = 0.
Proof. unfold flogR. rewrite ln_1. field. Admitted.

Fact flogR_a_a (a : R) : flogR a a = 1. Admitted.
Fact flnR_1 : ln 1 = 0. Admitted.
Fact flnR_e : let e := 2.71828 in ln e = 1. Admitted.

(** 常用公式 *)
Fact flnR_mul : forall a x y, flogR a (x * y) = (flogR a x) + (flogR a y). Admitted.
Fact flnR_div : forall a x y, flogR a (x / y) = (flogR a x) - (flogR a y). Admitted.
Fact flnR_exp : forall a x y, flogR a (fexpR x y) = y * (flogR a x). Admitted.
Fact flnR_chgbottom : forall a b x, flogR a x = (flogR b x) / (flogR b a). Admitted.
Fact fexpR_flnR : forall x, exp (ln x) = x. Admitted.
Fact flnR_fexpR : forall x, ln (exp x) = x. Admitted.

Fact flnR_eq1 : forall u v : R, fpowerR u v = exp (ln (fpowerR u v)).
Proof. intros. rewrite fexpR_flnR. auto. Qed.
Fact flnR_eq2 : forall u v : R, fpowerR u v = exp (v * ln u).
Proof. intros. Admitted.

(* ======================================================================= *)
(** ** Trigonometric functions  三角函数 *)

(** Convert between degree and radian *)
Definition deg2rad (d : R) : R := d * (PI / 180).  (* 1 degree = 0.01745.. rad *)
Definition rad2deg (r : R) : R := r * (180 / PI).  (* 1 rad = 27.29578.. degree *)

(** definition of triangle functions *)
(* Check sin. *)
(* Check cos. *)
(* Check tan. *)
(* Check cot. *)
Definition cot (x : R) : R := / (tan x).
(* Check sec. *)
Definition sec (x : R) : R := / (cos x).
Definition csc (x : R) : R := / (sin x).

(** periodicity of sin/cos function over Z type *)
(* Note that, the coq standard library only defined it over nat type *)

(** sin (x + 2 * IZR k * PI) = sin x *)
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

(** cos (x + 2 * IZR k * PI) = cos x *)
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


(** 基本关系 *)
Fact sin_csc : forall x, (sin x) * (csc x) = 1. Admitted.
Fact cos_sec : forall x, (cos x) * (sec x) = 1. Admitted.
Fact tan_cot : forall x, (tan x) * (cot x) = 1. Admitted.
Fact sec_eq : forall x, sec x = 1 / (cos x). Admitted.
Fact csc_eq : forall x, csc x = 1 / (sin x). Admitted.
Fact tan_eq : forall x, tan x = (sin x) / (cos x). Admitted.
Fact cot_eq : forall x, cot x = (cos x) / (sin x). Admitted.
Fact sin2_add_cos2 : forall x, (sin x)² + (cos x)² = 1. Admitted.
Fact sec2_sub_tan2 : forall x, (sec x)² - (tan x)² = 1. Admitted.
Fact csc2_sub_cot2 : forall x, (csc x)² - (cot x)² = 1. Admitted.
Fact sin2_eq : forall x, (sin x)² = 1 - (cos x)². Admitted.
Fact cos2_eq : forall x, (cos x)² = 1 - (sin x)². Admitted.
Fact sec2_eq : forall x, (sec x)² = 1 - (tan x)². Admitted.
Fact tan2_eq : forall x, (tan x)² = 1 - (sec x)². Admitted.
Fact csc2_eq : forall x, (csc x)² = 1 - (csc x)². Admitted.
Fact cot2_eq : forall x, (cot x)² = 1 - (cot x)². Admitted.

(** 诱导公式 *)
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

Fact tan_PI2_sub : forall x, tan (PI/2 - x) = cot x. Admitted.
Fact tan_PI2_add : forall x, tan (PI/2 + x) = - cot x. Admitted.
Fact tan_PI_sub : forall x, tan (PI - x) = - tan x. Admitted.
Fact tan_PI_add : forall x, tan (PI + x) = tan x. Admitted.
Fact tan_add_PI : forall x, tan (x + PI) = tan x. Admitted.
Fact tan_sub_PI : forall x, tan (x - PI) = tan x. Admitted.
Fact tan_3PI2_sub : forall x, tan (3 * PI / 2 - x) = cot x. Admitted.
Fact tan_3PI2_add : forall x, tan (3 * PI / 2 + x) = - cot x. Admitted.
Fact tan_2PI_add : forall x, tan (2 * PI + x) = tan x. Admitted.

Fact cot_PI2_sub : forall x, cot (PI/2 - x) = tan x. Admitted.
Fact cot_PI2_add : forall x, cot (PI/2 + x) = - tan x. Admitted.
Fact cot_PI_sub : forall x, cot (PI - x) = - cot x. Admitted.
Fact cot_PI_add : forall x, cot (PI + x) = cot x. Admitted.
Fact cot_3PI2_sub : forall x, cot (3 * PI / 2 - x) = tan x. Admitted.
Fact cot_3PI2_add : forall x, cot (3 * PI / 2 + x) = - tan x. Admitted.
Fact cot_2PI_add : forall x, cot (2 * PI + x) = cot x. Admitted.

(** 特殊三角函数值 *)
Fact sin_0 : sin 0 = 0. Admitted.
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

Fact cos_0 : cos 0 = 1. Admitted.
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

(** 和差公式 *)
Fact sin_add : forall x y, sin (x + y) = sin x * cos y + cos x * sin y. Admitted.
Fact sin_sub : forall x y, sin (x - y) = sin x * cos y - cos x * sin y. Admitted.

Fact cos_add : forall x y, cos (x + y) = cos x * cos y - sin x * sin y. Admitted.
Fact cos_sub : forall x y, cos (x - y) = cos x * cos y + sin x * sin y. Admitted.

Fact tan_add : forall x y, tan (x + y) = (tan x + tan y) / (1 - tan x * tan y). Admitted.
Fact tan_sub : forall x y, tan (x - y) = (tan x - tan y) / (1 + tan x * tan y). Admitted.

Fact cot_add : forall x y, cot (x + y) = (cot x * cot y - 1) / (cot x + cot y). Admitted.
Fact cot_sub : forall x y, cot (x - y) = (cot x * cot y + 1) / (cot x - cot y). Admitted.

(** 倍角公式 *)
Fact sin_2a : forall x, sin (2 * x) = 2 * sin x * cos x. Admitted.
Fact cos_2a : forall x, cos (2 * x) = (cos x)² - (sin x)². Admitted.
Fact cos_2a' : forall x, cos (2 * x) = 1 - 2 * (sin x)². Admitted.
Fact cos_2a'' : forall x, cos (2 * x) = 2 * (cos x)² - 1. Admitted.
Fact tan_2a : forall x, tan (2 * x) = (2 * tan x) / (1 - (tan x)²). Admitted.
Fact cot_2a : forall x, cot (2 * x) = ((cot x)² - 1) / (2 * cot x). Admitted.

(** 半角公式 *)

(** 积化和差，和差化积 *)
Fact sin_cos : forall x y, sin x * cos y = (1/2) * (sin (x + y) + sin (x - y)). Admitted.
Fact cos_cos : forall x y, cos x * cos y = (1/2) * (cos (x + y) + cos (x - y)). Admitted.
Fact sin_sin : forall x y, sin x * sin y = (1/2) * (cos (x - y) - cos (x + y)). Admitted.

Fact sin_add_sin : forall x y, sin x + sin y = 2 * sin ((x+y)/2) * cos ((x-y)/2).
Admitted.
Fact sin_sub_sin : forall x y, sin x - sin y = 2 * sin ((x-y)/2) * cos ((x+y)/2).
Admitted.
Fact cos_add_cos : forall x y, cos x + cos y = 2 * cos ((x+y)/2) * cos ((x-y)/2).
Admitted.
Fact cos_sub_cos : forall x y, cos x - cos y = -2 * sin ((x+y)/2) * sin ((x-y)/2).
Admitted.

(** 周期公式 *)

(* cos x = 1 -> x = 2kπ *)
Lemma cos_1_period : forall (x : R) (k : Z), cos x = 1 -> x = 2 * IZR k * PI.
Admitted.

(* cos x = -1 -> x = 2kπ + π *)
Lemma cos_neg1_period : forall (x : R) (k : Z), cos x = -1 -> x = 2 * IZR k * PI + PI.
Admitted.

(* cos x = 0 -> x = kπ + π/2 *)
Lemma cos_0_period : forall (x : R) (k : Z), cos x = 0 -> x = IZR k * PI + PI/2.
Admitted.

(* ======================================================================= *)
(** ** 5. 反三角函数 *)
(* Check asin. *)
(* Check acos. *)
(* Check atan. *)
(* Check acot. *)
Parameter acot : R -> R.

(** 特殊函数值 *)
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

(* Fact atan_0 : atan 0 = 0. Admitted. *)
Fact atan_sqrt3_3 : atan ((sqrt 3) / 3) = PI / 6. Admitted.
(* Fact atan_1 : atan 1 = PI. Admitted. *)
Fact atan_sqrt3 : atan (sqrt 3) = PI / 3. Admitted.

Fact acot_0 : acot 0 = PI / 2. Admitted.
Fact acot_sqrt3_3 : acot ((sqrt 3) / 3) = PI / 6. Admitted.
Fact acot_1 : acot 1 = PI. Admitted.
Fact acot_sqrt3 : acot (sqrt 3) = PI / 3. Admitted.

(** 补充引理  *)

(** acos is injective in its domain *)
Lemma acos_inj : forall x1 x2 : R,
    -1 <= x1 <= 1 -> -1 <= x2 <= 1 -> acos x1 = acos x2 -> x1 = x2.
Proof.
  intros. rewrite <- cos_acos; auto.
  rewrite <- H1. rewrite cos_acos; auto.
Qed.

(* x < 0 -> acos x = atan ((sqrt (1-x²) / x) + PI *)
Lemma acos_atan_neg: forall x : R,
    x < 0 -> acos x = atan (sqrt (1 - x²) / x) + PI.
Proof.
  intros. replace x with (- (-x))%R; ra.
  rewrite acos_opp. rewrite Rmult_opp_opp.
  rewrite Rdiv_opp_r. rewrite atan_opp. rewrite acos_atan; ra.
Qed.
