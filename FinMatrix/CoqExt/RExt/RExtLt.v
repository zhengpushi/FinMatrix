(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Simplify the expressions about Rlt,Rle,Rgt,Rge.
  author    : Zhengpu Shi
  date      : 2021.05

  remark    :
 *)

Require Export RExtBase RExtSqr RExtAbs.

(* ======================================================================= *)
(** ** Basic automation *)

Hint Resolve
  Rlt_gt                (* a < b -> b > a *)
  Rgt_lt                (* a > b -> b < a *)
  Rle_ge                (* a <= b -> b >= a *)
  Rlt_le                (* a < b -> a <= b *)
  Rge_le                (* a >= b -> b <= a *)
  Rplus_lt_le_0_compat  (* 0 < r1 -> 0 <= r2 -> 0 < r1 + r2 *)
  Rplus_le_lt_0_compat  (* 0 <= r1 -> 0 < r2 -> 0 < r1 + r2 *)
  Rplus_lt_0_compat     (* 0 < r1 -> 0 < r2 -> 0 < r1 + r2 *)
  Rplus_le_le_0_compat  (* 0 <= r1 -> 0 <= r2 -> 0 <= r1 + r2 *)
  Rsqr_pos_lt           (* x <> 0 -> 0 < x² *)
  Rinv_0_lt_compat      (* 0 < r -> 0 < / r *)
  Rinv_lt_0_compat      (* r < 0 -> / r < 0 *)
  : R.


(* ======================================================================= *)
(** ** Additional properties *)

(** *** Basic logic relations *)

(** 0 < r -> r <> 0 *)
Lemma Rgt0_neq0 : forall r : R, 0 < r -> r <> 0.
Proof. intros. lra. Qed.
Hint Resolve Rgt0_neq0 : R.

(** r < 0 -> r <> 0 *)
Lemma Rlt0_neq0 : forall r : R, r < 0 -> r <> 0.
Proof. intros. lra. Qed.
Hint Resolve Rlt0_neq0 : R.

(** *** For arithmetic operations  *)

(** 0 <= 1 *)
Lemma zero_le_1 : 0 <= 1.
Proof. ra. Qed.
Hint Resolve zero_le_1 : R.

(** a <> b -> a <= b -> a < b *)
Lemma Rneq_le_lt : forall a b, a <> b -> a <= b -> a < b.
Proof. ra. Qed.
Hint Resolve Rneq_le_lt : R.

(** a < b -> 0 < b - a *)
(* Note, Rlt_Rminus is deprecated since 8.19 *)
Lemma Rlt_Rminus : forall a b : R, a < b -> 0 < b - a.
Proof. intros. apply (proj2 (Rlt_0_minus a b)); auto. Qed.
Hint Resolve Rlt_Rminus : R.

(** 0 < r -> 0 < 1 / r *)
Lemma Rinv1_gt0 : forall r : R, 0 < r -> 0 < 1 / r.
Proof. ra. Qed.
Hint Resolve Rinv1_gt0 : R.

(** 0 <= a -> b < 0 -> a / b <= 0 *)
Lemma Rdiv_ge0_lt0_le0 : forall a b : R, 0 <= a -> b < 0 -> a / b <= 0.
Proof. ra. assert (/b < 0); ra. Qed.
Hint Resolve Rdiv_ge0_lt0_le0 : R.

(** a < 0 -> b < 0 -> 0 < a / b *)
Lemma Rdiv_gt0_compat_neg : forall a b : R, a < 0 -> b < 0 -> 0 < a / b.
Proof. ra. assert (/b < 0); ra. Qed.
Hint Resolve Rdiv_gt0_compat_neg : R.

(** 0 <= a -> 0 < b -> 0 <= a / b *)
Lemma Rdiv_ge0_compat : forall a b : R, 0 <= a -> 0 < b -> 0 <= a / b.
Proof. ra. assert (0 < /b); ra. Qed.
Hint Resolve Rdiv_ge0_compat : R.

(** 0 < a -> b < 0 -> a / b < 0 *)
Lemma Rdiv_lt_0_compat_l : forall a b : R, 0 < a -> b < 0 -> a / b < 0.
Proof. intros. unfold Rdiv. assert (/b < 0); ra. Qed.
Hint Resolve Rdiv_lt_0_compat_l : R.

(** a < 0 -> 0 < b -> a / b < 0 *)
Lemma Rdiv_lt_0_compat_r : forall a b : R, a < 0 -> 0 < b -> a / b < 0.
Proof. intros. unfold Rdiv. assert (/b > 0); ra. Qed.
Hint Resolve Rdiv_lt_0_compat_r : R.

(** 0 <= a² + b² *)
Lemma Rplus2_sqr_ge0 : forall a b : R, 0 <= a² + b².
Proof. ra. Qed.
Hint Resolve Rplus2_sqr_ge0 : R.

(** a² + b² <> 0 -> 0 < a² + b² *)
Lemma Rplus2_sqr_neq0_imply_gt0 : forall a b : R, a² + b² <> 0 -> 0 < a² + b².
Proof. ra. Qed.
Hint Resolve Rplus2_sqr_neq0_imply_gt0 : R.

(** 0 < a² + b² -> a² + b² <> 0 *)
Lemma Rplus2_sqr_neq0_if_gt0 : forall a b : R, 0 < a² + b² -> a² + b² <> 0.
Proof. ra. Qed.
Hint Resolve Rplus2_sqr_neq0_if_gt0 : R.

(** a² + b² <> 0 <-> 0 < a² + b² *)
Lemma Rplus2_sqr_neq0_iff_gt0 : forall a b : R, a² + b² <> 0 <-> 0 < a² + b².
Proof. ra. Qed.

(** 2 * a * b <= a² + b² *)
Lemma R_neq1 : forall a b : R, 2 * a * b <= a² + b².
Proof. intros. apply Rge_le. apply Rminus_ge. rewrite <- Rsqr_minus. ra. Qed.
Hint Resolve R_neq1 : R.

(** 0 < a² + b² -> (a <> 0 \/ b <> 0) *)
Lemma Rplus2_sqr_gt0_imply : forall a b : R, 0 < a² + b² -> (a <> 0 \/ b <> 0).
Proof. ra. Qed.
Hint Resolve Rplus2_sqr_gt0_imply : R.

(** (a <> 0 \/ b <> 0) -> 0 < a² + b² *)
Lemma Rplus2_sqr_gt0_if : forall a b : R, (a <> 0 \/ b <> 0) -> 0 < a² + b².
Proof. ra. Qed.
Hint Resolve Rplus2_sqr_gt0_if : R.

(** 0 < a² + b² <-> (a <> 0 \/ b <> 0) *)
Lemma Rplus2_sqr_gt0 : forall a b : R, 0 < a² + b² <-> (a <> 0 \/ b <> 0).
Proof. ra. Qed.

(** a <> 0 -> 0 < a² + b² *)
Lemma Rplus2_sqr_gt0_l : forall a b, a <> 0 -> 0 < a² + b².
Proof. ra. Qed.
Hint Resolve Rplus2_sqr_gt0_l : R.

(** b <> 0 -> 0 < a² + b² *)
Lemma Rplus2_sqr_gt0_r : forall a b, b <> 0 -> 0 < a² + b².
Proof. ra. Qed.
Hint Resolve Rplus2_sqr_gt0_r : R.

(** (a * c + b * d)² <= (a² + b²) * (c² + d²) *)
Lemma Rsqr_mult_le : forall a b c d : R, (a * c + b * d)² <= (a² + b²) * (c² + d²).
Proof.
  intros. unfold Rsqr. ring_simplify.
  rewrite !Rplus_assoc. apply Rplus_le_compat_l.
  rewrite <- !Rplus_assoc. apply Rplus_le_compat_r.
  autorewrite with R.
  replace (a² * d²) with (a * d)²; [|ra].
  replace (c² * b²) with (c * b)²; [|ra].
  replace (2 * a * c * b * d) with (2 * (a * d) * (c * b)); [|ra].
  apply R_neq1.
Qed.

(** b > 0 -> a * /b < c -> a < b * c *)
Lemma Rdiv_le_imply_Rmul_gt a b c : b > 0 -> a * / b < c -> a < b * c.
Proof.
  ra. apply (Rmult_lt_compat_l b) in H0; auto.
  replace (b * (a * /b)) with a in H0; auto. ra.
Qed.
Hint Resolve Rdiv_le_imply_Rmul_gt : R.

(** b > 0 -> a < b * c -> a * / b < c *)
Lemma Rmul_gt_imply_Rdiv_le a b c : b > 0 -> a < b * c -> a * / b < c.
Proof.
  ra. apply (Rmult_lt_compat_l (/b)) in H0; auto with R.
  replace (/b * a) with (a / b) in *; ra.
  replace (/b * (b * c)) with c in *; ra.
Qed.
Hint Resolve Rmul_gt_imply_Rdiv_le : R.

(** 0 < a -> 0 < b -> 0 < c -> a < b * c -> a / b < c *)
Lemma Rdiv_lt_gt0_gt0_gt0 : forall a b c : R,
    0 < a -> 0 < b -> 0 < c -> a < b * c -> a / b < c.
Proof. ra. unfold Rdiv; ra. Qed.
Hint Resolve Rdiv_lt_gt0_gt0_gt0 : R.

(** 0 <= a -> 0 < b -> a <= b -> a / b <= 1 *)
Lemma Rdiv_le_1 : forall x y : R, 0 <= x -> 0 < y -> x <= y -> x / y <= 1.
Proof.
  intros. unfold Rdiv. replace 1 with (y * / y); ra.
  apply Rmult_le_compat_r; ra.
Qed.

(** b <> 0 -> |a| <= |b| -> |a / b| <= 1 *)
Lemma Rdiv_abs_le_1 : forall a b : R, b <> 0 -> |a| <= |b| -> | a / b | <= 1.
Proof.
  intros. unfold Rdiv. rewrite Rabs_mult. rewrite Rabs_inv.
  apply Rdiv_le_1; auto; ra. apply Rabs_pos_lt; auto.
Qed.


(** *** For operation sqrt  *)

(** \sqrt {a² + b²} <= |a| + |b| *)
Lemma R_neq5 : forall a b : R, sqrt (a² + b²) <= Rabs a + Rabs b.
Proof.
  intros.
  rewrite <- sqrt_square.
  - apply sqrt_le_1_alt.
    apply Rle_trans with (Rabs a * Rabs a + Rabs b * Rabs b)%R.
    + rewrite <- !Rabs_mult. apply Rplus_le_compat.
      apply RRle_abs. apply RRle_abs.
    + ring_simplify.
      rewrite !Rplus_assoc. apply Rplus_le_compat_l.
      rewrite <- Rplus_0_l at 1. apply Rplus_le_compat_r.
      assert (0 <= Rabs a) by ra; assert (0 <= Rabs b) by ra. ra.
  - assert (0 <= Rabs a) by ra; assert (0 <= Rabs b) by ra. ra.
Qed.

(** a * c + b * d <= \sqrt {(a² + b²) * (c² + d²)} *)
Lemma R_neq6 : forall a b c d : R, a * c + b * d <= sqrt((a² + b²) * (c² + d²)).
Proof.
  intros.
  apply Rsqr_incr_0_var; ra.
  rewrite Rsqr_sqrt; ra.
  unfold Rsqr. ring_simplify.
  (* Tips: we should develop "sgroup" like tactci to automate these two steps *)
  rewrite !Rplus_assoc; repeat apply Rplus_le_compat_l.
  rewrite <- !Rplus_assoc; repeat apply Rplus_le_compat_r.
  autorewrite with R.
  (* 2acbd <= a² * d² + c² * b² *)
  replace (2 * a * c * b * d) with (2 * (a * d) * (b * c)) by ra.
  replace (a² * d² + c² * b²)%R with ((a*d)² + (b * c)²) by ra.
  apply R_neq1.
Qed.


(** *** For famous inequalities *)

(* QM-AM-GM-HM inequalities.
   https://en.wikipedia.org/wiki/QM-AM-GM-HM_inequalities

  Suppose that x1,x2,...,xn are positive real numbers,
  denoted
    调和平均数 harmonic mean (HM)   = \frac{n}{∑(1/xi)},
    算术平均数 arithmetic mean (AM) = (∑xi)/n,
    几何平均数 geometric mean (GM)  = n√(∏xi),
    二次平均数 quadratic mean (QM)  = \sqrt{(∑xi^2)/n},
  then
    0 < HM <= AM <= GM <= QM.
 *)

(* AM-GM inequality.
   https://en.wikipedia.org/wiki/AM%E2%80%93GM_inequality
     a1+a2+...+an      n______________
    -------------- >=  / a1*a2*...*an
          n
    and this equality holds if and only if x1 = x2 = · · · = xn. 
 *)

(* AM-QM inequality, case n = 2 *)
Lemma Rneq_AM_GM_2 : forall a b : R,
    0 <= a -> 0 <= b ->
    (a + b) / 2 >= sqrt(a * b).
Proof.
Admitted.

(* AM-QM inequality, case n = 3 *)
Lemma Rneq_AM_GM_3 : forall a b c : R,
    0 <= a -> 0 <= b -> 0 <= c ->
    (a + b + c) / 3 >= sqrt(a * b).
Admitted.


(** *** For inequalities about PI *)

(** 0 < r -> 0 < r * PI *)
Lemma mult_PI_gt0 : forall r, 0 < r -> 0 < r * PI.
Proof. ra. Qed.


(* A strange problem about "lra":
   现象：
   在一个涉及到PI的不等式证明中，无法自动化完成。
   当新增一个看似无关的前提“- PI < b <= PI” (此处的 b 未在命题中出现），则可以得证。

   分析：
   可能是 lra 不知道 - PI < PI 这个事实。
   通过这个例子，我们也发现了一个技巧，虽然 lra 无法证明 PI，但可以设定一个近似表示，
   比如 “3.14 < PI < 3.15”，然后 lra 就能用了。
   
   总结：
   主要原因是关于 PI 的自动化程度低，需要借助常量。
 *)
Section lra_problem.

  (* Just give a hypothesis about PI such as "- PI < x < PI",
     then the next proof will not be done. *)
  Variable abcdefg : R.
  Hypotheses Habcdefg : - PI < abcdefg < PI.

  (* Or, simply give "- PI < PI" *)
  (* Hypotheses Habcdefg' : - PI < PI. *)
  
  Lemma Rsplit_neg_pi_to_pi' : forall a : R,
      -PI < a <= PI <->
        a = -PI/2 \/ a = 0 \/ a = PI/2 \/
          (-PI < a < -PI/2) \/ (-PI/2 < a < 0) \/
          (0 < a < PI/2) \/ (PI/2 < a <= PI).
  Proof.
    intros.
    lra.
  Qed.
End lra_problem.

(* Motivation example: I cannot prove it automatically *)
Goal 2 < PI.
Proof.
  (* lra. *)
  (* nra. *)
Abort.

(** Explicit upper and lower bound of PI *)
Notation PI_ub := 3.14159266.
Notation PI_lb := 3.14159265.
Axiom PI_ub_axiom : PI < PI_ub.
Axiom PI_lb_axiom : PI_lb < PI.
Hint Resolve PI_ub_axiom PI_lb_axiom : R.

(** PI_lb < PI < PI_ub *)
Lemma PI_bound : PI_lb < PI < PI_ub.
Proof. ra. Qed.

Section test.
  (* method 1: by transitivity *)
  Goal 2 < PI.
  Proof.
    ra. apply Rlt_trans with PI_lb; ra.
  Qed.

  (* method 2: by adding an equation *)
  Goal 2 < PI.
  Proof.
    pose proof PI_bound. ra.
  Qed.
End test.


(** *** Other things that need to be done manually *)

(* Examples that cannot automatically solved now *)
Section examples.

  (* About Carg in Complex. *)
  Goal forall a b c, a > 0 -> b <= c / a -> 0 <= c - b *a.
  Proof.
    ra.
    apply Rmult_le_compat_r with (r:=a) in H0; ra.
    unfold Rdiv in H0. rewrite Rmult_assoc in H0.
    rewrite Rinv_l in H0; ra.
  Qed.

  (* About Propulsition System in FCS *)
  
  (* 1/153 = 0.006536.. *)
  
  (* This proof cannot be finished in one step *)
  Goal forall h T, 0 < h -> h < 9200 -> -60 < T -> T < 60 -> h / (273.15 + T) < 153.
  Proof. ra. Abort.

  (* Let's manually prove it *)
  Variable h T : R.
  Hypothesis Hh1 : 0 < h.
  Hypothesis Hh2 : h < 9200.
  Hypothesis HT1 : -60 < T.
  Hypothesis HT2 : T < 60.

  (* a simpler proposition, it can be proved in one step *)
  Goal h * 0.0065 < 273.15 + T. ra. Qed.

  (* A bit complex proposition, requires manual proof *)
  Goal h / (273.15 + T) < 153.
  Proof.
    ra.
    assert (273.15 + T > 0); ra.
    assert (h < (273.15 + T) * 153); ra.
    unfold Rdiv; ra.
  Qed.

  (* A more bit complex proposition, requires manual proof *)
  Goal h / (273.15 + T) < 1 / 0.0065.
  Proof.
    ra.
    assert (273.15 + T > 0); ra.
    assert (h < (273.15 + T) * (1/0.0065)); ra.
    apply Rdiv_lt_gt0_gt0_gt0; ra.
  Qed.
  
  (* Original proposition, requires manual proof *)
  Goal 0 < 1 - (0.0065 * (h * / (273.15 + T))).
  Proof.
    assert (h / (273.15 + T) < /0.0065); ra.
    apply Rdiv_lt_gt0_gt0_gt0; ra. 
  Qed.

End examples.


(* ======================================================================= *)
(** ** Extra automation *)
