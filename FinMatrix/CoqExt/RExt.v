(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : extension for Coq.Reals.
  author    : ZhengPu Shi
  date      : 2021.05
  
  remark    :
  1. possible reason of "field" failure
    a. notation "/", need unfold Rdiv first.
    b. unknown variable name, need be rewrite first.

  2. why need this library?
     (1) lots of properties are lack in standard library.
     (2) more automation, especially inequality.
     (3) We want to solve any problem of equality or inequality in one step.
  3. why auto fail? and how to better naming a term?
     (1) use two lemmas like A -> B and B -> A instead of A <-> B
     (2) x * x and x² are mixed, and x² is defined as x * x, and Coq Standard 
         Library prefer x², so we'd better choose x². But, notice that we should 
         rewrie x² to x * x before using ring or field, it's a bit annoying.
     (3) 1 and R1 are mixed, and 1 is (IZR (Zpos xH)), and will be reduced to R1
         finally, and Coq Standard Library prefer 1, so we choose 1 as well.
     (4) x - y and x + (-y) is same, but we prefer x - y.
     (5) x / y and x * (-y), we prefer x / y as well.

  4. Coq's support for automatic proofs of equalities and inequalities.
     ref：https://coq.inria.fr/distrib/current/refman/addendum/micromega.html
     (1) Micromega: a solver to solving arithmetic goals by ordered ring structure.
     (2). Psatz: a solver to solvign arithmetic golas on Q,R,Z,nat, and N.
     lia: linear, for integer (including Z,nat, and N)
     nia: non-linear, for integer
     lqa: linear, for rational number Q.
     lra: linear, for real number R and rational number Q.
     nra: non-linear, for real number and rational number.
     psatz D n: non-linear
     here, D is Z/Q/R, n is an optional integer representing search depth.
     (3). What's the ability of these solvers?
     It can solve the propositional formulas which its parameters are in the 
     field D∈{Z,Q,R}. The formulas are belows:
        p ::= c | x | -p | p+p | p-p | p*p | p^n
        A ::= p=p | p>p | p<p | p<=p | p>=p
        F ::= A | P | True | False | F/\F | F\/F | F<->F | F->F | ~F | F=F
        Here,
            c is constant in D,
            x is variable in D,
            -,+,* is subtract,addition,multiplication seperately,
            p^n is power of nat n,
            F are interpreted as Prop or bool.
       (a) If F is interpreted as bool, the corresponding operaters are:
           &&,||,eqb,implb,negb.
           And if D is Z, then the relations are: Z.eqb,Z.gtb,Z.ltb,Z.geb,Z.leb
           And if D is Q, then the equal realtion is Qeq (==), not eq (=).
       (b) the range of constant c,
           for Z and Q, c is all possible value could be get;
           for R, c is the expression below:
            c ::= R0 | R1 | IZR z | Q2R q 
                  | Rmult c c | Rplus c c | Rminus c c| Rdiv c c | Rinv c
 *)


Require Export RExtBase RExtCvt RExtStruct RExtBool RExtLt.
Require Export RExtPlus RExtMult RExtOpp RExtInv.
Require Export RExtSqr RExtSqrt RExtAbs RExtTrigo.

(* About "1" *)
Section test.
  Goal 1 = R1. ra. Qed.
  Goal R1² = 1. ra. Qed.
  Goal 1² = R1. ra. Qed.
  Goal /R1 = R1. ra. Qed.
  Goal /R1 = 1. ra. Qed.
  Goal /1 = R1. ra. Qed.
  Goal 0 <= R1. ra. Qed.
End test.

(* About "square" *)
Section test.
  (** r * r = 0 <-> r = 0 *)
  Goal forall r, r * r = 0 <-> r = 0. ra. Qed.
  Goal forall r, r * r <> 0 <-> r <> 0. ra. Qed.
  Goal forall r1 r2 : R, 0 <= r1 * r1 + r2 * r2. ra. Qed.
  Goal forall r1 r2 : R,  r1 <> 0 \/ r2 <> 0 <-> r1 * r1 + r2 * r2 <> 0. ra. Qed.
  Goal forall r1 r2 : R,  r1 * r1 + r2 * r2 <> 0 <-> 0 < r1 * r1 + r2 * r2. ra. Qed.
  Goal forall r1 r2 r3 : R,
      r1 <> 0 \/ r2 <> 0 \/ r3 <> 0 <-> r1 * r1 + r2 * r2 + r3 * r3 <> 0. ra. Qed.
  Goal forall r1 r2 r3 r4 : R,
      r1 <> 0 \/ r2 <> 0 \/ r3 <> 0 \/ r4 <> 0 <->
        r1 * r1 + r2 * r2 + r3 * r3 + r4 * r4 <> 0. ra. Qed.
End test.

(* About "trigonometric functions" *)
Section test.
  Goal forall x, cos x * cos x + sin x * sin x = R1. ra. Qed.
  Goal forall x, sin x * sin x + cos x * cos x = R1. ra. Qed.
End test.

(* About "0 <= x" *)
Section test.
  Goal forall r, 0 <= r * r. ra. Qed.
  Goal forall r, 0 <= r². ra. Qed.
  Goal forall r1 r2, 0 <= r1 * r1 + r2 * r2. ra. Qed.
  Goal forall r1 r2, 0 <= r1² + r2². ra. Qed.
  Goal forall r1 r2, 0 <= r1 * r1 + r2². ra. Qed.
  Goal forall r1 r2, 0 <= r1² + r2 * r2. ra. Qed.
  Goal forall r, 0 <= r -> 0 <= r * 5. ra. Qed.
  Goal forall r, 0 <= r -> 0 <= r * 5 * 10. ra. Qed.
  Goal forall r, 0 <= r -> 0 <= r * (/5) * 10. ra. Qed.
End test.

(* 0 < x *)
Section test.
  Goal forall r, 0 <> r -> 0 < r * r. ra. Qed.
  Goal forall r, 0 <> r -> 0 < r². ra. Qed.
  Goal forall r, 0 < r -> 0 < r * r. ra. Qed.
  Goal forall r, 0 < r -> 0 < r². ra. Qed.
  Goal forall r1 r2, r1 <> 0 -> 0 < r1 * r1 + r2 * r2. ra. Qed.
  Goal forall r1 r2, r1 <> 0 -> 0 < r1² + r2 * r2. ra. Qed.
  Goal forall r1 r2, r1 <> 0 -> 0 < r1 * r1 + r2². ra. Qed.
  
  Goal forall r1 r2, r2 <> 0 -> 0 < r1 * r1 + r2 * r2. ra. Qed.
  Goal forall r1 r2, r2 <> 0 -> 0 < r1² + r2 * r2. ra. Qed.
  Goal forall r1 r2, r2 <> 0 -> 0 < r1 * r1 + r2². ra. Qed.
  
  Goal forall r1 r2, 0 < r1 -> 0 < r1 * r1 + r2 * r2. ra. Qed.
  Goal forall r1 r2, 0 < r2 -> 0 < r1 * r1 + r2 * r2. ra. Qed.
  
  Goal forall r, 0 < r -> 0 < r * 10. ra. Qed.
  Goal forall r, 0 < r -> 0 < r + 10. ra. Qed.
  Goal forall r, 0 < r -> 0 < r * 100 + 23732. ra. Qed.
End test.

(* x <> 0 *)
Section test.
  Goal forall r, r² <> 0 <-> r <> 0. ra. Qed.
  Goal forall r, r² <> 0 -> r <> 0. ra. Qed.
  Goal forall r, r <> 0 -> r * r <> 0. ra. Qed.
  Goal forall r, r <> 0 -> r² <> 0. ra. Qed.

  Goal forall r, 0 <> r * r -> r <> 0. ra. Qed.
  Goal forall r, r * r <> 0 -> 0 <> r. ra. Qed.
  Goal forall r, 0 <> r * r -> 0 <> r. ra. Qed.
  
  Goal forall r1 r2 r3 r4 : R,
    r1 <> 0 \/ r2 <> 0 \/ r3 <> 0 \/ r4 <> 0 <-> 
    r1 * r1 + r2 * r2 + r3 * r3 + r4 * r4 <> 0.
  Proof. ra. Qed.
End test.

?


(* ######################################################################### *)
(** * atan *)


(* ######################################################################### *)
(** * Approximate of two real numbers *)

(** r1 ≈ r2, that means |r1 - r2| <= diff *)
Definition Rapprox (r1 r2 diff : R) : Prop := |r1 - r2| <= diff.

(** boolean version of approximate function *)
Definition Rapproxb (r1 r2 diff : R) : bool := |r1 - r2| <=? diff.


(* ######################################################################### *)
(** * Additional properties *)

(** (a * c + b * d)² <= (a² + b²) * (c² + d²) *)
Lemma Rsqr_mult_le : forall a b c d : R, (a * c + b * d)² <= (a² + b²) * (c² + d²).
Proof.
  intros. unfold Rsqr. ring_simplify.
  rewrite !associative. apply Rplus_le_compat_l.
  rewrite <- !associative. apply Rplus_le_compat_r.
  autorewrite with R.
  replace (a² * d²) with (a * d)²; [|ra].
  replace (c² * b²) with (c * b)²; [|ra].
  replace (2 * a * c * b * d) with (2 * (a * d) * (c * b)); [|ra].
  apply R_neq1.
Qed.

Lemma Rdiv_le_1 : forall x y : R, 0 <= x -> 0 < y -> x <= y -> x / y <= 1.
Proof.
  intros. unfold Rdiv. replace 1 with (y * / y); ra.
  apply Rmult_le_compat_r; ra. apply Rinv_r; ra.
Qed.

(* b <> 0 -> |a| <= |b| -> |a/b| <= 1 *)
Lemma Rdiv_abs_le_1 : forall a b : R, b <> 0 -> |a| <= |b| -> | a / b | <= 1.
Proof.
  intros. unfold Rdiv. rewrite Rabs_mult. rewrite Rabs_inv.
  apply Rdiv_le_1; auto; ra. apply Rabs_pos_lt; auto.
Qed.

#[export] Hint Resolve
  Rdiv_le_1
  : R.


(** b <> 0 -> a * b = b -> a = 1 *)
Lemma Rmult_eq_r_reg : forall a b : R, b <> 0 -> a * b = b -> a = 1.
Proof.
  intros. replace b with (1 * b)%R in H0 at 2 by lra.
  apply Rmult_eq_reg_r in H0; auto.
Qed.

(** a <> 0 -> a * b = a -> b = 1 *)
Lemma Rmult_eq_l_reg : forall a b : R, a <> 0 -> a * b = a -> b = 1.
Proof.
  intros. replace a with (a * 1)%R in H0 at 2 by lra.
  apply Rmult_eq_reg_l in H0; auto.
Qed.

(** Absolute function *)
Lemma Rabs_pos_iff : forall x, |x| = x <-> x >= 0.
Proof.
  intros. split; intros.
  - bdestruct (x >=? 0). lra. exfalso.
    assert (x <= 0); try lra.
    apply Rabs_left1 in H1. lra.
  - apply Rabs_right. auto.
Qed.

Lemma Rabs_neg_iff : forall x, |x| = - x <-> x <= 0.
Proof.
  intros. split; intros.
  - destruct (Rleb_reflect x 0); auto.
    assert (x >= 0); try lra.
    apply Rabs_right in H0. lra.
  - apply Rabs_left1. auto.
Qed.

Lemma Rabs_le_rev : forall a b : R, |a| <= b -> - b <= a <= b.
Proof.
  intros. bdestruct (a <? 0).
  - assert (|a| = -a). apply Rabs_neg_iff; ra. ra.
  - assert (|a| = a). apply Rabs_pos_iff; ra. ra.
Qed.

Lemma mult_PI_gt0 : forall r, 0 < r -> 0 < r * PI.
Proof. ra. Qed.  

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
  apply Rsqr_incr_0_var; ra. ring_simplify.
  autorewrite with R sqrt; ra.
  ring_simplify.
  rewrite !Rplus_assoc; repeat apply Rplus_le_compat_l.
  rewrite <- !Rplus_assoc; repeat apply Rplus_le_compat_r.
  (* 2acbd <= a^2*d^2+b^2*c^2 *)
  autorewrite with R.
  replace (2 * a * c * b * d)%R with (2 * (a * d) * (b * c))%R by ring.
  replace (a² * d² + c² * b²)%R with ((a*d)² + (b * c)²)%R; try (cbv; ring).
  apply R_neq1.
Qed.


(** 算术-几何平均值不等式，简称 “算几不等式” *)
(* 设 x1,x2,...,xn 为 n 个正实数，
     记算术平均数是 An = (∑xi)/n，
     记几何平均数是 Gn = n√(∏xi)，
     则 An >= Gn
     等号成立，当且仅当 x1 = x2 = ... = xn。
     
     展开后的形式

     a1+a2+...+an    n ______________
     ------------ >=  / a1*a2*...*an
          n
 *)

(** 平均数不等式，或称平均值不等式、均值不等式。是算几不等式的推广 *)
(* https://zh.wikipedia.org/wiki/平均数不等式 *)

(* 在2维和3维的具体形式 *)
Lemma R_neq7 : forall a b : R,
    0 <= a -> 0 <= b ->
    (a + b) / 2 >= sqrt(a * b).
Abort.

Lemma R_neq8 : forall a b c : R,
    0 <= a -> 0 <= b -> 0 <= c ->
    (a + b + c) / 3 >= sqrt(a * b).
Abort.
