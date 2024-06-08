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
Require Export RExtPlus RExtMult RExtPow RExtOpp RExtInv.
Require Export RExtSqr RExtSqrt RExtAbs RExtExp RExtApprox RExtTrigo.


(* ======================================================================= *)
(** ** Sign function *)
Definition sign : R -> R :=
  fun x => if x >? 0 then 1 else (if x =? 0 then 0 else -1).

(** x = 0 -> sign x = 0 *)
Lemma sign_eq0 : forall x, x = 0 -> sign x = 0.
Proof.
  intros. unfold sign. bdestruct (0 <? x); ra. bdestruct (x =? 0); ra.
Qed.

(** x > 0 -> sign x = 1 *)
Lemma sign_gt0 : forall x, x > 0 -> sign x = 1.
Proof. intros. unfold sign. bdestruct (x >? 0); ra. Qed.

(** x < 0 -> sign x = - 1 *)
Lemma sign_lt0 : forall x, x < 0 -> sign x = -1.
Proof.
  intros. unfold sign. bdestruct (x >? 0); ra. bdestruct (x =? 0); ra.
Qed.

(** (sign x) * x = |x| *)
Lemma sign_mul_eq_abs : forall x, ((sign x) * x)%R = Rabs x.
Proof.
  intros. unfold sign. bdestruct (0 <? x); ra. bdestruct (x =? 0); subst; ra.
  rewrite Rabs_left1; ra.
Qed.

(** (sign x) * |x| = x *)
Lemma sign_mul_abs_eq : forall x, ((sign x) * (Rabs x))%R = x.
Proof.
  intros. unfold sign. bdestruct (0 <? x); ra. bdestruct (x =? 0); ra.
  rewrite Rabs_left1; ra.
Qed.

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
Fact flnR_Rpower : forall a x y, flogR a (Rpower x y) = y * (flogR a x). Admitted.
Fact flnR_chgbottom : forall a b x, flogR a x = (flogR b x) / (flogR b a). Admitted.
Fact fexpR_flnR : forall x, exp (ln x) = x. Admitted.
Fact flnR_fexpR : forall x, ln (exp x) = x. Admitted.

Fact flnR_eq1 : forall u v : R, Rpower u v = exp (ln (Rpower u v)).
Proof. intros. rewrite fexpR_flnR. auto. Qed.
Fact flnR_eq2 : forall u v : R, Rpower u v = exp (v * ln u).
Proof. intros. Admitted.


(* ======================================================================= *)
(** ** Test *)

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
