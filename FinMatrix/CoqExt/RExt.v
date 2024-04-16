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


Require Export Lia Lra Reals.
Require Import ZExt QExt QcExt.
Require Export Basic.
Require Export Hierarchy.

Open Scope R_scope.

(* ######################################################################### *)
(** * Config the usage of Coq-Standard-Library Reals: Hints, Opaque, auto *)

(** Config hint db for autounfold *)
Global Hint Unfold
  Rminus        (* a - b = a + - b *)
  Rdiv          (* a / b = a * / b *)
  Rsqr          (* r² = r * r *)
  : R.

(** Config hint db for autorewrite, for rewriting of equations *)
#[export] Hint Rewrite
  (* Abs *)
  Rabs_R0             (* |0| = 0 *)
  Rabs_Ropp           (* |-x| = |x| *)
  Rabs_Rabsolu        (* | |x| | = |x| *)

  (* + *)
  Rplus_0_l           (* 0 + r = r *)
  Rplus_0_r           (* r + 0 = r *)

  (* -a *)
  Ropp_0              (* - 0 = 0 *)
  Rminus_0_r          (* r - 0 = r *)
  Ropp_involutive     (* - - r = r *)
  Rplus_opp_r         (* r + - r = 0 *)
  Rplus_opp_l         (* - r + r = 0 *)
  Rminus_diag         (* r - r = 0 *)

  (* x *)
  Rsqr_0              (* 0² = 0 *)
  Rsqr_1              (* 1² = 1 *)
  Rmult_0_l           (* 0 * r = 0 *)
  Rmult_0_r           (* r * 0 = 0 *)
  Rmult_1_l           (* 1 * r = r *)
  Rmult_1_r           (* r * 1 = r *)
(*   Ropp_mult_distr_r_reverse     (* r1 * - r2 = - (r1 * r2) *) *)
(*   Ropp_mult_distr_l_reverse     (* - r1 * r2 = - (r1 * r2) *) *)

  (* pow *)
  pow1                (* 1 ^ n = 1 *)
  pow_O               (* x ^ 0 = 1 *)
  pow_1               (* x ^ 1 = x *)

  (* Rpower *)
  Rpower_O            (* power x 0 = 1 *)
  Rpower_1            (* power x 1 = x *) 
  
  (* sqr *)
  Rsqr_mult           (* (x * y)² = x² * y² *)

  (* sqrt *)
  sqrt_Rsqr_abs       (* (sqrt x²) = |x| *)
  
  sqrt_0              (* sqrt 0 = 0 *)
  : R.


(** Note that, these leamms should be used careful, they may generate an undesired
    burden of proof. Thus, we use a new database name "sqrt" *)
#[export] Hint Rewrite
  (* Abs *)
  Rsqr_sqrt           (* 0 <= x -> (sqrt x)² = x *)
  sqrt_Rsqr           (* 0 <= x -> sqrt x² = x *)
  : sqrt.


(** Config hint db for auto，for solving equalities or inequalities *)
Global Hint Resolve
  (* equalities *)
  eq_sym              (* a = b -> b = a *)
  sqrt_0              (* sqrt 0 = 0 *)
  Rsqr_eq_0           (* x² = 0 -> x = 0 *)
(*   sqrt_sqrt           (* 0 <= x -> sqrt x * sqrt x = x *) *)
  Rsqr_sqrt           (* 0 <= x -> (sqrt x)² = x *)
  sqrt_Rsqr           (* 0 <= x -> sqrt x² = x *)
  sin2_cos2           (* (sin x)² + (cos x)² = 1 *)
  acos_0              (* acos 0 = PI/2 *)
  acos_1              (* acos 1 = 0 *)

  (* general inequalities *)
  Rlt_0_1             (* 0 < 1 *)
  PI_RGT_0            (* PI > 0 *)
  Rabs_pos            (* 0 <= |x| *)
  Rabs_no_R0          (* r <> 0 -> |r| <> 0 *)
  sqrt_pos            (* 0 <= sqrt x *)
  
  (* inequalities such as "0 <= r1 + r2" *)
  Rplus_le_le_0_compat  (* 0 <= r1 -> 0 <= r2 -> 0 <= r1 + r2 *)
  Rplus_lt_le_0_compat  (* 0 < r1 -> 0 <= r2 -> 0 < r1 + r2 *)
  Rplus_le_lt_0_compat  (* 0 <= r1 -> 0 < r2 -> 0 < r1 + r2 *)
  Rplus_lt_0_compat   (* 0 < r1 -> 0 < r2 -> 0 < r1 + r2 *)

  (* inequalities such as {0 <= r1*r2, 0 <= /r, 0 <= r1/r2} *)
  Rle_0_sqr           (* 0 <= r² *)
(*   Rsqr_inj            (* 0 <= x -> 0 <= y -> x² = y² -> x = y *) *)
  Rsqr_pos_lt         (* x <> 0 -> 0 < x² *)
  Rmult_lt_0_compat   (* 0 < r1 -> 0 < r2 -> 0 < r1 * r2 *)
  Rinv_0_lt_compat    (* 0 < r -> 0 < / r *)
  Rinv_lt_0_compat    (* r < 0 -> / r < 0 *)
  Rdiv_lt_0_compat    (* 0 < a -> 0 < b -> 0 < a / b *)


  (* inequalities such as "r1 <= r2" *)
  Rlt_gt              (* r1 < r2 -> r2 > r1 *)  (* THIS IS ALWAYS NEED! *)
  Rgt_lt              (* r1 > r2 -> r2 < r1 *)  (* THIS ONE, slow but useful *)
  Rge_le              (* r1 >= r2 -> r2 <= r1 *)
  Rle_ge              (* r1 <= r2 -> r2 >= r1 *)
  Rlt_le              (* r1 < r2 -> r1 <= r2 *)
  Rsqr_pos_lt         (* x <> 0 -> 0 < x² *)

  (* inequalities such as "r1 <> r2" *)
  Rgt_not_eq          (* r1 > r2 -> r1 <> r2 *)
  Rlt_not_eq          (* r1 < r2 -> r1 <> r2 *)

  (* inequalities containing "sqrt" *)
  sqrt_lt_R0          (* 0 < x -> 0 < sqrt x *) (* THIS should be IFF *)
  sqrt_inj            (* 0 <= x -> 0 <= y -> sqrt x = sqrt y -> x = y *)
  : R.


(** Control Opaque / Transparent of the definitions *)
Global Opaque 
  PI 
  sqrt
  Rpower 
  sin 
  cos
  tan
  asin
  atan
  acos
  ln
.

Section TEST_psatz.
  Goal forall x y, x ^ 2 + y * y >= x * y.
    intros.
    (* psatz R 1. (* require external tool CSDP *) *)
    nra.
  Qed.

End TEST_psatz.

(* ======================================================================= *)
(** ** Automation for proof *)

(** arithmetric on reals : lra + nra *)
Ltac ra :=
  intros; unfold Rsqr in *; try lra; try nra; auto with R.

(** Try to prove equality of two R values, using `R` db, especially for triangle *)
Ltac req :=
  autorewrite with R; ra.

(** Convert `a ^ (n + 2)` to `(a ^ 2) * (a ^ n)` *)
Ltac simp_pow :=
  match goal with
  | |- context[?a ^ 4] => replace (a ^ 4) with ((a ^ 2) ^ 2); [|ring]
  | |- context[?a ^ 3] => replace (a ^ 3) with ((a ^ 2) * a)%R; [|ring]
  end.


(* ######################################################################### *)
(** * Decidable procedure for comparison of R *)

(** ** Notations for comparison with decidable procedure *)
Infix "??=" := (Req_EM_T) : R_scope.

(* For all four cases of comparison, we allow all these notations, but the `Display`
   will be only two cases, in order to simplify the cases of proof *)

(* These two notations will be covered by next two notations *)
Notation "x ??>= y" := (Rle_lt_dec y x) : R_scope.
Notation "x ??> y" := (Rlt_le_dec y x) : R_scope.

(* These two notations have higher priority *)
Infix "??<=" := (Rle_lt_dec) : R_scope.
Infix "??<" := (Rlt_le_dec) : R_scope.

(** ** Verify above notations are reasonable *)

(* a = b, iff, a ??= b *)
Lemma ReqDec_spec : forall a b : R, a = b <-> if a ??= b then true else false.
Proof. intros. destruct (_??=_); split; intros; try congruence. Qed.

(* a ??>= b, iff, b ??<= a *)
Lemma RgeDec_spec : forall a b : R,
    (if a ??>= b then true else false) = (if b ??<= a then true else false).
Proof. intros. auto. Qed.

(* a ??> b, iff, b ??< a *)
Lemma RgtDec_spec : forall a b : R,
    (if a ??> b then true else false) = (if b ??< a then true else false).
Proof. intros. auto. Qed.

(* a <= b, iff, a ??<= b *)
Lemma RleDec_spec : forall a b : R, a <= b <-> if a ??<= b then true else false.
Proof. intros. destruct (_??<=_); split; intros; try congruence. lra. Qed.

(* a < b, iff, a ??< b *)
Lemma RltDec_spec : forall a b : R, a < b <-> if a ??< b then true else false.
Proof. intros. destruct (_??<_); split; intros; try congruence. lra. Qed.


(** ** Aditional properties about RxxDec *)

(* if x ??<= x then b1 else b2 = b1 *)
Lemma RleDec_refl : forall {B} (x : R) (b1 b2 : B),
    (if x ??<= x then b1 else b2) = b1.
Proof. intros. destruct (_??<= _); ra. Qed.


(* ######################################################################### *)
(** * Reqb,Rleb,Rltb: Boolean comparison of R *)


#[export] Instance R_eq_Dec : Dec (@eq R).
Proof. constructor. apply Req_EM_T. Defined.

#[export] Instance R_le_Dec : Dec Rle.
Proof. constructor. intros. destruct (Rle_lt_dec a b); auto. right; lra. Qed.

#[export] Instance R_lt_Dec : Dec Rlt.
Proof. constructor. intros. destruct (Rlt_le_dec a b); auto. right; lra. Qed.

Definition Reqb (r1 r2 : R) : bool := Acmpb R_eq_Dec r1 r2.
Definition Rleb (r1 r2 : R) : bool := Acmpb R_le_Dec r1 r2.
Definition Rltb (r1 r2 : R) : bool := Acmpb R_lt_Dec r1 r2.
Infix "=?"  := Reqb : R_scope.
Infix "<=?" := Rleb : R_scope.
Infix "<?"  := Rltb : R_scope.
Infix ">?"  := (fun x y => y <? x) : R_scope.
Infix ">=?" := (fun x y => y <=? x) : R_scope.

Lemma Reqb_true : forall x y, x =? y = true <-> x = y.
Proof. apply Acmpb_true. Qed.

Lemma Reqb_false : forall x y, x =? y = false <-> x <> y.
Proof. apply Acmpb_false. Qed.
    
Lemma Reqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros. unfold Reqb,Acmpb. destruct dec; constructor; auto.
Qed.
#[export] Hint Resolve Reqb_reflect : bdestruct.

Lemma Reqb_refl : forall r, r =? r = true.
Proof. intros. unfold Reqb,Acmpb. destruct dec; auto. Qed.

Lemma Reqb_comm : forall r1 r2, (r1 =? r2) = (r2 =? r1).
Proof. intros. unfold Reqb,Acmpb. destruct dec,dec; auto. lra. Qed.

Lemma Reqb_trans : forall r1 r2 r3, r1 =? r2 = true ->
  r2 =? r3 = true -> r1 =? r3 = true.
Proof. intros. unfold Reqb,Acmpb in *. destruct dec,dec,dec; auto. lra. Qed.

Lemma Rltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof. intros. unfold Rltb,Acmpb in *. destruct dec; auto; constructor; lra. Qed.
#[export] Hint Resolve Rltb_reflect : bdestruct.

Lemma Rleb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof. intros. unfold Rleb,Acmpb in *. destruct dec; auto; constructor; lra. Qed.
#[export] Hint Resolve Rleb_reflect : bdestruct.

(* x <=? x = true *)
Lemma Rleb_refl : forall x : R, x <=? x = true.
Proof. intros. bdestruct (x <=? x); ra. Qed.

(* (x <=? - y) = (-x >=? y) *)
Lemma Rleb_opp_r : forall x y : R, (x <=? - y) = (- x >=? y).
Proof. intros. bdestruct (x <=? -y); bdestruct (-x >=? y); ra. Qed.

(* (- x <=? y) = (x >=? - y) *)
Lemma Rleb_opp_l : forall x y : R, (- x <=? y) = (x >=? - y).
Proof. intros. bdestruct (- x <=? y); bdestruct (x >=? -y); ra. Qed.

(** (a - b <? 0) = (0 <? b - a) *)
Lemma Rminus_ltb0_comm : forall a b : R, (a - b <? 0) = (0 <? b - a).
Proof. intros. unfold Rltb,Acmpb. destruct dec,dec; auto; lra. Qed.
  
(** (a - b >? 0) = (0 >? b - a) *)
Lemma Rminus_gtb0_comm : forall a b : R, (a - b >? 0) = (0 >? b - a).
Proof. intros. unfold Rltb,Acmpb. destruct dec,dec; auto; lra. Qed.


(* ######################################################################### *)
(** * Suplymentary properties about "real number R" *)

(* ======================================================================= *)
(** ** Rsqr, Rpow2, x*x *)

(** There are several ways to represent square:

    For example, write sqrt of x has multiple ways:
    x * x
    x²
    Rsqr x
    Rmult x x
    x ^ 2
    pow x 2

    x * x，it is a notation for "Rmult x x"
    x ^ 2, it is a notation for "pow x 2"
    x²   , it is a notation for "Rsqr x", which defined as x * x.
    In Coq-std-lib, I should use which one to representing square? What's the 
    famous way? After the search, I find that:
        x * x，9
        x ^ 2, 14
        x², 100
    So, we should mainly use x², and other ways should be converted to this way,
    and the lost lemmas should be given manually.

    Another question, the lra tactic is working well on "x * x" and "pow x 2",
    but not working on "x²".
    So, we use "try (unfold Rsqr in *; lra)" insead of "try lra".
    In addition, using the tactics ring and field also need to unfold Rsqr.

    In conclusion, there are two cases:
    1. when use "ring,field,lra", write: unfold Rsqr in *; ring.
    2. other cases, write: autorewrite with R; auto with R.
 *)

(** We always prefer x², an exception is when using ring or field tactic. *)
Lemma xx_Rsqr x : x * x = x².
Proof. auto. Qed.
#[export] Hint Rewrite xx_Rsqr : R.

(** r ^ 2 = r² *)
Lemma Rpow2_Rsqr r : r ^ 2 = r².
Proof. ra. Qed.
#[export] Hint Rewrite Rpow2_Rsqr : R.

(** r ^ 4 = (r²)² *)
Lemma Rpow4_Rsqr_Rsqr r : r ^ 4 = r²².
Proof. ra. Qed.
#[export] Hint Rewrite Rpow4_Rsqr_Rsqr : R.

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
Proof. intros. replace x with (- -x)%R; ra. Qed.


(* ======================================================================= *)
(** ** About R0 and 0 *)

(* (** We always prefer 0 *) *)
(* Lemma R0_eq_0 : R0 = 0. *)
(* Proof. *)
(*   auto. *)
(* Qed. *)
(* #[export] Hint Rewrite R0_eq_0 : R. *)

Lemma Rsqr_R0 : R0² = R0.
Proof.
  ra.
Qed.
#[export] Hint Rewrite Rsqr_R0 : R.
Global Hint Resolve Rsqr_R0 : R.

Lemma Rplus_eq0_if_both0 : forall a b : R, a = 0 -> b = 0 -> a + b = 0.
Proof. intros. subst. lra. Qed.


(* ======================================================================= *)
(** ** About R1 and 1 *)

(* (** We always prefer 1 *) *)
(* Lemma R1_eq_1 : R1 = 1. *)
(* Proof. *)
(*   auto. *)
(* Qed. *)
(* #[export] Hint Rewrite R1_eq_1 : R. *)

(** (R1)² = 1 *)
Lemma Rsqr_R1 : (R1)² = 1.
Proof. ra. Qed.

(** 0 <= 1 *)
Lemma zero_le_1 : 0 <= 1.
Proof. auto with R. Qed.

(** 0 <> 1 *)
Lemma zero_neq_1 : 0 <> 1.
Proof. auto with R. Qed.

(** / R1 = 1 *)
Lemma Rinv_R1 : / R1 = 1.
Proof. ra. Qed.

(** a / 1 = a *)
Lemma Rdiv_1 : forall a, a / 1 = a.
Proof. ra. Qed.

(** 0 / a = 0 *)
Lemma Rdiv_0_eq0 : forall a : R, a <> 0 -> 0 / a = 0.
Proof. intros. field; auto. Qed.

#[export] Hint Rewrite
  Rsqr_R1           (* (R1)² = 1 *)
  Rinv_1            (* / 1 = 1 *)
  Rinv_R1           (* / R1 = 1 *)
  Rdiv_1            (* a / 1 = 1 *)
  Rdiv_0_eq0        (* 0 / a = 0 *)
  : R.

#[export] Hint Resolve
  Rsqr_R1           (* (R1)² = 1 *)
  Rinv_1            (* / 1 = 1 *)
  zero_le_1         (* 0 <= 1 *)
  zero_neq_1        (* 0 <> 1 *)
  : R.

Module TEST_R1_and_1.
  Goal 1 = R1. auto with R. Qed.
  Goal R1² = 1. auto with R. Qed.
  Goal 1² = R1. auto with R. Qed.
  Goal /R1 = R1. auto with R. Qed.
  Goal /R1 = 1. auto with R. Qed.
  Goal /1 = R1. auto with R. Qed.
  Goal 0 <= R1. auto with R. Qed.
End TEST_R1_and_1.


(* ======================================================================= *)
(** ** About "-a" and "a-b" *)

Lemma Rsub_opp r1 r2 : r1 - (- r2) = r1 + r2.
Proof.
  ring.
Qed.
#[export] Hint Rewrite Rsub_opp : R.           (* r1 - (- r2) = r1 + r2 *)

Lemma Rsqr_opp : forall r : R, (- r)² = r ².
Proof. intros. rewrite <- Rsqr_neg. auto. Qed.

Lemma Ropp_Rmul_Ropp_l : forall (r : R), - ((- r) * r) = r².
Proof. intros. cbv. ring. Qed.

Lemma Ropp_Rmul_Ropp_r : forall (r : R), - (r * (- r)) = r².
Proof. intros. cbv. ring. Qed.

Lemma Rmult_neg1_l : forall r : R, (- 1) * r = - r.
Proof. intros. lra. Qed.

Lemma Rmult_neg1_r : forall r : R, r * (- 1) = - r.
Proof. intros. lra. Qed.

#[export] Hint Rewrite
  (* Ropp_Rmul_Ropp_l            (* - ((-r) * r) = r² *) *)
  (* Ropp_Rmul_Ropp_r            (* - (r * (-r)) = r² *) *)
  Rsqr_opp                    (* (-r)² = r² *)
  Ropp_mult_distr_l_reverse   (* - r1 * r2 = - (r1 * r2) *)
  Ropp_mult_distr_r_reverse   (* r1 * - r2 = - (r1 * r2) *)
  Rdiv_opp_l                  (* - x / y = - (x / y) *)
  Rdiv_opp_r                  (* x / - y = - (x / y) *)
  Rmult_neg1_l                (* (-1) * r = -r *)
  Rmult_neg1_r                (* r * (-1) = -r *)
  : R.


(* ======================================================================= *)
(** ** About "/a" and "a/b" *)

Lemma Rinv_ab_simpl_a : forall r1 r2 r3,
    r1 <> 0 -> r3 <> 0 -> (r1 * r2) * / (r1 * r3) = r2 * / r3.
Proof. intros. field; auto. Qed.

Lemma Rinv_ab_simpl_b : forall r1 r2 r3,
    r2 <> 0 -> r3 <> 0 -> (r1 * r2) * / (r3 * r2) = r1 * / r3.
Proof. intros. field; auto. Qed.

Lemma Rdiv_1_neq_0_compat : forall r : R, r <> 0 -> 1 / r <> 0.
Proof. intros. pose proof (Rinv_neq_0_compat r H). ra. Qed.

#[export] Hint Rewrite
  Rinv_ab_simpl_a       (* (r1 * r2) * / (r1 * r3) = r2 * / r3 *)
  Rinv_ab_simpl_b       (* (r1 * r2) * / (r3 * r2) = r1 * / r3 *)
  : R.


(* ======================================================================= *)
(** ** About "square" *)

(* -------------------------------------------- *)
(** *** r * r *)
Lemma Rsqr_ge0 : forall r, 0 <= r * r.
Proof. ra. Qed.

(* -------------------------------------------- *)
(** *** r1² + r2² *)

(** r1² + r2² = 0 <-> r1 = 0 /\ r2 = 0 *)
Lemma Rplus2_sqr_eq0 : forall r1 r2, r1² + r2² = 0 <-> r1 = 0 /\ r2 = 0.
Proof. ra. Qed.

(* Lemma Rplus2_sqr_eq0' : forall r1 r2, r1 * r1 + r2 * r2 = 0 <-> r1 = 0 /\ r2 = 0. *)
(* Proof. ra. Qed. *)

(** r1² + r2² = 0 -> r1 = 0 *)
Lemma Rplus2_sqr_eq0_l : forall r1 r2, r1² + r2² = 0 -> r1 = 0.
Proof. ra. Qed.

(** r1² + r2² = 0 -> r2 = 0 *)
Lemma Rplus2_sqr_eq0_r : forall r1 r2, r1² + r2² = 0 -> r2 = 0.
Proof. ra. Qed.

(** r1² + r2² <> 0 <-> r1 <> 0 \/ r2 <> 0 *)
Lemma Rplus2_sqr_neq0 : forall r1 r2, r1² + r2² <> 0 <-> r1 <> 0 \/ r2 <> 0.
Proof. ra. Qed.

(** r1*r1 + r2*r2 <> 0 -> 0 < r1*r1 + r2*r2 *)
Lemma Rplus2_sqr_neq0_iff_gt0 : forall r1 r2 : R,
  r1² + r2² <> 0 <-> 0 < r1² + r2².
Proof. ra. Qed.

(** 2 * a * b <= a² + b² *)
Lemma R_neq1 : forall r1 r2 : R, 2 * r1 * r2 <= r1² + r2².
Proof. intros. apply Rge_le. apply Rminus_ge. rewrite <- Rsqr_minus. auto with R. Qed.

(** 0 <= r1² + r2² *)
Lemma Rplus2_sqr_ge0 : forall r1 r2 : R, 0 <= r1² + r2².
Proof. ra. Qed.

(* Lemma Rplus2_sqr_ge0' : forall r1 r2 : R, 0 <= r1 * r1 + r2 * r2. *)
(* Proof. ra. Qed. *)

(** 0 < r1² + r2² <-> (r1 <> 0 \/ r2 <> 0) *)
Lemma Rplus2_sqr_gt0 : forall r1 r2 : R, 0 < r1² + r2² <-> (r1 <> 0 \/ r2 <> 0).
Proof. ra. Qed.

(** r1 <> 0 -> 0 < r1² + r2² *)
Lemma Rplus2_sqr_gt0_l : forall r1 r2, r1 <> 0 -> 0 < r1² + r2².
Proof. ra. Qed.

(** r2 <> 0 -> 0 < r1² + r2² *)
Lemma Rplus2_sqr_gt0_r : forall r1 r2, r2 <> 0 -> 0 < r1² + r2².
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

Global Hint Resolve
  Rsqr_ge0             (* 0 <= x * x *)
  Rplus2_sqr_eq0       (* r1² + r2² = 0 <-> r1 = 0 /\ r2 = 0 *)
  Rplus2_sqr_eq0_l     (* r1² + r2² = 0 -> r1 = 0 *)
  Rplus2_sqr_eq0_r     (* r1² + r2² = 0 -> r2 = 0 *)
  Rplus2_sqr_neq0         (* r1² + r2²<>0 <-> r1<>0 \/ r2<>0*)
  Rplus2_sqr_neq0_iff_gt0 (* r1² + r2²<>0 <-> 0 <r1² + r2² *)
  Rplus2_sqr_ge0       (* 0 <= r1² + r2² *)
  Rplus2_sqr_gt0       (* 0 < r1² + r2² *)
  Rplus3_sqr_eq0       (* r1,r2,r3, ... *)
  Rplus3_sqr_neq0      (* r1,r2,r3, ... *)
  Rplus4_sqr_eq0       (* r1,r2,r3,r4 ... *)
  Rplus4_sqr_neq0      (* r1,r2,r3,r4 ... *)
  R_neq1               (* 2 * a * b <= a² + b² *)
  : R.

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


(* ======================================================================= *)
(** ** About "absolute value" *)

Notation "| r |" := (Rabs r) : R_scope.

Lemma Rabs_neg_left : forall r, 0 <= r -> | -r | = r.
Proof.
  intros. rewrite Rabs_Ropp. apply Rabs_right; nra.
Qed.

Lemma Rabs_neg_right : forall r, r < 0 -> | -r| = -r.
Proof.
  intros. rewrite Rabs_Ropp. apply Rabs_left; nra.
Qed.

Global Hint Resolve
  Rabs_right     (* r >= 0 -> |r| = r *)
  Rabs_pos_eq    (* 0 <= r -> |r| = r *)
  Rabs_left      (* r < 0 -> |r| = - r *)
  Rabs_left1     (* r <= 0 -> |r| = - r *)
  Rabs_neg_left  (* 0 <= r -> |-r| = r *)
  Rabs_neg_right (* r < 0 -> |-r| = -r *)
  : R.



(* ======================================================================= *)
(** ** About "sqrt" *)

(** sqrt (r * r) = |r| *)
Lemma sqrt_square_abs : forall r, sqrt (r * r) = |r|.
Proof.
  intros. destruct (Rcase_abs r).
  - replace (r * r) with ((-r) * (-r)) by nra.
    rewrite sqrt_square; try nra. auto with R.
  - rewrite sqrt_square; auto with R.
Qed.

Lemma sqrt_1 : sqrt 1 = 1.
Proof.
  apply Rsqr_inj; autorewrite with R; auto with R.
Qed.

Lemma sqrt_0_eq0 : forall r, r = 0 -> sqrt r = 0.
Proof. intros. rewrite H. ra. Qed.
  
Lemma sqrt_le0_eq_0 : forall r, r <= 0 -> sqrt r = 0.
Proof.
  intros. Transparent sqrt. unfold sqrt. destruct (Rcase_abs r); auto.
  assert (r = 0); try lra. subst. compute. 
  destruct (Rsqrt_exists). destruct a.
  symmetry in H1. auto with R.
Qed.

Lemma sqrt_lt0_eq_0 : forall r, r < 0 -> sqrt r = 0.
Proof.
  intros. apply sqrt_le0_eq_0. auto with R.
Qed.

Lemma sqrt_gt0_imply_gt0 : forall (x : R), 0 < sqrt x -> 0 < x.
Proof.
  intros. replace 0 with (sqrt 0) in H; auto with R.
  apply sqrt_lt_0_alt in H; auto.
Qed.

Lemma sqrt_gt0_imply_ge0 : forall (x : R), 0 < sqrt x -> 0 <= x.
Proof.
  intros. apply Rlt_le. apply sqrt_gt0_imply_gt0; auto.
Qed.

Lemma sqrt_eq1_imply_eq1 : forall (x : R), sqrt x = 1 -> x = 1.
Proof.
  intros.
  assert ((sqrt x)² = 1). rewrite H. autounfold with R in *; ring.
  rewrite <- H0.
  apply eq_sym. apply Rsqr_sqrt.
  assert (0 < sqrt x). rewrite H; auto with R.
  apply sqrt_gt0_imply_gt0 in H1. auto with R.
Qed.

Lemma sqrt_eq1_iff : forall (x : R), sqrt x = 1 <-> x = 1.
Proof.
  intros. split; intros.
  - apply sqrt_eq1_imply_eq1; auto.
  - subst. rewrite sqrt_1; auto.
Qed.

(** sqrt x = 0 <-> x <= 0 *)
Lemma sqrt_eq0_iff : forall r, sqrt r = 0 <-> r <= 0.
Proof.
  intros. split; intros.
  - bdestruct (r <=? 0); ra.
    apply Rnot_le_lt in H0. apply sqrt_lt_R0 in H0. ra.
  - apply sqrt_neg_0; auto.
Qed.

(** sqrt x <> 0 <-> x > 0 *)
Lemma sqrt_neq0_iff : forall r, sqrt r <> 0 <-> r > 0.
Proof.
  intros. split; intros; ra.
  bdestruct (r =? 0). subst. autorewrite with R in H. ra.
  bdestruct (r <? 0); ra. apply sqrt_lt0_eq_0 in H1. ra.
Qed.

(** ( √ r1 * √ r2)^2 = r1 * r2 *)
Lemma Rsqr_sqrt_sqrt r1 r2 : 0 <= r1 -> 0 <= r2 ->
  ((sqrt r1) * (sqrt r2))² = r1 * r2.
Proof.
  destruct (Rcase_abs r1), (Rcase_abs r2); try lra.
  autorewrite with R; auto with R.
  autorewrite with sqrt; ra.
Qed.

(** If the sqrt of the sum of squares of two real numbers equal to 0, iff both of 
    them are 0. *)
Lemma Rsqrt_plus_sqr_eq0_iff : forall r1 r2 : R,
  sqrt (r1² + r2²) = 0 <-> r1 = 0 /\ r2 = 0.
Proof.
  intros. autorewrite with R. split; intros H.
  - apply sqrt_eq_0 in H; ra.
  - destruct H; subst. autorewrite with R; auto with R.
Qed.

(** The multiplication of the square roots of two real numbers is >= 0 *)
Lemma Rmult_sqrt_sqrt_ge0 : forall r1 r2 : R, 0 <= (sqrt r1) * (sqrt r2).
Proof.
  intros. apply Rmult_le_pos; auto with R.
Qed.

(** The addition of the square roots of two real numbers is >= 0 *)
Lemma Rplus_sqrt_sqrt_ge0 : forall r1 r2 : R, 0 <= (sqrt r1) + (sqrt r2).
Proof.
  intros. apply Rplus_le_le_0_compat; auto with R.
Qed.

Lemma Rsqr_plus_sqr_neq0_l : forall r1 r2, r1 <> 0 -> sqrt (r1² + r2²) <> 0.
Proof.
  intros. auto 6 with R.
Qed.

Lemma Rsqr_plus_sqr_neq0_r : forall r1 r2, r2 <> 0 -> sqrt (r1² + r2²) <> 0.
Proof.
  intros. auto 6 with R.
Qed.

(** /(sqrt (1+(b/a)²)) = abs(a) / sqrt(a*a + b*b) *)
Lemma Rinv_sqrt_plus_1_sqr_div_a_b (a b : R) : a <> 0 ->
  (/ (sqrt (1+(b/a)²)) = |a| / sqrt(a*a + b*b)).
Proof.
  intros.
  replace (1 + (b/a)²) with ((a*a + b*b) / (|a|*|a|)).
  - rewrite sqrt_div_alt.
    + rewrite sqrt_square. 
      * field. split; autorewrite with R; auto 6 with R.
      * auto with R.
    + autorewrite with R; auto with R.
  - unfold Rsqr.
    destruct (Rcase_abs a).
    + replace (|a|) with (-a). field; auto. rewrite Rabs_left; auto.
    + replace (|a|) with a. field; auto. rewrite Rabs_right; auto.
Qed.

(** (√ r1 * √ r2) * (√ r1 * √ r2) = r1 * r2 *)
Lemma sqrt_mult_sqrt : forall (r1 r2 : R), 
  0 <= r1 -> 0 <= r2 ->
  ((sqrt r1) * (sqrt r2)) * ((sqrt r1) * (sqrt r2)) = r1 * r2.
Proof.
  intros. ring_simplify. repeat rewrite pow2_sqrt; auto.
Qed.


#[export] Hint Rewrite
  sqrt_square_abs         (* sqrt (r * r) = |r| *)
  (* Rsqr_sqrt               (* 0 <= x -> (sqrt x)² = x *) *)
  sqrt_1                  (* sqrt 1 = 1 *)
  Rsqr_sqrt_sqrt          (* ( √ r1 * √ r2)² = r1 * r2 *)
  sqrt_mult_sqrt          (* (√ r1 * √ r2) * (√ r1 * √ r2) = r1 * r2 *)
  : R.

Global Hint Resolve
  sqrt_1                  (* sqrt 1 = 1 *)
  sqrt_le0_eq_0           (* r <= 0 -> sqrt r = 0 *)
  sqrt_lt0_eq_0           (* r < 0 -> sqrt r = 0 *)
  sqrt_gt0_imply_gt0      (* 0 < sqrt x -> 0 < x *)
  sqrt_gt0_imply_ge0      (* 0 < sqrt x -> 0 <= x *)
  sqrt_eq1_imply_eq1      (* sqrt x = 1 -> x = 1 *)
  Rsqr_sqrt_sqrt          (* ( √ r1 * √ r2)² = r1 * r2 *)
  sqrt_mult_sqrt          (* (√ r1 * √ r2) * (√ r1 * √ r2) = r1 * r2 *)
  Rmult_sqrt_sqrt_ge0     (* 0 <= (sqrt r1) * (sqrt r2) *)
  Rplus_sqrt_sqrt_ge0     (* 0 <= (sqrt r1) + (sqrt r2) *)
  sqrt_square             (* 0 <= x -> sqrt (x * x) = x *)
  Rsqr_plus_sqr_neq0_l    (* r1 <> 0 -> sqrt (r1² + r2²) <> 0 *)
  Rsqr_plus_sqr_neq0_r    (* r2 <> 0 -> sqrt (r1² + r2²) <> 0 *)
  : R.

(** simplify expression has sqrt and pow2 *)
Ltac simpl_sqrt_pow2 :=
  repeat (
  (* (_²) -> x * x *)
  unfold Rsqr;
  (* (sqrt r1 * sqrt r2)^2 = r1 * r2 *)
  try rewrite sqrt_mult_sqrt;
  (* (sqrt x) ^ 2 = x *)
  try rewrite pow2_sqrt;
  (* sqrt (x ^ 2) = x *)
  try rewrite sqrt_pow2;
  (* (sqrt x * sqrt x) = x *)
  try rewrite sqrt_sqrt
  ).

Section TEST_Rsqrt.
  Goal sqrt R1 = R1. autorewrite with R; auto with R. Qed.
  
End TEST_Rsqrt.

(** Automatically prove the goal such as "sqrt x = y" *)
Ltac solve_sqrt_eq :=
  match goal with
  | |- sqrt ?x = ?y => apply Rsqr_inj; [ra|ra|rewrite Rsqr_sqrt;ra]
  end.


(* ======================================================================= *)
(** ** About "trigonometric functions" *)

(** sin R0 = 0 *)
Lemma sin_R0 : sin R0 = 0.
Proof. pose proof sin_0. ra. Qed.

(** cos R0 = 1 *)
Lemma cos_R0 : cos R0 = 1.
Proof. pose proof cos_0. ra. Qed.

(*  sin (- (PI/2)) = -1 *)
Lemma sin_PI2_neg : sin (- (PI/2)) = -1.
Proof.
  rewrite sin_neg. rewrite sin_PI2. auto.
Qed.

(* cos (- (PI/2)) = 0 *)
Lemma cos_PI2_neg : cos (- (PI/2)) = 0.
Proof.
  rewrite cos_neg. apply cos_PI2.
Qed.

(* sin (r + PI) = - (sin r) *)
Lemma sin_plus_PI : forall r, sin (r + PI) = (- (sin r))%R.
Proof.
  apply neg_sin.
Qed.

(* sin (r - PI) = - (sin r) *)
Lemma sin_sub_PI : forall r, sin (r - PI) = (- (sin r))%R.
Proof.
  intros. replace (r - PI)%R with (- (PI - r))%R; try ring.
  rewrite sin_neg. rewrite Rtrigo_facts.sin_pi_minus. auto.
Qed.

(* cos (r + PI) = - (cos r) *)
Lemma cos_plus_PI : forall r, cos (r + PI) = (- (cos r))%R.
Proof.
  apply neg_cos.
Qed.

(* cos (r - PI) = - (cos r) *)
Lemma cos_sub_PI : forall r, cos (r - PI) = (- (cos r))%R.
Proof.
  intros. replace (r - PI)%R with (- (PI - r))%R; try ring.
  rewrite cos_neg. apply Rtrigo_facts.cos_pi_minus.
Qed.

(* (cos x)² + (sin x)² = 1 *)
Lemma cos2_sin2: forall x : R, (cos x)² + (sin x)² = 1.
Proof.
  intros. rewrite Rplus_comm. apply sin2_cos2.
Qed.

Lemma cos2' : forall x : R, (cos x) ^ 2 = (1 - (sin x) ^ 2)%R.
Proof. intros. autorewrite with R. rewrite cos2. auto. Qed.

Lemma sin2' : forall x : R, (sin x) ^ 2 = (1 - (cos x) ^ 2)%R.
Proof. intros. autorewrite with R. rewrite sin2. auto. Qed.

(* sin r * / cos r = tan r *)
Lemma Rtan_rw : forall r : R, sin r * / cos r = tan r.
Proof. auto. Qed.

(* - PI / 2 < r < PI / 2 -> cos r <> 0 *)
Lemma cos_neg0 : forall r : R, - PI / 2 < r < PI / 2 -> cos r <> 0.
Proof. intros. assert (0 < cos r). { apply cos_gt_0; ra. } ra. Qed.

#[export] Hint Rewrite
  sin_0         (* sin 0 = 0 *)
  sin_R0        (* sin R0 = 0 *)
  cos_0         (* cos 0 = 1 *)
  cos_R0        (* cos R0 = 1 *)
  sin_PI        (* sin PI = 0 *)
  cos_PI        (* cos PI = -1 *)
  sin_PI2       (* sin (PI / 2) = 1 *)
  cos_PI2       (* cos (PI / 2) = 0 *)
  sin_PI2_neg   (* sin (- (PI/2)) = -1 *)
  cos_PI2_neg   (* cos (- (PI/2)) = 0 *)
  sin_plus_PI   (* sin (r + PI) = - (sin r) *)
  sin_sub_PI    (* sin (r - PI) = - (sin r) *)
  cos_plus_PI   (* cos (r + PI) = - (cos r) *)
  cos_sub_PI    (* cos (r - PI) = - (cos r) *)
  sin2_cos2     (* (sin x)² + (cos x)² = 1 *)
  cos2_sin2     (* (cos x)² + (sin x)² = 1 *)
  cos_plus      (* cos (x + y) = cos x * cos y - sin x * sin y *)
  cos_minus     (* cos (x - y) = cos x * cos y + sin x * sin y *)
  sin_plus      (* sin (x + y) = sin x * cos y + cos x * sin y *)
  sin_minus     (* sin (x - y) = sin x * cos y - cos x * sin y *)
  cos_neg       (* cos (- x) = cos x *)
  sin_neg       (* sin (- x) = - sin x *)
  Rtan_rw       (* sin r * / cos r = tan r *)
  atan_tan      (* atan (tan x) = x *)
  asin_sin      (* asin (sin x) = x *)
  acos_cos      (* acos (cos x) = x *)
  asin_opp      (* asin (-x) = - asin x *)
  acos_opp      (* acos (-x) = PI - acos x *)
  atan_opp      (* atan (-x) = - atan x *)
  : R.

#[export] Hint Resolve
  sin_0         (* sin 0 = 0 *)
  sin_R0        (* sin R0 = 0 *)
  cos_0         (* cos 0 = 1 *)
  cos_R0        (* cos R0 = 1 *)
  sin_PI        (* sin PI = 0 *)
  cos_PI        (* cos PI = -1 *)
  sin_PI2       (* sin (PI / 2) = 1 *)
  cos_PI2       (* cos (PI / 2) = 0 *)
  sin_PI2_neg   (* sin (- (PI/2)) = -1 *)
  cos_PI2_neg   (* cos (- (PI/2)) = 0 *)
  sin_plus_PI   (* sin (r + PI) = - (sin r) *)
  sin_sub_PI    (* sin (r - PI) = - (sin r) *)
  cos_plus_PI   (* cos (r + PI) = - (cos r) *)
  cos_sub_PI    (* cos (r - PI) = - (cos r) *)
  sin2_cos2     (* (sin x)² + (cos x)² = 1 *)
  cos2_sin2     (* (cos x)² + (sin x)² = 1 *)
  cos_neg       (* cos (- x) = cos x *)
  sin_neg       (* sin (- x) = - sin x *)
  cos_neg0      (* - PI / 2 < r < PI / 2 -> cos r <> 0 *)
  : R.

Section TEST_sin_cos_tan.
  Goal forall x, cos x * cos x + sin x * sin x = R1.
  intros; autorewrite with R; auto with R. Qed.
  
  Goal forall x, sin x * sin x + cos x * cos x = R1.
  intros; autorewrite with R; auto with R. Qed.

End TEST_sin_cos_tan.


(* ======================================================================= *)
(** ** About "Rpower" *)

(**
Rpower rules:
<<
  1. Definition of Rpower
  a^n       = a * a * ... * a    (* there are n numbers *)
  a^0       = 1 (a ≠ 0)
  a^(-n)    = 1 / a^n (a ≠ 0)
  a^(m/n)   = n√ a^m  (a > 0)
  a^(-m/n)  = 1 / n√ a^m  (a > 0)
>>
 *)
Lemma Rpower_neq0 x y : x <> 0 -> Rpower x y <> 0.
Proof.
  Abort.


(* ######################################################################### *)
(** * Automatic solving equalites or inequalities on real numbers *)

(* ======================================================================= *)
(** ** r = 0 *)

Lemma Rmult_eq_self_imply_0_or_k1 : forall k x,
    k * x = x -> x = 0 \/ (x <> 0 /\ k = R1).
Proof. ra. Qed.

Lemma Rsqr_eq0_if0 : forall r, r = 0 -> r² = 0. ra. Qed.

Lemma Rmult_eq_reg_l_rev : forall r r1 r2 : R, r * r1 = r * r2 -> r1 <> r2 -> r = 0.
Proof. ra. Qed.

Lemma Rmult_eq_reg_r_rev : forall r r1 r2 : R, r1 * r = r2 * r -> r1 <> r2 -> r = 0.
Proof. ra. Qed.


(* ======================================================================= *)
(** ** 0 <= x *)

(** deprecated *)
(* Ltac zero_le := *)
(*   intros; autorewrite with R; *)
(*   repeat (match goal with *)
(*   | |- 0 <= ?r1 * ?r2 => apply Rmult_le_pos *)
(*   | |- _ => idtac *)
(*   end; *)
(*   auto with R; try lra). *)

Section TEST_zero_le.
  Goal forall r, 0 <= r * r. ra. Qed.
  Goal forall r, 0 <= r². ra. Qed.
  Goal forall r1 r2, 0 <= r1 * r1 + r2 * r2. ra. Qed.
  Goal forall r1 r2, 0 <= r1² + r2². ra. Qed.
  Goal forall r1 r2, 0 <= r1 * r1 + r2². ra. Qed.
  Goal forall r1 r2, 0 <= r1² + r2 * r2. ra. Qed.
  Goal forall r, 0 <= r -> 0 <= r * 5. ra. Qed.
  Goal forall r, 0 <= r -> 0 <= r * 5 * 10. ra. Qed.
  Goal forall r, 0 <= r -> 0 <= r * (/5) * 10. ra. Qed.
End TEST_zero_le.

(** a >= 0 -> b < 0 -> a / b <= 0 *)
Lemma Rdiv_ge0_lt0_le0 : forall a b : R, a >= 0 -> b < 0 -> a / b <= 0.
Proof. intros. unfold Rdiv. assert (/b<0); ra. Qed.

Lemma Rdiv_gt_0_compat_neg: forall a b : R, a < 0 -> b < 0 -> 0 < a / b.
Proof. intros. unfold Rdiv. assert (/b < 0); ra. Qed.

Lemma Rdiv_ge_0_compat: forall a b : R, 0 <= a -> 0 < b -> 0 <= a / b.
Proof. intros. unfold Rdiv. assert (0 < /b); ra. Qed.

(* 0 <= a * a *)
Lemma Rsqr_gt0 : forall a : R, 0 <= a * a.
Proof. intros. nra. Qed.

(** 0 <= a -> 0 <= b -> a + b = 0 -> b = 0 *)
Lemma Rplus_eq_0_r : forall a b : R, 0 <= a -> 0 <= b -> a + b = 0 -> b = 0.
Proof. intros. lra. Qed.
                                                    

Hint Resolve
  Rdiv_ge0_lt0_le0
  Rdiv_gt_0_compat_neg
  Rdiv_ge_0_compat
  : R.


(* ======================================================================= *)
(** ** 0 < x *)

(** deprecated *)
(* Ltac zero_lt := *)
(*   intros; autorewrite with R; *)
(*   match goal with *)
(*   | H : ?r1 <> 0 |- 0 < ?r1² + ?r2² => apply Rneq0_imply_Rplus_gt0_2_1 *)
(*   | H : ?r2 <> 0 |- 0 < ?r1² + ?r2² => apply Rneq0_imply_Rplus_gt0_2_2 *)
(*   | H : 0 < ?r1  |- 0 < ?r1² + ?r2² => apply Rgt0_imply_Rplus_gt0_2_1 *)
(*   | H : 0 < ?r2  |- 0 < ?r1² + ?r2² => apply Rgt0_imply_Rplus_gt0_2_2 *)
(*   | H : 0 < ?r1  |- 0 < ?r1 * ?r2 => apply Rmult_lt_0_compat *)
(*   (* these methods are too ugly, but could work now *) *)
(*   | |- (0 < ?r1 + ?r2)%R => apply Rplus_lt_0_compat *)
(*   | |- (0 < ?r1 * ?r2)%R => apply Rmult_lt_0_compat *)
(*   | |- (0 < ?r1²)%R => apply Rlt_0_sqr *)
(*   | |- _ => idtac *)
(*   end; *)
(*   auto with R; try lra. *)
  
Section TEST_zero_lt.
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
  
End TEST_zero_lt.

(** This property is used in in Complex. Although lra can solve it, but using a 
    special lemma name combined with the match machanism could speed up the proof. *)


(** a <> b -> a <= b -> a < b *)
Lemma Rneq_le_lt : forall a b, a <> b -> a <= b -> a < b.
Proof. ra. Qed.

(** 0 < r -> 0 < 1 / r *)
Lemma Rinv1_gt0 : forall r : R, 0 < r -> 0 < 1 / r.
Proof. cbv. ra. Qed.

(** 0 < a -> b < 0 -> a / b < 0 *)
Lemma Rdiv_lt_0_compat_l: forall a b : R, 0 < a -> b < 0 -> a / b < 0.
Proof. intros. unfold Rdiv. assert (/b < 0); ra. Qed.

(** a < 0 -> 0 < b -> a / b < 0 *)
Lemma Rdiv_lt_0_compat_r: forall a b : R, a < 0 -> 0 < b -> a / b < 0.
Proof. intros. unfold Rdiv. assert (/b > 0); ra. Qed.

#[export] Hint Resolve
  Rdiv_lt_0_compat_l
  Rdiv_lt_0_compat_r
  Rneq_le_lt
  Rinv1_gt0
  : R.


(* ======================================================================= *)
(** ** x <> 0 *)

(* (** deprecated *) *)
(* Ltac neq_zero := *)
(*   intros; autorewrite with R in *; *)
(*   repeat match goal with *)
(*   (* symmetry *) *)
(*   | H : 0 <> ?a |- ?b <> 0 => apply not_eq_sym in H *)
(*   | H : 0 <> ?a |- 0 <> ?b => apply not_eq_sym in H; apply not_eq_sym *)
(*   (* normal *) *)
(*   | _ : 0 < ?r |- ?r <> 0 => apply zero_lt_imply_Rneq0 *)
(*   | _ : ?r1 <> 0 |- ?r1² <> 0 => apply Rneq0_imply_Rsqr_neq0 *)
(*   | _ : ?r1² <> 0 |- ?r1 <> 0 => apply Rsqr_neq0_imply_Rneq0 *)
(*   | _ : ?r1 + ?r2 <> 0, _ : ?r1 = 0 |- ?r2 <> 0 =>  *)
(*     apply Rplus_neq0_imply_Rneq0_2_1 *)
(*   | _ : ?r1 + ?r2 <> 0, _ : ?r2 = 0 |- ?r1 <> 0 =>  *)
(*     apply Rplus_neq0_imply_Rneq0_2_2 *)
(*   (* default *) *)
(* (*   | |- ?b <> 0 => apply zero_lt_imply_Rneq0 *) *)
(*   | |- _ => idtac *)
(*   end; *)
(*   auto with R. *)

Section TEST_neq_zero.
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

End TEST_neq_zero.


(* ======================================================================= *)
(** ** a < b *)

Lemma Rdiv_le_imply_Rmul_gt a b c : b > 0 -> a * /b < c -> a < b * c.
Proof.
  intros.
  apply (Rmult_lt_compat_l b) in H0; auto.
  replace (b * (a * /b)) with a in H0; auto.
  field. auto with R.
Qed.
Global Hint Resolve Rdiv_le_imply_Rmul_gt : R.

Lemma Rmul_gt_imply_Rdiv_le a b c : b > 0 -> a < b * c -> a * /b < c.
Proof.
  intros.
  apply (Rmult_lt_compat_l (/b)) in H0; auto with R.
  autorewrite with R in *.
  replace (/b * a) with (a / b) in *; try field; auto with R.
  replace (/b * (b * c)) with c in *; try field; auto with R.
Qed.
Global Hint Resolve Rmul_gt_imply_Rdiv_le : R.


(* Note, Rlt_Rminus is deprecated since 8.19 *)
Lemma Rlt_Rminus : forall a b : R, a < b -> 0 < b - a.
Proof. intros. apply (proj2 (Rlt_0_minus a b)); auto. Qed.

(* Global Hint Resolve  *)
(*     Rminus_gt_0_lt  (* 0 < b - a -> a < b *) *)
(*     Rlt_Rminus      (* a < b -> 0 < b - a *) *)
(*     Rlt_minus       (* r1 < r2 -> r1 - r2 < 0 *) *)
(*     : R. *)
    
Ltac tac_le :=
  autounfold with R;
  match goal with
  | |- 0 < ?a + - ?b => apply Rlt_Rminus
  | |- ?a * (?b * /?c) < ?e => replace (a * (b * /c)) with ((a * b) * /c)
  | |- ?a * /?b < ?c => assert (a < b * c); assert (0 < b)
  | |- _ => idtac
  end; try lra; auto with R.
  
Section TEST_tac_le.

  (** This proof cannot be finished in one step *)
  Goal forall h T, 0 < h -> h < 9200 -> -60 < T -> T < 60 -> h / (273.15 + T) < 153.
    ra. Abort.

  (** Naming the hypothesises *)
  Variable h T : R.
  Hypothesis Hh1 : 0 < h.
  Hypothesis Hh2 : h < 9200.
  Hypothesis HT1 : -60 < T.
  Hypothesis HT2 : T < 60.

  (** a simpler proposition can be proved in one step *)
  Goal h * 0.0065 < 273.15 + T. ra. Qed.

  (** We can finish the original proof with manually help *)
  Goal h / (273.15 + T) < 153.
    autounfold with R.
    assert (273.15 + T > 0). ra.
    assert (h < (273.15 + T) * 153). ra. auto with R.
  Qed.

  (** Another example, also need to manually *)
  Goal h / (273.15 + T) < 1 / 0.0065.
  Proof.
    ra. (* can not finish it *)
    autounfold with R.
    assert (273.15 + T > 0). ra.
    assert (h < (273.15 + T) * (1/0.0065)). ra. auto with R.
  Qed.

  (* This example shows the usage of tac_le tactic *)
  Goal h / (273.15 + T) < 1 / 0.0065.
  Proof.
    tac_le.
  Qed.

  (** This example shows the usage of tac_le and ra together. *)
  Goal  0 < 1 - (0.0065 * (h * / (273.15 + T))).
  Proof.
    (* construct condition manually, then try to automate *)
    assert (h / (273.15 + T) < 1/0.0065).
    tac_le. ra.
  Qed.
  
  Goal 0 < 1 - (0.0065 * (h * / (273.15 + T))).
  Proof.
    do 3 tac_le.
  Qed.

End TEST_tac_le.

(* ======================================================================= *)
(** ** Examples which cannot automatically solved now *)

(** This example comes from a proof about Carg in Complex. *)
Goal forall a b r, a > 0 -> b <= r / a -> 0 <= r - b *a.
Proof.
  intros.
  ra. (* No effect *)
  apply Rmult_le_compat_r with (r:=a) in H0; ra.
  unfold Rdiv in H0. rewrite Rmult_assoc in H0.
  rewrite Rinv_l in H0; ra.
Qed.


(* ======================================================================= *)
(** ** Compare with PI *)
Section compare_with_PI.
  
  (** How to prove the inequalities about PI *)
  Goal 2 < PI.
  Proof.
  Abort.

  (** One method: give the upper and lower bound of PI with concrete
      value by axiom, then use transitivity to solve it by lra. *)
  Notation PI_ub := 3.14159266.
  Notation PI_lb := 3.14159265.
  
  Axiom PI_upper_bound : PI < PI_ub.
  Axiom PI_lower_bound : PI_lb < PI.
  
  Lemma PI_bound : PI_lb < PI < PI_ub.
  Proof. split. apply PI_lower_bound. apply PI_upper_bound. Qed.

  (* method 1: by transitivity *)
  Goal 2 < PI.
  Proof.
    apply Rlt_trans with PI_lb. lra. apply PI_bound.
  Abort.
  
  (* method 2: by lra directly *)
  Goal 2 < PI.
  Proof.
    pose proof PI_bound. lra.
  Abort.
  
End compare_with_PI.


(* ======================================================================= *)
(** ** OLD CODE EARLY, they should be carefuly CHECKED and then DISCARDED *)

(* (** a + b <> 0 *) *)
(* Ltac plus_neq0 := *)
(*   match goal with *)
(*   | |- ?a + ?b <> 0 => apply Rgt_not_eq,Rlt_gt,Rplus_lt_0_compat;  *)
(*     auto with R fcs *)
(*   end. *)

(* (** 0 < a *) *)
(* Ltac zero_lt := *)
(*   repeat match goal with *)
(*   (* 0 *) *)
(*   | H: ?a <> 0 |- 0 < ?a * ?a => apply Rlt_0_sqr; apply H *)
(*   | |- 0 < ?a + ?b => apply Rplus_lt_0_compat *)
(*   | |- 0 < ?a * ?b => apply Rmult_lt_0_compat *)
(*   | |- 0 < sqrt ?a => apply sqrt_lt_R0 *)
(*   | |- 0 < ?a / ?b => unfold Rdiv *)
(*   | |- 0 < / ?a => apply Rinv_0_lt_compat *)
(*   | |- 0 < ?a ^ _ => simpl *)
(*   | |- 0 < (?a)² => unfold Rsqr *)
(*   | |- 0 < ?a => auto with R fcs; try lra *)
(*   (* R0 *) *)
(*   | |- R0 < ?a * ?b => apply Rmult_lt_0_compat; try lra; auto with R fcs *)
(*   | |- R0 < sqrt ?a => apply sqrt_lt_R0 *)
(*   | |- R0 < ?a / ?b => unfold Rdiv *)
(*   | |- R0 < / ?a => apply Rinv_0_lt_compat *)
(*   | |- R0 < ?a ^ _ => simpl *)
(*   | |- R0 < (?a)² => unfold Rsqr *)
(*   | |- R0 < ?a => auto with R fcs; try lra *)
(*   end. *)


(* (** 0 <= a *) *)
(* Ltac zero_le := *)
(*   (* simplify sqrt+pow2 *) *)
(*   repeat ( *)
(*   try simpl_sqrt_pow2; *)
(*   try match goal with *)
(*   (* 0 <= sqrt x *) *)
(*   | |- 0 <= sqrt _ => apply sqrt_pos *)
(*   (* 0 <= a * a *) *)
(*   | |- 0 <= ?a * ?a => apply Rle_0_sqr *)
(*   (* 0 <= a -> 0 <= b -> 0 <= a + b *)  *)
(*   | |- 0 <= ?a + ?b => apply Rplus_le_le_0_compat *)
(*   (* 0 <= a -> 0 <= b -> 0 <= a * b *) *)
(*   | |- 0 <= ?a * ?b => apply Rmult_le_pos *)
(*   (* if fail, proof < again *) *)
(* (*   | |- 0 <= ?a => apply Rlt_le; zero_le *)
(*   | |- R0 <= ?a => apply Rlt_le; zero_le *) *)
(*   end). *)

(* (** a * b <> 0 *) *)
(* Ltac mult_neq0 := *)
(*   match goal with *)
(*   | |- ?a * ?b <> 0 => apply Rgt_not_eq,Rlt_gt;zero_le *)
(*   end. *)

(* (** a <> 0 *) *)
(* Ltac neq0 := *)
(*   repeat match goal with *)
(*   | |- ?a /\ ?b => repeat split *)
(*   | |- ?a <> 0 => apply Rgt_not_eq,Rlt_gt; zero_le *)
(*   end. *)


(** Simplification for trigonometric functions *)

(* Lemma xx_sqr : forall x:R, x * x = Rsqr x. *)
(* Proof. auto. Qed. *)

(* Lemma cos2_sin2' : forall x:R, Rsqr (cos x) + Rsqr (sin x) = 1. *)
(* Proof. intros. autorewrite with R. auto with R. Qed. *)

(* Lemma cos_sin : forall x:R, cos x * sin x = sin x * cos x. *)
(* Proof. ra. Qed. *)

(* Lemma x_neg_x : forall x:R, x + - x = 0. *)
(* Proof. ra. Qed. *)

(* Lemma neg_x_x : forall x:R, -x + x = 0. *)
(* Proof. intros. lra. Qed. *)

(* Lemma x_mul_neg_x : forall x y : R, y * -x = - (x * y). *)
(* Proof. intros. lra. Qed. *)

(* Lemma neg_x_mul_x : forall x y : R, -y * x = - (y * x). *)
(* Proof. intros. lra. Qed. *)

(* Lemma sqrR1_R1 : R1² = R1. *)
(* Proof. unfold Rsqr. ring. Qed. *)

(* Lemma one_R1 : 1 = R1. *)
(* Proof. ring. Qed. *)

(* Lemma inv1_R1 : /1 = R1. *)
(* Proof. field. Qed. *)

(* Lemma invR1_R1 : /R1 = R1. *)
(* Proof. field. Qed. *)

(* Lemma sqrtR1_R1 : sqrt R1 = R1. *)
(* Proof. apply Rsqr_inj. zero_le. lra. rewrite Rsqr_sqrt. *)
(*   rewrite sqrR1_R1. auto. lra. *)
(* Qed. *)

(* Lemma sqrt1_R1 : sqrt 1 = R1. *)
(* Proof. rewrite one_R1. apply sqrtR1_R1. Qed. *)

(* Lemma coscos_sinsin : forall x : R, (cos x * cos x + sin x * sin x) = 1. *)
(* Proof. intros. rewrite ?xx_sqr. rewrite ?cos2_sin2. auto. Qed. *)

(* Lemma sinsin_coscos : forall x : R, (sin x * sin x + cos x * cos x) = 1. *)
(* Proof. intros. rewrite ?xx_sqr. rewrite ?sin2_cos2. auto. Qed. *)

(* (** r1 - (-r2) = r1 + r2 *) *)
(* Lemma Rsub_Rneg : forall (r1 r2 : R), r1 - (- r2) = r1 + r2. *)
(* Proof. intros. ring. Qed. *)

(* (** Simplify trigonometric function and expression of real number *) *)
(* Ltac trigo_simp :=  *)
(*   rewrite ?Rmult_opp_opp;   (* -x * -x = x * x *) *)
(* (*   rewrite ?xx_sqr;          (* x * x = Rsqr x  *) *) *)
(*   rewrite ?Rsub_Rneg,       (* r1 - (-r2) = r1 + r2 *) *)
(*           ?sin2_cos2,       (* sin^2 + cos^2 = 1 *) *)
(*           ?cos2_sin2,       (* cos^2 + sin^2 = 1 *) *)
(*           ?coscos_sinsin,   (* cos*cos + sin*sin = 1 *) *)
(*           ?sinsin_coscos,   (* sin*sin + cos*cos = 1 *) *)
(*           ?cos_sin,         (* cos * sin = sin * cos *) *)
(*           ?x_mul_neg_x,     (* y * -x = - (x * y) *) *)
(*           ?neg_x_mul_x,     (* -y * x = - (x * y) *) *)
(*           ?x_neg_x,         (* x + -x = 0 *) *)
(*           ?neg_x_x,         (* -x + x = 0 *) *)
(*           ?sqrtR1_R1,       (* sqrt R1 = R1 *) *)
(*           ?sqrt1_R1,        (* sqrt 1 = 1 *) *)
(*           ?sqrR1_R1,        (* R1² = R1 *) *)
(* (*           ?Rinv_1,           (* /1 = 1 *) *) *)
(*           ?inv1_R1,         (* /1 = R1 *) *)
(*           ?invR1_R1,        (* /R1 = R1 *) *)
(*           ?one_R1           (* 1 = R1 *) *)
(*   ; *)
(*   autorewrite with R;       (* +0, 0+, *0, 0*, *1, 1* *) *)
(*   try field; *)
(*   auto. *)

(* (* sqrt x = R1 -> x = R1 *) *)
(* Lemma sqrt_eqR1_imply_R1 : forall (x : R), sqrt x = R1 -> x = R1. *)
(* Proof. *)
(*   intros. *)
(*   assert ((sqrt x)² = R1). rewrite H. unfold Rsqr. lra. rewrite <- H0. *)
(*   rewrite Rsqr_sqrt; auto. *)
(*   assert (0 < sqrt x). rewrite H. lra.  *)
(*   apply sqrt_gt0_imply_gt0 in H1. lra. *)
(* Qed. *)


(* ######################################################################### *)
(** ** Split a large range to small pieces *)

(** Split the range of (-π,π] to several small ranges *)
Section a_strange_problem.

  (** Tips: A strange problem about "lra":
      If I declare a condition here, the next proof will be finished by lra,
      otherwise, the next proof will not be done. *)
  Variable b: R.
  Hypotheses Hb : - PI < b < PI.

  Lemma Rsplit_neg_pi_to_pi' : forall a : R,
      -PI < a <= PI <->
        a = -PI/2 \/ a = 0 \/ a = PI/2 \/
          (-PI < a < -PI/2) \/ (-PI/2 < a < 0) \/
          (0 < a < PI/2) \/ (PI/2 < a <= PI).
  Proof.
    intros.
    (* Here, the automatic process is determined by the existence of "Hb", Why ?
       可能的原因，-PI < -PI/2 < PI 无法被lra证明，但有了 Hb 后就能证了，
       虽然 b 和 a 没有关系，但确实完成了证明。暂不知原理。
       
       同时，也发现了一个技巧，虽然 PI 不能被 lra 证明，但可以设定一个近似表示，比如
       “3.14 < PI < 3.15”，然后 lra 就能用了。

       主要原因还是关于 PI 的自动化程度优点低，可能需要某个触发条件。
     *)
    lra.
  Qed.
End a_strange_problem.

Lemma Rsplit_neg_pi_to_pi : forall a : R,
    -PI < a <= PI <->
      a = -PI/2 \/ a = 0 \/ a = PI/2 \/
        (-PI < a < -PI/2) \/ (-PI/2 < a < 0) \/
        (0 < a < PI/2) \/ (PI/2 < a <= PI).
Proof.
  intros.
  (* 引入 PI 的不等式，以便 lra 能够使用 *)
  pose proof PI_bound. lra.
Qed.


(* ######################################################################### *)
(** * atan *)

(** 背景：
    在 atan2 的证明中，经常需要化简形如 atan ((a * b) / (a * c)) 的式子 *)

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
  intros. bdestruct (x =? 0).
  - subst. rewrite atan_0; cbv; ra.
  - assert (x > 0); ra. pose proof (atan_bound_gt0 x H1); ra.
Qed.

(** -π/2 < atan x <= 0 *)
Lemma atan_bound_le0 : forall x, x <= 0 -> - PI / 2 < atan x <= 0.
Proof.
  intros. bdestruct (x =? 0).
  - subst. rewrite atan_0; cbv; ra. split; ra. assert (PI > 0); ra.
  - assert (x < 0); ra. pose proof (atan_bound_lt0 x H1); ra.
Qed.


(* ######################################################################### *)
(** * Conversion between R and other types *)

(** Remark:
    
    We need two functions commonly used in computer: floor (rounding down), and 
    ceiling (rounding up). Although the function "up" in Coq-std-lib is looks like
    a rounding up function, but it is a bit different. We need to explicitly 
    define them. Meanwhile, we tested their behaviors on negative numbers
    
    The behavior of "up" is this:
        2.0 <= r < 3.0 -> up(r) = 3,
    and there is a lemma saying this:
        Check archimed. (* IZR (up r) > r /\ IZR (up r) - r <= 1 *)

    But we need the behavior of floor and ceiling are these below exactly:
    1. floor
       2.0 <= r < 3.0 -> floor(r) = 2
       So, floor(r) = up(r) - 1
    2. ceiling
       2.0 < r < 3.0 -> ceiling(r) = 3
       r = 2.0 -> ceiling(r)=2
       So, if IZR(up(r))=r，then ceiling(r)=up(r)-1，else ceiling(r)=up(r).

    When talking about negative numbers, their behaviors are below:
    floor    2.0 = 2
    floor    2.5 = 2
    floor   -2.0 = -2
    floor   -2.5 = -3

    ceiling  2.0 = 2
    ceiling  2.5 = 3
    ceiling -2.0 = -2
    ceiling -2.5 = -2
 *)

(** ** Properties about up and IZR *)

(** Eliminate the up_IZR *)
Lemma up_IZR : forall z, up (IZR z) = (z + 1)%Z.
Proof.
  intros.
  rewrite up_tech with (r:=IZR z); auto; ra.
  apply IZR_lt. lia.
Qed.

(** There is a unique integer if such a IZR_up equation holds. *)
Lemma IZR_up_unique : forall r, r = IZR (up r - 1) -> exists! z, IZR z = r.
Proof.
  intros.
  exists (up r - 1)%Z. split; auto.
  intros. subst.
  rewrite up_IZR in *.
  apply eq_IZR. auto.
Qed.

(** There isn't any integer z and real number r such that r ∈(IZR z, IZR (z+1)) *)
Lemma IZR_in_range_imply_no_integer : forall r z,
    IZR z < r ->
    r < IZR (z + 1) ->
    ~(exists z', IZR z' = r).
Proof.
  intros. intro. destruct H1. subst.
  apply lt_IZR in H0.
  apply lt_IZR in H. lia.
Qed.


(* ######################################################################### *)
(** ** Conversion between R and other types *)

(** *** Conversion between Z and R *)

(** Z to R *)
Definition Z2R (z : Z) : R := IZR z.

(** Rounding R to z, take the floor: truncate to the nearest integer
    not greater than it *)
Definition R2Z_floor (r : R) : Z := (up r) - 1.

(** Rounding R to z, take the ceiling: truncate to the nearest integer 
    not less than it *)
Definition R2Z_ceiling (r : R) : Z :=
  let z := up r in
  if Req_EM_T r (IZR (z - 1)%Z)
  then z - 1
  else z.

(* Compute R2Z_floor 0.5 *)

(** z <= r < z+1.0 -> floor(r) = z *)
Lemma R2Z_floor_spec : forall r z,
    IZR z <= r < IZR z + 1.0 -> R2Z_floor r = z.
Proof.
  intros. unfold R2Z_floor in *. destruct H.
  assert (up r = z + 1)%Z; try lia.
  rewrite <- up_tech with (z:=z); auto.
  rewrite plus_IZR. lra.
Qed.

(** (r=z -> ceiling r = z) /\ (z < r < z + 1.0 -> ceiling r = z+1) *)
Lemma R2Z_ceiling_spec : forall r z,
    (r = IZR z -> R2Z_ceiling r = z) /\
      (IZR z < r < IZR z + 1.0 -> R2Z_ceiling r = (z+1)%Z).
Proof.
  intros. unfold R2Z_ceiling in *. split; intros.
  - destruct (Req_EM_T r (IZR (up r - 1))).
    + rewrite H. rewrite up_IZR. lia.
    + rewrite H in n. destruct n.
      rewrite up_IZR. f_equal. lia.
  - destruct H. destruct (Req_EM_T r (IZR (up r - 1))).
    + apply IZR_in_range_imply_no_integer in H; auto.
      * destruct H. exists (up r - 1)%Z; auto.
      * rewrite plus_IZR. ra.
    + rewrite up_tech with (r:=r); auto; ra.
      rewrite plus_IZR. ra.
Qed.

(** Z2R (R2Z_floor r) is less than r *)
Lemma Z2R_R2Z_floor_le : forall r, Z2R (R2Z_floor r) <= r.
Proof.
  intros. unfold Z2R,R2Z_floor. rewrite minus_IZR.
  destruct (archimed r). ra.
Qed.

(** r-1 is less than Z2R (R2Z_floor r) *)
Lemma Z2R_R2Z_floor_gt : forall r, r - 1 < Z2R (R2Z_floor r).
Proof.
  intros. unfold Z2R,R2Z_floor. rewrite minus_IZR.
  destruct (archimed r). ra.
Qed.

(** *** Conversion between nat and R *)

Definition nat2R (n : nat) : R := Z2R (nat2Z n).
Definition R2nat_floor (r : R) : nat := Z2nat (R2Z_floor r).
Definition R2nat_ceiling (r : R) : nat := Z2nat (R2Z_ceiling r).

(** *** Conversion from Q to R *)
Section Q2R.
  Import Rdefinitions.
  Import Qreals.
  Import QExt.
  
  (* Definition Q2R (x : Q) : R := Q2R x. *)

  Lemma Q2R_eq_iff : forall a b : Q, Q2R a = Q2R b <-> Qeq a b.
  Proof. intros. split; intros. apply eqR_Qeq; auto. apply Qeq_eqR; auto. Qed.

  Lemma Q2R_add : forall a b : Q, Q2R (a + b) = (Q2R a + Q2R b)%R.
  Proof. intros. apply Qreals.Q2R_plus. Qed.

End Q2R.


(** *** Conversion from Qc to R *)
Section Qc2R.
  Import Rdefinitions.
  Import Qreals.
  Import QcExt.

  Section QcExt_additional.
    
    Lemma this_Q2Qc_eq_Qred : forall a : Q, this (Q2Qc a) = Qred a.
    Proof. auto. Qed.

  End QcExt_additional.
  
  Definition Qc2R (x : Qc) : R := Q2R (Qc2Q x).

  Lemma Qc2R_add : forall a b : Qc, Qc2R (a + b) = (Qc2R a + Qc2R b)%R.
  Proof.
    intros. unfold Qc2R,Qc2Q. rewrite <- Q2R_add. apply Q2R_eq_iff.
    unfold Qcplus. rewrite this_Q2Qc_eq_Qred. apply Qred_correct.
  Qed.
  
  Lemma Qc2R_0 : Qc2R 0 = 0%R.
  Proof. intros. cbv. ring. Qed.
  
  Lemma Qc2R_opp : forall a : Qc, Qc2R (- a) = (- (Qc2R a))%R.
  Proof.
    intros. unfold Qc2R,Qc2Q. rewrite <- Q2R_opp. apply Q2R_eq_iff.
    unfold Qcopp. rewrite this_Q2Qc_eq_Qred. apply Qred_correct.
  Qed.
  
  Lemma Qc2R_mul : forall a b : Qc, Qc2R (a * b) = (Qc2R a * Qc2R b)%R.
  Proof.
    intros. unfold Qc2R,Qc2Q. rewrite <- Q2R_mult. apply Q2R_eq_iff.
    unfold Qcmult. rewrite this_Q2Qc_eq_Qred. apply Qred_correct.
  Qed.
  
  Lemma Qc2R_1 : Qc2R 1 = (1)%R.
  Proof. intros. cbv. field. Qed.
  
  Lemma Qc2R_inv : forall a : Qc, a <> 0 -> Qc2R (/ a) = (/ (Qc2R a))%R.
  Proof.
    intros. unfold Qc2R,Qc2Q. rewrite <- Q2R_inv. apply Q2R_eq_iff.
    unfold Qcinv. rewrite this_Q2Qc_eq_Qred. apply Qred_correct.
    intro. destruct H. apply Qc_is_canon. simpl. auto.
  Qed.
  
  Lemma Qc2R_eq_iff : forall a b : Qc, Qc2R a = Qc2R b <-> a = b.
  Proof.
    split; intros; subst; auto. unfold Qc2R, Qc2Q in H.
    apply Qc_is_canon. apply eqR_Qeq; auto.
  Qed.
  
  Lemma Qc2R_lt_iff : forall a b : Qc, (Qc2R a < Qc2R b)%R <-> a < b.
  Proof.
    intros. unfold Qc2R, Qc2Q,Qclt in *. split; intros.
    apply Rlt_Qlt; auto. apply Qlt_Rlt; auto.
  Qed.
  
  Lemma Qc2R_le_iff : forall a b : Qc, (Qc2R a <= Qc2R b)%R <-> a <= b.
  Proof.
    intros. unfold Qc2R, Qc2Q,Qclt in *. split; intros.
    apply Rle_Qle; auto. apply Qle_Rle; auto.
  Qed.

  #[export] Instance Qc_ConvertToR
    : ConvertToR Qcplus (0%Qc) Qcopp Qcmult (1%Qc) Qcinv Qclt Qcle Qcltb Qcleb Qc2R.
  Proof.
    constructor; intros.
    apply Qc2R_add. apply Qc2R_0. apply Qc2R_opp. apply Qc2R_mul. apply Qc2R_1.
    apply Qc2R_inv; auto. apply Qc_Order. apply Qc2R_eq_iff.
    apply Qc2R_lt_iff. apply Qc2R_le_iff.
  Qed.
  
End Qc2R.


(* ######################################################################### *)
(** * Approximate of two real numbers *)

(** r1 ≈ r2, that means |r1 - r2| <= diff *)
Definition Rapprox (r1 r2 diff : R) : Prop := |r1 - r2| <= diff.

(** boolean version of approximate function *)
Definition Rapproxb (r1 r2 diff : R) : bool := |r1 - r2| <=? diff.


(* ######################################################################### *)
(** * Mathematical Structure *)

(* ======================================================================= *)
(** ** Well-defined (or compatible, or proper morphism) of operations on R. *)

Lemma Rplus_wd : Proper (eq ==> eq ==> eq) Rplus.
Proof. simp_proper. intros; subst; ring. Qed.

Lemma Ropp_wd : Proper (eq ==> eq) Ropp.
Proof. simp_proper. intros; subst; ring. Qed.

Lemma Rminus_wd : Proper (eq ==> eq ==> eq) Rminus.
Proof. simp_proper. intros; subst; ring. Qed.

Lemma Rmult_wd : Proper (eq ==> eq ==> eq) Rmult.
Proof. simp_proper. intros; subst; ring. Qed.

Lemma Rinv_wd : Proper (eq ==> eq) Rinv.
Proof. simp_proper. intros; subst; ring. Qed.

Lemma Rdiv_wd : Proper (eq ==> eq ==> eq) Rdiv.
Proof. simp_proper. intros; subst; ring. Qed.

Hint Resolve
  Rplus_wd Ropp_wd Rminus_wd Rmult_wd Rinv_wd Rdiv_wd
  : wd.

(* ======================================================================= *)
(** ** Useful structures *)

#[export] Instance R_Order : Order Rlt Rle Rltb Rleb.
Proof.
  constructor; intros; try lra.
  destruct (total_order_T a b) as [[H|H]|H]; auto.
  apply Rltb_reflect. apply Rleb_reflect.
Qed.

#[export] Instance R_ARing : ARing Rplus R0 Ropp Rmult R1.
Proof.
  repeat constructor; intros; ring.
Qed.

#[export] Instance R_OrderedARing
  : OrderedARing Rplus 0 Ropp Rmult 1 Rlt Rle Rltb Rleb.
Proof.
  constructor. apply R_ARing. apply R_Order.
  - intros. lra.
  - intros. apply Rmult_lt_compat_r; auto.
Qed.

#[export] Instance R_Field : Field Rplus R0 Ropp Rmult R1 Rinv.
Proof.
  constructor. apply R_ARing. intros. field; auto. lra.
Qed.

#[export] Instance R_OrderedField
  : OrderedField Rplus 0 Ropp Rmult 1 Rinv Rlt Rle Rltb Rleb.
Proof.
  constructor. apply R_Field. apply R_OrderedARing.
Qed.


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

#[export] Instance R_ConvertToR
  : ConvertToR Rplus 0 Ropp Rmult 1 Rinv Rlt Rle Rltb Rleb id.
Proof. constructor; intros; unfold id; auto; try easy. apply R_Order. Qed.


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
Lemma Rineq2 : forall a b : R,
    0 <= a -> 0 <= b ->
    (a + b) / 2 >= sqrt(a * b).
Abort.

Lemma Rineq3 : forall a b c : R,
    0 <= a -> 0 <= b -> 0 <= c ->
    (a + b + c) / 3 >= sqrt(a * b).
Abort.
