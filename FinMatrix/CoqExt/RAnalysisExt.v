(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : real function
  author    : Zhengpu Shi
  date      : 2023.03
  
  reference :
  1. 高等数学学习手册，徐小湛
 *)


Require Export RExt RFunExt.
Open Scope R_scope.

(* ######################################################################### *)
(** * Basis of real analysis *)


(* (** Type of a function from real number to real number *) *)
(* Definition tpRfun := R -> R. *)

(* (** Type of a function from real function to another real function *) *)
(* Definition tpRfunctional := (R->R) -> (R->R). *)


(* ======================================================================= *)
(** ** 实数集 *)

(** R上的一个子集 *)
Definition setR := R -> Prop.

Section test.
  Let X : setR := fun (x : R) => x > 0.
  (* Variable Y : setR. *)
End test.

(** 全体 *)
Definition allR : setR := fun _ => True.

(* ======================================================================= *)
(** ** 邻域 *)
Definition neighbourhoodR (a delta : R) : setR :=
  fun x => delta > 0 /\ Rabs (x - a) < delta.

(* ======================================================================= *)
(** ** 实数界的有界性 *)

(** 一个集合是有界的 *)
Definition boundR (X : setR) : Prop :=
  exists (M : R), (M > 0) /\ (forall x, X x -> Rabs x <= M).

(** 一个集合是无界的 *)
Definition unboundR (X : setR) : Prop :=
  forall (M : R), (M > 0) -> (exists x, X x /\ Rabs x > M).

(** 集合有界的等价定义 *)
Definition boundR' (X : setR) : Prop :=
  exists (A B : R), (A < B) /\ (forall x, X x -> (A <= x <= B)).

Theorem boundR_eq_boundR' : forall X, boundR X <-> boundR' X.
Admitted.

(* ======================================================================= *)
(** ** Domain of real functions *)

(** 函数的定义域：使得函数表达式有意义的一切实数组成的集合 *)
Parameter domain_of : (R -> R) -> setR.

(** 常见函数的定义域 *)
Axiom domain_of_inv : domain_of Rinv = fun x => x <> 0%R.
Axiom domain_of_sqrt : domain_of (fun u => sqrt u) = fun u => u >= 0.
Axiom domain_of_ln : domain_of ln = fun u => u > 0.
Axiom domain_of_tan :
  domain_of tan = fun u => ~(exists (k : Z), u = (2 * (IZR k) * PI + PI/2))%R.

(* ======================================================================= *)
(** ** Range of real functions *)

(** 函数的值域：函数在定义域内取值后的到的函数值的集合 *)
Definition range_of (f : R -> R) : setR :=
  fun y => exists x, (domain_of f) x -> f x = y.

(* ======================================================================= *)
(** ** Composition of real functions. *)

(** composition of two real functions f and g, with right associativity *)
Definition fcomp (f g : R -> R) : R -> R := fun x => f (g x).
Infix "\o" := fcomp : RFun_scope.

Fact fcomp_rw : forall u v : R -> R, (fun x => u (v x)) = (u \o v).
Proof. auto. Qed.

(** 两个函数可以复合的条件是：内函数的值域与外函数的定义域的交集非空 *)
Definition fcomp_valid (u v : R -> R) : Prop :=
  let Du := domain_of u in
  let Rv := range_of v in
  exists x, (Du x /\ Rv x).

Section test.
  Goal let f := fun x => (x * x + / x)%R in
       let g := fun x => (x + / x)%R in
       fcomp_valid f g ->
       (f \o g) = fun x =>
                     let x2 := (x * x)%R in
                     (x2 + / x2 + (x / (x2 + 1)) + 2)%R.
  Proof.
    intros. unfold f, g, fcomp, fcomp_valid in *. apply feq_iff; intros.
    field.
  Abort.
End test.

(* ======================================================================= *)
(** ** 函数的有界性 *)

(** f在X内是有界的 *)
Definition boundf (f : R -> R) (X : setR) : Prop :=
  exists M, M > 0 /\ (forall x, X x -> (Rabs (f x) <= M)).

(** f在X内不是有界的 *)
Definition unboundf (f : R -> R) (X : setR) : Prop :=
  forall M, M > 0 -> (exists x, X x /\ (Rabs (f x) > M)).

(** 有界性的等价刻画 *)
Definition boundf' (f : R -> R) (X : setR) : Prop :=
  exists (A B : R), (A < B) /\ (forall x, X x -> (A <= f x <= B)).

Theorem boundf_eq_boundf' : forall f X, boundf f X <-> boundf' f X.
Admitted.

(* ======================================================================= *)
(** ** 函数的上界、下界、界  *)

(** l是f在定义域内的下界 *)
Definition lower_bound_of (f : R -> R) (l : R) : Prop :=
  l > 0 /\ (forall x, (domain_of f x -> f x >= l)).

(** u是f在定义域内的上界 *)
Definition upper_bound_of (f : R -> R) (u : R) : Prop :=
  u > 0 /\ (forall x, (domain_of f x -> f x <= u)).

(** u是f在定义域内的界 *)
Definition bound_of (f : R -> R) (u : R) : Prop :=
  u > 0 /\ (forall x, (domain_of f x -> Rabs (f x) <= u)).

(** 以下函数在其定义域内是有界的（整体有界） *)
Fact boundf_sin : boundf sin allR. Admitted.
Fact bound_sin : bound_of sin 1. Admitted.

Fact boundf_cos : boundf cos allR. Admitted.
Fact bound_cos : bound_of cos 1. Admitted.

(* ======================================================================= *)
(** ** Parity of function *)

Definition oddf (f : R -> R) : Prop := forall x, f (-x) = - (f x).
Definition evenf (f : R -> R) : Prop := forall x, f (-x) = f x.

Fact oddf_id : evenf id. Admitted.
Fact oddf_pow3 : evenf (fun x => x ^ 3). Admitted.
Fact oddf_sin : evenf sin. Admitted.
Fact oddf_tan : evenf tan. Admitted.

Fact evenf_fcnst : forall (C : R), evenf (fcnst C). Admitted.
Fact evenf_pow2 : evenf (fun x => x ^ 2). Admitted.
Fact evenf_pow2n : forall (n : nat), evenf (fun x => x ^ (2 * n)). Admitted.
Fact evenf_cos : evenf cos. Admitted.

Lemma fadd_odd_odd : forall u v, oddf u -> oddf v -> oddf (u +f v).
Admitted.

Lemma fsub_odd_odd : forall u v, oddf u -> oddf v -> oddf (u -f v).
Admitted.

Lemma fmul_odd_odd : forall u v, oddf u -> oddf v -> evenf (u *f v).
Admitted.

Lemma fdiv_odd_odd : forall u v, oddf u -> oddf v -> evenf (u /f v).
Admitted.

Lemma fadd_even_even : forall u v, evenf u -> evenf v -> evenf (u +f v).
Admitted.

Lemma fsub_even_even : forall u v, evenf u -> evenf v -> evenf (u -f v).
Admitted.

Lemma fmul_even_even : forall u v, evenf u -> evenf v -> evenf (u *f v).
Admitted.

Lemma fdiv_even_even : forall u v, evenf u -> evenf v -> evenf (u /f v).
Admitted.

Lemma fcomp_any_even : forall u v, evenf v -> evenf (u \o v).
Admitted.

Lemma fcomp_odd_odd : forall u v, oddf u -> oddf v -> oddf (u \o v).
Admitted.

Lemma fcomp_even_odd : forall u v, evenf u -> oddf v -> evenf (u \o v).
Admitted.


(** ** 周期函数 *)
(* ======================================================================= *)

(** 函数 f 是周期函数 *)
Definition periodicf (f : R -> R) : Prop :=
  exists (l : R), l > 0 /\ (forall x, (domain_of f) x -> f (x + l)%R = f x).

(** 函数 f 是以 T 为周期 *)
Definition periodic_of (f : R -> R) (T : R) : Prop :=
  T > 0 /\ (forall x, (domain_of f) x -> f (x + T)%R = f x).

(** 常见的周期函数 *)
Fact periodicf_sin : periodicf sin. Admitted.
Fact periodic_of_sin : periodic_of sin (2*PI). Admitted.

Fact periodicf_cos : periodicf cos. Admitted.
Fact periodic_of_cos : periodic_of cos (2*PI). Admitted.

Fact periodicf_tan : periodicf tan. Admitted.
Fact periodic_of_tan : periodic_of tan (2*PI). Admitted.


(* ######################################################################### *)
(** * Analysis of basic elementary functions *)

Axiom domain_of_Rpower : forall (a : R), (a > 0 /\ a <> 1) -> domain_of (Rpower a) = allR.
Fact range_of_Rpower (a : R) : range_of (Rpower a) = fun x => x > 0. Admitted.

Axiom domain_of_Rlog : forall (a : R),
    (a > 0 /\ a <> 1) -> domain_of (Rlog a) = (fun x => x > 0).
Fact range_of_Rlog (a : R) : range_of (Rlog a) = allR. Admitted.

