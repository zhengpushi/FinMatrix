(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Conversion between R and other types.
  author    : Zhengpu Shi
  date      : 2021.05

  remark    :
 *)

Require Export NatExt ZExt QExt QcExt.
Require Import Qreals.
Require Export RExtBase.

(* ######################################################################### *)
(** * Conversion between Z and R *)

(* ======================================================================= *)
(** * R -> Z *)

(** Z to R *)
Definition Z2R (z : Z) : R := IZR z.


(* ======================================================================= *)
(** * Rfloor and Rceiling for R -> Z *)

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

(** Eliminate the up_IZR *)
Lemma up_IZR : forall z, up (IZR z) = (z + 1)%Z.
Proof.
  intros. rewrite up_tech with (r:=IZR z); auto; try lra.
  apply IZR_lt. lia.
Qed.

(** There is a unique integer if such a IZR_up equation holds. *)
Lemma IZR_up_unique : forall r, r = IZR (up r - 1) -> exists! z, IZR z = r.
Proof.
  intros. exists (up r - 1)%Z. split; auto.
  intros. subst. rewrite up_IZR in *. apply eq_IZR. auto.
Qed.

(** There isn't any integer z and real number r such that r ∈(IZR z, IZR (z+1)) *)
Lemma IZR_in_range_imply_no_integer : forall r z,
    IZR z < r ->
    r < IZR (z + 1) ->
    ~(exists z', IZR z' = r).
Proof.
  intros. intro. destruct H1. subst.
  apply lt_IZR in H0.  apply lt_IZR in H. lia.
Qed.


(** Rounding R to z, take the floor: truncate to the nearest integer
    not greater than it *)
Definition Rfloor (r : R) : Z := (up r) - 1.

(** Rounding R to z, take the ceiling: truncate to the nearest integer 
    not less than it *)
Definition Rceiling (r : R) : Z :=
  let z := up r in
  if Req_EM_T r (IZR (z - 1)%Z) then z - 1 else z.

(** z <= r < z+1.0 -> floor(r) = z *)
Lemma Rfloor_spec : forall r z,
    IZR z <= r < IZR z + 1.0 -> Rfloor r = z.
Proof.
  intros. unfold Rfloor in *. destruct H.
  assert (up r = z + 1)%Z; try lia.
  rewrite <- up_tech with (z:=z); auto.
  rewrite plus_IZR. lra.
Qed.

(** (r=z -> ceiling r = z) /\ (z < r < z + 1.0 -> ceiling r = z+1) *)
Lemma Rceiling_spec : forall r z,
    (r = IZR z -> Rceiling r = z) /\
      (IZR z < r < IZR z + 1.0 -> Rceiling r = (z+1)%Z).
Proof.
  intros. unfold Rceiling in *. split; intros.
  - destruct (Req_EM_T r (IZR (up r - 1))).
    + rewrite H. rewrite up_IZR. lia.
    + rewrite H in n. destruct n.
      rewrite up_IZR. f_equal. lia.
  - destruct H. destruct (Req_EM_T r (IZR (up r - 1))).
    + apply IZR_in_range_imply_no_integer in H; auto.
      * destruct H. exists (up r - 1)%Z; auto.
      * rewrite plus_IZR. lra.
    + rewrite up_tech with (r:=r); auto; try lra.
      rewrite plus_IZR. lra.
Qed.

(** Z2R (Rfloor r) is less than r *)
Lemma Z2R_Rfloor_le : forall r, Z2R (Rfloor r) <= r.
Proof.
  intros. unfold Z2R,Rfloor. rewrite minus_IZR.
  destruct (archimed r). lra.
Qed.

(** r-1 is less than Z2R (Rfloor r) *)
Lemma Z2R_Rfloor_gt : forall r, r - 1 < Z2R (Rfloor r).
Proof.
  intros. unfold Z2R,Rfloor. rewrite minus_IZR.
  destruct (archimed r). lra.
Qed.


(* ######################################################################### *)
(** * Conversion between nat and R *)

Definition nat2R (n : nat) : R := Z2R (nat2Z n).

Definition R2nat_floor (r : R) : nat := Z2nat (Rfloor r).

Definition R2nat_ceiling (r : R) : nat := Z2nat (Rceiling r).


(* ######################################################################### *)
(** * Conversion between Q and R *)

Lemma Q2R_eq_iff : forall a b : Q, Q2R a = Q2R b <-> Qeq a b.
Proof. intros. split; intros. apply eqR_Qeq; auto. apply Qeq_eqR; auto. Qed.

Lemma Q2R_add : forall a b : Q, Q2R (a + b) = (Q2R a + Q2R b)%R.
Proof. intros. apply Qreals.Q2R_plus. Qed.


(* ######################################################################### *)
(** * Conversion between Qc and R *)

Definition Qc2R (x : Qc) : R := Q2R (Qc2Q x).

Lemma Qc2R_add : forall a b : Qc, Qc2R (a + b) = (Qc2R a + Qc2R b)%R.
Proof.
  intros. unfold Qc2R,Qc2Q. rewrite <- Q2R_add. apply Q2R_eq_iff.
  unfold Qcplus. apply Qred_correct.
Qed.

Lemma Qc2R_0 : Qc2R 0 = 0%R.
Proof. intros. cbv. ring. Qed.

Lemma Qc2R_opp : forall a : Qc, Qc2R (- a) = (- (Qc2R a))%R.
Proof.
  intros. unfold Qc2R,Qc2Q. rewrite <- Q2R_opp. apply Q2R_eq_iff.
  unfold Qcopp. apply Qred_correct.
Qed.

Lemma Qc2R_mul : forall a b : Qc, Qc2R (a * b) = (Qc2R a * Qc2R b)%R.
Proof.
  intros. unfold Qc2R,Qc2Q. rewrite <- Q2R_mult. apply Q2R_eq_iff.
  unfold Qcmult. apply Qred_correct.
Qed.

Lemma Qc2R_1 : Qc2R 1 = (1)%R.
Proof. intros. cbv. field. Qed.

Lemma Qc2R_inv : forall a : Qc, a <> (0%Qc) -> Qc2R (/ a) = (/ (Qc2R a))%R.
Proof.
  intros. unfold Qc2R,Qc2Q. rewrite <- Q2R_inv. apply Q2R_eq_iff.
  unfold Qcinv. apply Qred_correct.
  intro. destruct H. apply Qc_is_canon. simpl. auto.
Qed.

Lemma Qc2R_eq_iff : forall a b : Qc, Qc2R a = Qc2R b <-> a = b.
Proof.
  split; intros; subst; auto. unfold Qc2R, Qc2Q in H.
  apply Qc_is_canon. apply eqR_Qeq; auto.
Qed.

Lemma Qc2R_lt_iff : forall a b : Qc, (Qc2R a < Qc2R b)%R <-> (a < b)%Qc.
Proof.
  intros. unfold Qc2R, Qc2Q,Qclt in *. split; intros.
  apply Rlt_Qlt; auto. apply Qlt_Rlt; auto.
Qed.

Lemma Qc2R_le_iff : forall a b : Qc, (Qc2R a <= Qc2R b)%R <-> (a <= b)%Qc.
Proof.
  intros. unfold Qc2R, Qc2Q,Qclt in *. split; intros.
  apply Rle_Qle; auto. apply Qle_Rle; auto.
Qed.


(* ######################################################################### *)
(** * Conversion between nat and R *)


