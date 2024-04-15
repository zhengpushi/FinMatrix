(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : extension for Qc (canonical rational number).
  author    : ZhengPu Shi
  date      : 2022.07
*)


Require Export QExt Qcanon.
Require Export Hierarchy.  
Open Scope Qc.


(* ######################################################################### *)
(** ** Understanding the Qc type *)

(* Why Qc is better than Q *)
Section eq.
  (* Why 1#2 and 2#4 could be equal? *)
  
  (* Compute Q2Qc (1#2). *)
  (* = {| this := 1 # 2; canon := Qred_involutive (1 # 2) |} *)
  (* Compute Q2Qc (2#4). *)
  (* = {| this := 1 # 2; canon := Qred_involutive (2 # 4) |} *)

  (* Answer: because the Qc type.

     Record Qc : Set := Qcmake { 
       this : Q;  
       canon : Qred this = this }.

     Here, canon is a proof of equality, so its unique by the help of UIP.
     Then, only need the "this" component equal.
   *)
  Goal Q2Qc (1#2) = Q2Qc (2#4).
  Proof. cbv. f_equal. apply UIP. Qed.
End eq.


(* ######################################################################### *)
(** * Mathematical Structure *)

#[export] Instance Qc_eq_Dec : Dec (@eq Qc).
Proof. constructor. apply Qc_eq_dec. Defined.

#[export] Instance Qc_le_Dec : Dec Qcle.
Proof.
  constructor. intros. destruct (Qclt_le_dec b a); auto.
  right. intro. apply Qcle_not_lt in H. easy.
Defined.

#[export] Instance Qc_lt_Dec : Dec Qclt.
Proof.
  constructor. intros. destruct (Qclt_le_dec a b); auto.
  right. intro. apply Qcle_not_lt in q. easy.
Defined.

(* ~ (a < a) *)
Lemma Qc_lt_irrefl : forall a : Qc, ~ (a < a).
Proof.
  intros. intro. apply Qclt_not_eq in H. easy.
Qed.

(* a <> b -> a <= b -> a < b *)
Lemma Qcle_lt_strong : forall a b : Qc, a <> b -> a <= b -> a < b.
Proof.
  intros.
  destruct (Qc_dec a b) as [[H1|H1]|H1]; auto.
  - apply Qcle_not_lt in H0. easy.
  - subst. easy.
Qed.

(* -q + q = 0 *)
Lemma Qcplus_opp_l : forall q : Qc, -q + q = Q2Qc 0.
Proof. intros. rewrite commutative, Qcplus_opp_r; auto. Qed. 

(* c + a = c + b -> a = b *)
Lemma Qc_add_reg_l : forall a b c : Qc, c + a = c + b -> a = b.
Proof.
  intros.
  assert (-c + c + a = -c + c + b). { rewrite !associative. rewrite H. auto. }
  rewrite Qcplus_opp_l in H0. rewrite !Qcplus_0_l in H0. auto.
Qed.

(* a + c = b + c -> a = b *)
Lemma Qc_add_reg_r : forall a b c : Qc, a + c = b + c -> a = b.
Proof.
  intros.
  assert (a + c + -c = b + c + -c). { rewrite H. auto. }
  rewrite !associative in H0. rewrite Qcplus_opp_r in H0.
  rewrite !Qcplus_0_r in H0. auto.
Qed.

(* a < b -> a + c < b + c *)
Lemma Qc_lt_add_compat_r : forall a b c : Qc, a < b -> a + c < b + c.
Proof.
  intros. pose proof (Qcplus_le_compat a b c c). destruct (Aeqdec a b).
  - subst. apply Qc_lt_irrefl in H. easy.
  - apply Qcle_lt_strong; auto.
    + intro. apply Qc_add_reg_r in H1. easy.
    + apply H0. apply Qclt_le_weak; auto. apply Qcle_refl.
Qed.

(* a < b -> c + a < c + b *)
Lemma Qc_lt_add_compat_l : forall a b c : Qc, a < b -> c + a < c + b.
Proof. intros. rewrite !(commutative c _). apply Qc_lt_add_compat_r; auto. Qed.

(* a < b -> 0 < c -> a * c < b * c *)
Lemma Qc_lt_mul_compat_r : forall a b c : Qc, a < b -> 0 < c -> a * c < b * c.
Proof. intros. apply Qcmult_lt_compat_r; auto. Qed.

(* a < b -> 0 < c -> c * a < c * b *)
Lemma Qc_lt_mul_compat_l : forall a b c : Qc, a < b -> 0 < c -> c * a < c * b.
Proof. intros. rewrite !(commutative c _). apply Qc_lt_mul_compat_r; auto. Qed.

(* n <= n *)
Lemma Qc_le_refl : forall n : Qc, n <= n.
Proof. apply Qcle_refl. Qed.


(** Bool version of "<" and "<=" for Qc *)
Definition Qcltb (a b : Qc) : bool := if Qclt_le_dec a b then true else false.
Definition Qcleb (a b : Qc) : bool := if Qclt_le_dec b a then false else true.
Infix "<?" := Qcltb : Qc_scope.
Infix "<=?" := Qcleb : Qc_scope.

Lemma Qcltb_reflect : forall a b : Qc, reflect (a < b) (a <? b).
Proof.
  intros. unfold Qcltb. destruct Qclt_le_dec; constructor; auto.
  apply Qcle_not_lt; auto.
Qed.

Lemma Qcleb_reflect : forall a b : Qc, reflect (a <= b) (a <=? b).
Proof.
  intros. unfold Qcleb. destruct Qclt_le_dec; constructor; auto.
  apply Qclt_not_le; auto.
Qed.

#[export] Instance Qc_Order : Order Qclt Qcle Qcltb Qcleb.
Proof.
  constructor; intros.
  - split; intros. apply Qcle_lt_or_eq; auto. destruct H.
    apply Qclt_le_weak; auto. subst. apply Qcle_refl.
  - apply Qc_lt_irrefl.
  - pose proof (Qclt_trans a b a H H0). apply Qc_lt_irrefl in H1. easy.
  - apply Qclt_trans with b; auto.
  - apply Qc_dec.
  - apply Qcltb_reflect.
  - apply Qcleb_reflect.
Qed.

Section test.
  Goal forall a b : Qc, {a = b} + {a <> b}.
  Proof. intros. apply Aeqdec. Abort.
End test.


(* ######################################################################### *)
(** ** Convertion between Qc and other types *)

(** Qc to Q *)
Definition Qc2Q (x : Qc) : Q := this x.

(** Z to Qc *)
Definition Z2Qc (x : Z) : Qc := Q2Qc (Z2Q x).

(** nat to Qc *)
Definition nat2Qc (x : nat) : Qc := Q2Qc (nat2Q x).

(** Qc to Z *)
Definition Qc2Z_ceiling (q : Qc) : Z := Q2Z_ceiling (Qc2Q q).
Definition Qc2Z_floor (q : Qc) : Z := Q2Z_floor (Qc2Q q).

(** list Q to list Qc *)
Definition Q2Qc_list l := map Q2Qc l.

(** dlist Q to dlist Qc *)
Definition Q2Qc_dlist dl := map Q2Qc_list dl.

(** list Qc to list Q, for better printing *)
Definition Qc2Q_list l := map Qc2Q l.

(** dlist Qc to dlist Q *)
Definition Qc2Q_dlist dl := map Qc2Q_list dl.


(* ######################################################################### *)
(** ** Properties for Qeqb and Qeq *)

Notation Qceqdec := Qc_eq_dec.

Notation Qceqb := Qc_eq_bool.

Infix     "=?"          := Qceqb          : Qc_scope.

(** Reflection of (=) and (=?) *)
Lemma Qceqb_true_iff : forall x y, x =? y = true <-> x = y.
Proof.
  intros; split; intros.
  - apply Qc_eq_bool_correct; auto.
  - subst. unfold Qceqb, Qc_eq_bool.
    unfold Qceqdec.
    destruct (Qeq_dec y y) eqn: E1; auto.
    destruct n. apply Qeq_refl.
Qed.

Lemma Qceqb_false_iff : forall x y, x =? y = false <-> x <> y.
Proof. 
  intros; split; intros.
  - intro. apply Qceqb_true_iff in H0. rewrite H in H0. easy.
  - destruct (Qceqb x y) eqn:E1; auto. apply Qceqb_true_iff in E1. easy.
Qed.


(* ######################################################################### *)
(** ** Well-defined (or compatible, or proper morphism) of operations on Qc. *)

Lemma Qcplus_wd : Proper (eq ==> eq ==> eq) Qcplus.
Proof. simp_proper. intros; subst; ring. Qed.

Lemma Qcopp_wd : Proper (eq ==> eq) Qcopp.
Proof. simp_proper. intros; subst; ring. Qed.

Lemma Qcminus_wd : Proper (eq ==> eq ==> eq) Qcminus.
Proof. simp_proper. intros; subst; ring. Qed.

Lemma Qcmult_wd : Proper (eq ==> eq ==> eq) Qcmult.
Proof. simp_proper. intros; subst; ring. Qed.

Lemma Qcinv_wd : Proper (eq ==> eq) Qcinv.
Proof. simp_proper. intros; subst; ring. Qed.

Lemma Qcdiv_wd : Proper (eq ==> eq ==> eq) Qcdiv.
Proof. simp_proper. intros; subst; ring. Qed.

Hint Resolve
  Qcplus_wd Qcopp_wd Qcminus_wd Qcmult_wd Qcinv_wd Qcdiv_wd
  : wd.


(* ######################################################################### *)
(** ** Others *)


(** ** sqrt of Q *)

(* Definition Qsqrt (q : Q) := Qmake (Z.sqrt (Qnum q)) (Pos.sqrt (Qden q)). *)

(* Example *)
(* Compute Qsqrt 1.21. *)
