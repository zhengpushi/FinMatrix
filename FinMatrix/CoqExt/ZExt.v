(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : extension for Z.
  author    : ZhengPu Shi
  date      : 2022.04
*)

Require Export Hierarchy ElementType.
Require Export ZArith.
Open Scope Z.


(* ######################################################################### *)
(** * Algebraic Structures *)

(** equality is equivalence relation: Equivalence (@eq Z) *)
Hint Resolve eq_equivalence : Z.

(** operations are well-defined. Eg: Proper (eq ==> eq ==> eq) add *)
Hint Resolve
  Z.add_wd
  Z.opp_wd
  Z.sub_wd
  Z.mul_wd
  : Z.


(** Decidable *)

#[export] Instance Z_eq_Dec : Dec (@eq Z).
Proof. constructor. apply Z.eq_dec. Defined.

#[export] Instance Z_le_Dec : Dec Z.le.
Proof. constructor. intros. destruct (Z_le_gt_dec a b); auto. Defined.

#[export] Instance Z_lt_Dec : Dec Z.lt.
Proof. constructor. intros. destruct (Z_lt_le_dec a b); auto. right. lia. Defined.

(** Associative *)

#[export] Instance Zadd_Assoc : Associative Z.add.
Proof. constructor; intros; ring. Qed.

#[export] Instance Zmul_Assoc : Associative Z.mul.
Proof. constructor; intros; ring. Qed.

Hint Resolve Zadd_Assoc Zmul_Assoc : Z.

(** Commutative *)

#[export] Instance Zadd_Comm : Commutative Z.add.
Proof. constructor; intros; ring. Qed.

#[export] Instance Zmul_Comm : Commutative Z.mul.
Proof. constructor; intros; ring. Qed.

Hint Resolve Zadd_Comm Zmul_Comm : Z.

(** Identity Left/Right *)
#[export] Instance Zadd_IdL : IdentityLeft Z.add 0.
Proof. constructor; intros; ring. Qed.

#[export] Instance Zadd_IdR : IdentityRight Z.add 0.
Proof. constructor; intros; ring. Qed.

#[export] Instance Zmul_IdL : IdentityLeft Z.mul 1.
Proof. constructor; intros; ring. Qed.

#[export] Instance Zmul_IdR : IdentityRight Z.mul 1.
Proof. constructor; intros; ring. Qed.

Hint Resolve
  Zadd_IdL Zadd_IdR
  Zmul_IdL Zmul_IdR : Z.

(** Inverse Left/Right *)

#[export] Instance Zadd_InvL : InverseLeft Z.add 0 Z.opp.
Proof. constructor; intros; ring. Qed.

#[export] Instance Zadd_InvR : InverseRight Z.add 0 Z.opp.
Proof. constructor; intros; ring. Qed.

Hint Resolve Zadd_InvL Zadd_InvR : Z.


(** Distributive *)

#[export] Instance Zmul_add_DistrL : DistrLeft Z.add Z.mul.
Proof. constructor; intros; ring. Qed.

#[export] Instance Zmul_add_DistrR : DistrRight Z.add Z.mul.
Proof. constructor; intros; ring. Qed.

Hint Resolve Zmul_add_DistrL Zmul_add_DistrR : Z.

(** Semigroup *)

#[export] Instance Zadd_SGroup : SGroup Z.add.
Proof. constructor; auto with Z. Qed.

#[export] Instance Zmul_SGroup : SGroup Z.mul.
Proof. constructor; auto with Z. Qed.

Hint Resolve Zadd_SGroup Zmul_SGroup : Z.

(** Abelian semigroup *)

#[export] Instance Zadd_ASGroup : ASGroup Z.add.
Proof. constructor; auto with Z. Qed.

#[export] Instance Zmul_ASGroup : ASGroup Z.mul.
Proof. constructor; auto with Z. Qed.

Hint Resolve
  Zadd_ASGroup
  Zmul_ASGroup
  : Z.

(** Monoid *)
  
#[export] Instance Zadd_Monoid : Monoid Z.add 0.
Proof. constructor; auto with Z. Qed.

#[export] Instance Zmul_Monoid : Monoid Z.mul 1.
Proof. constructor; auto with Z. Qed.

Hint Resolve Zadd_Monoid Zmul_Monoid : Z.

(** Abelian monoid *)
  
#[export] Instance Zadd_AMonoid : AMonoid Z.add 0.
Proof. constructor; auto with Z. Qed.
  
#[export] Instance Zmul_AMonoid : AMonoid Z.mul 1.
Proof. constructor; auto with Z. Qed.

Hint Resolve Zadd_AMonoid Zmul_AMonoid : Z.

(** Group *)

#[export] Instance Zadd_Group : Group Z.add 0 Z.opp.
Proof. constructor; auto with Z. Qed.

Hint Resolve Zadd_Group : Z.

(** AGroup *)

#[export] Instance Zadd_AGroup : AGroup Z.add 0 Z.opp.
Proof. constructor; auto with Z. Qed.

Hint Resolve Zadd_AGroup : Z.

(** Ring *)

#[export] Instance Z_Ring : Ring Z.add 0 Z.opp Z.mul 1.
Proof. constructor; auto with Z. Qed.

Hint Resolve Z_Ring : Z.

(** ARing *)

#[export] Instance Z_ARing : ARing Z.add 0 Z.opp Z.mul 1.
Proof. constructor; auto with Z. Qed.

Hint Resolve Z_ARing : Z.

(** Order *)

#[export] Instance Z_Order : Order Z.lt Z.le.
Proof.
  constructor; intros; try lia; auto with Z.
  apply Z_dec'.
Qed.

Hint Resolve Z_Order : Z.

#[export] Instance Z_OrderedARing :
  OrderedARing Z.add 0 Z.opp Z.mul 1 Z.lt Z.le.
Proof.
  constructor; auto with Z.
  intros; lia.
  intros. apply Zmult_lt_compat_r; auto.
Qed.

Hint Resolve Z_OrderedARing : Z.


(* ######################################################################### *)
(** * Instances for ElementType *)

Module ElementTypeZ <: ElementType.
  Definition A : Type := Z.
  Definition Azero : A := 0.
  Hint Unfold A Azero : A.

  Lemma AeqDec : Dec (@eq A).
  Proof. apply Z_eq_Dec. Defined.
End ElementTypeZ.

Module MonoidElementTypeZ <: MonoidElementType.
  Include ElementTypeZ.

  Definition Aadd := Zplus.
  Hint Unfold Aadd : A.

  Infix "+" := Aadd : A_scope.

  #[export] Instance Aadd_AMonoid : AMonoid Aadd Azero.
  Proof. intros. repeat constructor; intros; autounfold with A; ring. Qed.
End MonoidElementTypeZ.

Module RingElementTypeZ <: RingElementType.
  Include MonoidElementTypeZ.

  Definition Aone : A := 1.
  Definition Aopp := Z.opp.
  Definition Amul := Zmult.
  Hint Unfold Aone Aopp Amul : A.

  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := Asub : A_scope.

  #[export] Instance ARing : ARing Aadd Azero Aopp Amul Aone.
  Proof. repeat constructor; autounfold with A; intros; ring. Qed.

  (* Add Ring Ring_inst : (make_ring_theory ARing). *)
End RingElementTypeZ.

Module OrderedElementTypeZ <: OrderedElementType.
  Include ElementTypeZ.

  Definition Alt := Z.lt.
  Definition Ale := Z.le.
  Hint Unfold Ale Alt : A.

  #[export] Instance Order : Order Alt Ale.
  Proof. apply Z_Order. Qed.
End OrderedElementTypeZ.

Module OrderedRingElementTypeZ <: OrderedRingElementType.
  Include RingElementTypeZ.
  
  Definition Ale := Z.le.
  Definition Alt := Z.lt.
  Hint Unfold Ale Alt : A.

  #[export] Instance Order : Order Alt Ale.
  Proof. apply OrderedElementTypeZ.Order. Qed.
  
  #[export] Instance OrderedARing
    : OrderedARing Aadd Azero Aopp Amul Aone Alt Ale.
  Proof.
    constructor. apply ARing. apply Order.
    - intros; autounfold with A in *. lia.
    - intros; autounfold with A in *. apply Zmult_lt_compat_r; auto.
  Qed.
End OrderedRingElementTypeZ.


(* ######################################################################### *)
(** * Conversion between Z and other types *)
Definition nat2Z (n : nat) : Z := Z.of_nat n.
Definition Z2nat (z : Z) : nat := Z.to_nat z.


(* ######################################################################### *)
(** * Properties for Zeqb and Zeq *)

Definition Zeqb := Z.eqb.

Infix     "=?"          := Zeqb           : Z_scope.

(** Reflection of (=) and (=?) *)
Lemma Zeqb_true_iff : forall x y, x =? y = true <-> x = y.
Proof.
  apply Z.eqb_eq.
Qed.

Lemma Zeqb_false_iff : forall x y, x =? y = false <-> x <> y.
Proof.
  apply Z.eqb_neq.
Qed.


(* ######################################################################### *)
(** * Other properties *)

(** Boolean equality of Zadd satisfy right cancelling rule *)
Lemma Zadd_eqb_cancel_r : forall (z1 z2 a : Z),
  (z1 + a =? z2 + a)%Z = (z1 =? z2)%Z.
Proof.
  intros.
  remember (z1 =? z2)%Z as b1 eqn : H1.
  remember (z1 + a =? z2 + a)%Z as b2 eqn : H2.
  destruct b1,b2; auto.
  - apply eq_sym in H1,H2. apply Z.eqb_eq in H1. apply Z.eqb_neq in H2.
    subst. auto.
  - apply eq_sym in H1,H2. apply Z.eqb_neq in H1. apply Z.eqb_eq in H2.
    apply Z.add_cancel_r in H2. apply H1 in H2. easy.
Qed.
