(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : extension for Z.
  author    : Zhengpu Shi
  date      : 2022.04
*)

Require Export ZArith.
Require Export PositiveExt.

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

(** Subset *)

Instance nat_Z_Subset : Subset nat Z.
Proof.
  refine (@Build_Subset _ _ Z.of_nat _).
  rewrite injective_eq_injective_form2. hnf. apply Nat2Z.inj.
Qed.


(** Decidable *)

Instance Z_eq_Dec : Dec (@eq Z).
Proof. constructor. apply Z.eq_dec. Defined.

Instance Z_le_Dec : Dec Z.le.
Proof. constructor. intros. destruct (Z_le_gt_dec a b); auto. Defined.

Instance Z_lt_Dec : Dec Z.lt.
Proof. constructor. intros. destruct (Z_lt_le_dec a b); auto. right. lia. Defined.

(** Associative *)

Instance Zadd_Assoc : Associative Z.add.
Proof. constructor; intros; ring. Qed.

Instance Zmul_Assoc : Associative Z.mul.
Proof. constructor; intros; ring. Qed.

Hint Resolve Zadd_Assoc Zmul_Assoc : Z.

(** Commutative *)

Instance Zadd_Comm : Commutative Z.add.
Proof. constructor; intros; ring. Qed.

Instance Zmul_Comm : Commutative Z.mul.
Proof. constructor; intros; ring. Qed.

Hint Resolve Zadd_Comm Zmul_Comm : Z.

(** Identity Left/Right *)
Instance Zadd_IdL : IdentityLeft Z.add 0.
Proof. constructor; intros; ring. Qed.

Instance Zadd_IdR : IdentityRight Z.add 0.
Proof. constructor; intros; ring. Qed.

Instance Zmul_IdL : IdentityLeft Z.mul 1.
Proof. constructor; intros; ring. Qed.

Instance Zmul_IdR : IdentityRight Z.mul 1.
Proof. constructor; intros; ring. Qed.

Hint Resolve
  Zadd_IdL Zadd_IdR
  Zmul_IdL Zmul_IdR : Z.

(** Inverse Left/Right *)

Instance Zadd_InvL : InverseLeft Z.add 0 Z.opp.
Proof. constructor; intros; ring. Qed.
Hint Resolve Zadd_InvL : Z.

Instance Zadd_InvR : InverseRight Z.add 0 Z.opp.
Proof. constructor; intros; ring. Qed.
Hint Resolve Zadd_InvR : Z.


(** Distributive *)

Instance Zmul_add_DistrL : DistrLeft Z.add Z.mul.
Proof. constructor; intros; ring. Qed.
Hint Resolve Zmul_add_DistrL : Z.

Instance Zmul_add_DistrR : DistrRight Z.add Z.mul.
Proof. constructor; intros; ring. Qed.
Hint Resolve Zmul_add_DistrR : Z.

(** Semigroup *)

Instance Zadd_SGroup : SGroup Z.add.
Proof. constructor; auto with Z. Qed.
Hint Resolve Zadd_SGroup : Z.

Instance Zmul_SGroup : SGroup Z.mul.
Proof. constructor; auto with Z. Qed.
Hint Resolve Zmul_SGroup : Z.

(** Abelian semigroup *)

Instance Zadd_ASGroup : ASGroup Z.add.
Proof. constructor; auto with Z. Qed.
Hint Resolve Zadd_ASGroup : Z.

Instance Zmul_ASGroup : ASGroup Z.mul.
Proof. constructor; auto with Z. Qed.
Hint Resolve Zmul_ASGroup : Z.

(** Monoid *)
  
Instance Zadd_Monoid : Monoid Z.add 0.
Proof. constructor; auto with Z. Qed.
Hint Resolve Zadd_Monoid : Z.

Instance Zmul_Monoid : Monoid Z.mul 1.
Proof. constructor; auto with Z. Qed.
Hint Resolve Zmul_Monoid : Z.

(** Abelian monoid *)
  
Instance Zadd_AMonoid : AMonoid Z.add 0.
Proof. constructor; auto with Z. Qed.
Hint Resolve Zadd_AMonoid : Z.
  
Instance Zmul_AMonoid : AMonoid Z.mul 1.
Proof. constructor; auto with Z. Qed.
Hint Resolve Zmul_AMonoid : Z.

(** Group *)

Instance Zadd_Group : Group Z.add 0 Z.opp.
Proof. constructor; auto with Z. Qed.
Hint Resolve Zadd_Group : Z.

(** AGroup *)

Instance Zadd_AGroup : AGroup Z.add 0 Z.opp.
Proof. constructor; auto with Z. Qed.
Hint Resolve Zadd_AGroup : Z.

(** SRing *)

Instance Z_SRing : SRing Z.add 0 Z.mul 1.
Proof. constructor; auto with Z. intros. ring. Qed.
Hint Resolve Z_SRing : Z.

(** Ring *)

Instance Z_Ring : Ring Z.add 0 Z.opp Z.mul 1.
Proof. constructor; auto with Z. Qed.
Hint Resolve Z_Ring : Z.

(** ARing *)

Instance Z_ARing : ARing Z.add 0 Z.opp Z.mul 1.
Proof. constructor; auto with Z. Qed.
Hint Resolve Z_ARing : Z.

(** Order *)

Instance Z_Order : Order Z.lt Z.le.
Proof.
  constructor; intros; try lia; auto with Z.
  apply Z_dec'.
Qed.
Hint Resolve Z_Order : Z.

Instance Z_OrderedARing :
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
  Definition tA : Type := Z.
  Definition Azero : tA := 0.
  Hint Unfold tA Azero : tA.

  Lemma AeqDec : Dec (@eq tA).
  Proof. apply Z_eq_Dec. Defined.
End ElementTypeZ.

Module MonoidElementTypeZ <: MonoidElementType.
  Include ElementTypeZ.

  Definition Aadd := Zplus.
  Hint Unfold Aadd : tA.

  Infix "+" := Aadd : A_scope.

  Instance Aadd_AMonoid : AMonoid Aadd Azero.
  Proof. intros. repeat constructor; intros; autounfold with tA; ring. Qed.
End MonoidElementTypeZ.

Module RingElementTypeZ <: RingElementType.
  Include MonoidElementTypeZ.

  Definition Aone : tA := 1.
  Definition Aopp := Z.opp.
  Definition Amul := Zmult.
  Hint Unfold Aone Aopp Amul : tA.

  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := Asub : A_scope.

  Instance SRing : SRing Aadd Azero Amul Aone.
  Proof. repeat constructor; autounfold with tA; intros; ring. Qed.

  Instance ARing : ARing Aadd Azero Aopp Amul Aone.
  Proof. repeat constructor; autounfold with tA; intros; ring. Qed.

  (* Add Ring Ring_inst : (make_ring_theory ARing). *)
End RingElementTypeZ.

Module OrderedElementTypeZ <: OrderedElementType.
  Include ElementTypeZ.

  Definition Alt := Z.lt.
  Definition Ale := Z.le.
  Hint Unfold Ale Alt : tA.

  Instance Order : Order Alt Ale.
  Proof. apply Z_Order. Qed.
End OrderedElementTypeZ.

Module OrderedRingElementTypeZ <: OrderedRingElementType.
  Include RingElementTypeZ.
  
  Definition Ale := Z.le.
  Definition Alt := Z.lt.
  Hint Unfold Ale Alt : tA.

  Instance Order : Order Alt Ale.
  Proof. apply OrderedElementTypeZ.Order. Qed.
  
  Instance OrderedARing
    : OrderedARing Aadd Azero Aopp Amul Aone Alt Ale.
  Proof.
    constructor. apply ARing. apply Order.
    - intros; autounfold with tA in *. lia.
    - intros; autounfold with tA in *. apply Zmult_lt_compat_r; auto.
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

(** Z.eqb reflects Z.eq *)
Hint Resolve Z.eqb_spec : bdestruct.


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
