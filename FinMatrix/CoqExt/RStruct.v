(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : extension for Coq.Reals.
  author    : Zhengpu Shi
  date      : 2021.05

  remark    :
 *)

Require Export ElementType.
Require Export RExtCvt.
Require Export RExtBase.


(* ######################################################################### *)
(** * Algebraic Structures *)

(** Qc has a A2R structure *)
Instance Qc_A2R
  : A2R Qcplus (0%Qc) Qcopp Qcmult (1%Qc) Qcinv Qclt Qcle Qc2R.
Proof.
  constructor; intros.
  apply Qc2R_add. apply Qc2R_0. apply Qc2R_opp. apply Qc2R_mul. apply Qc2R_1.
  apply Qc2R_inv; auto. apply Qc_Order. apply Qc2R_eq_iff.
  apply Qc2R_lt_iff. apply Qc2R_le_iff.
Qed.


(** equality is equivalence relation: Equivalence eq *)
Hint Resolve eq_equivalence : R.

(** operations are well-defined. Eg: Proper (eq ==> eq ==> eq) Rplus *)

Lemma Radd_wd : Proper (eq ==> eq ==> eq) Rplus.
Proof. repeat (hnf; intros); subst; auto. Qed.

Lemma Ropp_wd : Proper (eq ==> eq) Ropp.
Proof. repeat (hnf; intros); subst; auto. Qed.

Lemma Rsub_wd : Proper (eq ==> eq ==> eq) Rminus.
Proof. repeat (hnf; intros); subst; auto. Qed.

Lemma Rmul_wd : Proper (eq ==> eq ==> eq) Rmult.
Proof. repeat (hnf; intros); subst; auto. Qed.

Lemma Rinv_wd : Proper (eq ==> eq) Rinv.
Proof. repeat (hnf; intros); subst; auto. Qed.

Lemma Rdiv_wd : Proper (eq ==> eq ==> eq) Rdiv.
Proof. repeat (hnf; intros); subst; auto. Qed.

Hint Resolve
  Radd_wd Ropp_wd Rsub_wd
  Rmul_wd Rinv_wd Rdiv_wd : R.

(** Decidable *)

Instance Req_Dec : Dec (@eq R).
Proof. constructor. apply Req_EM_T. Defined.

Instance Rle_Dec : Dec Rle.
Proof. constructor. intros. destruct (Rle_lt_dec a b); auto. right; lra. Qed.

Instance Rlt_Dec : Dec Rlt.
Proof. constructor. intros. destruct (Rlt_le_dec a b); auto. right; lra. Qed.

(** Associative *)

Instance Radd_Assoc : Associative Rplus.
Proof. constructor; intros; field. Qed.

Instance Rmul_Assoc : Associative Rmult.
Proof. constructor; intros; field. Qed.

Hint Resolve Radd_Assoc Rmul_Assoc : R.

(** Commutative *)

Instance Radd_Comm : Commutative Rplus.
Proof. constructor; intros; field. Qed.

Instance Rmul_Comm : Commutative Rmult.
Proof. constructor; intros; field. Qed.

Hint Resolve Radd_Comm Rmul_Comm : R.

(** Identity Left/Right *)
Instance Radd_IdL : IdentityLeft Rplus 0.
Proof. constructor; intros; field. Qed.

Instance Radd_IdR : IdentityRight Rplus 0.
Proof. constructor; intros; field. Qed.

Instance Rmul_IdL : IdentityLeft Rmult 1.
Proof. constructor; intros; field. Qed.

Instance Rmul_IdR : IdentityRight Rmult 1.
Proof. constructor; intros; field. Qed.

Hint Resolve
  Radd_IdL Radd_IdR
  Rmul_IdL Rmul_IdR : R.

(** Inverse Left/Right *)

Instance Radd_InvL : InverseLeft Rplus 0 Ropp.
Proof. constructor; intros; ring. Qed.

Instance Radd_InvR : InverseRight Rplus 0 Ropp.
Proof. constructor; intros; ring. Qed.

Hint Resolve Radd_InvL Radd_InvR : R.

(** Distributive *)

Instance Rmul_add_DistrL : DistrLeft Rplus Rmult.
Proof. constructor; intros; field. Qed.

Instance Rmul_add_DistrR : DistrRight Rplus Rmult.
Proof. constructor; intros; field. Qed.

Hint Resolve
  Rmul_add_DistrL
  Rmul_add_DistrR
  : R.

(** Semigroup *)

Instance Radd_SGroup : SGroup Rplus.
Proof. constructor; auto with R. Qed.

Instance Rmul_SGroup : SGroup Rmult.
Proof. constructor; auto with R. Qed.

Hint Resolve
  Radd_SGroup
  Rmul_SGroup
  : R.

(** Abelian semigroup *)

Instance Radd_ASGroup : ASGroup Rplus.
Proof. constructor; auto with R. Qed.

Instance Rmul_ASGroup : ASGroup Rmult.
Proof. constructor; auto with R. Qed.

Hint Resolve
  Radd_ASGroup
  Rmul_ASGroup
  : R.

(** Monoid *)
  
Instance Radd_Monoid : Monoid Rplus 0.
Proof. constructor; auto with R. Qed.

Instance Rmul_Monoid : Monoid Rmult 1.
Proof. constructor; auto with R. Qed.

Hint Resolve
  Radd_Monoid
  Rmul_Monoid
  : R.

(** Abelian monoid *)
  
Instance Radd_AMonoid : AMonoid Rplus 0.
Proof. constructor; auto with R. Qed.
  
Instance Rmul_AMonoid : AMonoid Rmult 1.
Proof. constructor; auto with R. Qed.

Hint Resolve Radd_AMonoid Rmul_AMonoid : R.

(** Group *)

Instance Radd_Group : Group Rplus 0 Ropp.
Proof. constructor; auto with R. Qed.
Hint Resolve Radd_Group : R.

(** AGroup *)

Instance Radd_AGroup : AGroup Rplus 0 Ropp.
Proof. constructor; auto with R. Qed.
Hint Resolve Radd_AGroup : R.

(** SRing *)

Instance R_SRing : SRing Rplus 0 Rmult 1.
Proof. constructor; auto with R; intros; ring. Qed.
Hint Resolve R_SRing : R.

(** Ring *)

Instance R_Ring : Ring Rplus 0 Ropp Rmult 1.
Proof. constructor; auto with R. Qed.
Hint Resolve R_Ring : R.

(** ARing *)

Instance R_ARing : ARing Rplus 0 Ropp Rmult 1.
Proof. constructor; auto with R. Qed.
Hint Resolve R_ARing : R.

(** Field *)
Hint Resolve R1_neq_R0 : R.
Hint Resolve Rmult_inv_l : R.

Instance R_Field : Field Rplus 0 Ropp Rmult 1 Rinv.
Proof. constructor; auto with R. Qed.

Hint Resolve R_Field : R.

(** Order *)

Instance R_Order : Order Rlt Rle.
Proof.
  constructor; intros; try lra; auto with R.
  pose proof (total_order_T a b).
  do 2 (destruct H as [H|]; auto).
Qed.

Hint Resolve R_Order : R.

Instance R_OrderedARing :
  OrderedARing Rplus 0 Ropp Rmult 1 Rlt Rle.
Proof. constructor; auto with R. intros; lra. Qed.

Hint Resolve R_OrderedARing : R.

Instance R_OrderedField :
  OrderedField Rplus 0 Ropp Rmult 1 Rinv Rlt Rle.
Proof. constructor; auto with R. Qed.

Hint Resolve R_OrderedField : R.

Instance R_A2R
  : A2R Rplus 0 Ropp Rmult 1 Rinv Rlt Rle id.
Proof. constructor; intros; unfold id; auto with R; try easy. Qed.


(* ######################################################################### *)
(** * Instances for ElementType *)

(* Note that, because we need "Qc2R", thus this instance of "Qc" is here. *)
Module NormedOrderedFieldElementTypeQc <: NormedOrderedFieldElementType.
  Include OrderedFieldElementTypeQc.
  Import Reals.

  Definition a2r := Qc2R.
  
  Instance A2R
    : A2R Aadd Azero Aopp Amul Aone Ainv Alt Ale a2r.
  Proof. apply Qc_A2R. Qed.
End NormedOrderedFieldElementTypeQc.

Module ElementTypeR <: ElementType.
  Definition tA : Type := R.
  Definition Azero : tA := 0.
  Hint Unfold tA Azero : tA.

  Lemma AeqDec : Dec (@eq tA).
  Proof. apply Req_Dec. Defined.
End ElementTypeR.

Module test_ElementType.
  Import ElementTypeNat ElementTypeR.
  Module Import ElementTypeFunEx1 :=
    ElementTypeFun ElementTypeNat ElementTypeR.

  Definition f : tA := fun i => match i with 0%nat => 1 | 1%nat => 2 | _ => 1 end.
  Definition g : tA := fun i => match i with 1%nat => 2 | _ => 1 end.

  Goal f = g.
  Proof. cbv. intros. auto. Qed.
End test_ElementType.

Module OrderedElementTypeR <: OrderedElementType.
  Include ElementTypeR.

  Definition Alt := Rlt.
  Definition Ale := Rle.
  Hint Unfold Ale Alt : tA.

  Instance Order : Order Alt Ale.
  Proof. apply R_Order. Qed.
End OrderedElementTypeR.

Module MonoidElementTypeR <: MonoidElementType.
  Include ElementTypeR.
  
  Definition Aadd := Rplus.
  Hint Unfold Aadd : tA.
  
  Infix "+" := Aadd : A_scope.

  Instance Aadd_AMonoid : AMonoid Aadd Azero.
  Proof. intros. repeat constructor; intros; autounfold with tA; ring. Qed.
End MonoidElementTypeR.

Module test_MonoidElementType.
  Import MonoidElementTypeQc.
  Import MonoidElementTypeR.
  
  Module Import MonoidElementTypeFunEx1 :=
    MonoidElementTypeFun MonoidElementTypeQc MonoidElementTypeR.

  (* Definition f : tA := fun i:Qc => Qc2R i + R1. *)
  (* Definition g : tA := fun i:Qc => Qc2R (i+1). *)
  Definition f : tA := fun i => 1.
  Definition g : tA := fun i => 2.
  Definition h : tA := fun i => 3.

  Goal f + g + h = f + (g + h).
  Proof. rewrite associative. auto. Qed.
End test_MonoidElementType.

Module RingElementTypeR <: RingElementType.
  Include MonoidElementTypeR.
  
  Definition Aone : tA := 1.
  Definition Aopp := Ropp.
  Definition Amul := Rmult.
  Hint Unfold Aone Aadd Aopp Amul : tA.
  
  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := Asub : A_scope.

  Instance SRing : SRing Aadd Azero Amul Aone.
  Proof. repeat constructor; autounfold with tA; intros; ring. Qed.

  Instance ARing : ARing Aadd Azero Aopp Amul Aone.
  Proof. repeat constructor; autounfold with tA; intros; ring. Qed.
  
  (* Add Ring Ring_inst : (make_ring_theory ARing). *)
End RingElementTypeR.

Module test_RingElementType.
  Import RingElementTypeQc.
  Import RingElementTypeR.
  
  Module Import RingElementTypeFunEx1 :=
    RingElementTypeFun RingElementTypeQc RingElementTypeR.
  
  Definition f : tA := fun i:Qc => (Qc2R i + R1)%R.
  Definition g : tA := fun i:Qc => Qc2R (i+1).

  Goal f = g.
  Proof. Abort.
End test_RingElementType.


Module OrderedRingElementTypeR <: OrderedRingElementType.
  Include RingElementTypeR.
  
  Definition Ale := Rle.
  Definition Alt := Rlt.
  Hint Unfold Ale Alt : tA.

  Instance Order : Order Alt Ale.
  Proof. apply OrderedElementTypeR.Order. Qed.
  
  Instance OrderedARing
    : OrderedARing Aadd Azero Aopp Amul Aone Alt Ale.
  Proof.
    constructor. apply ARing. apply Order.
    - intros; autounfold with tA in *. lra.
    - intros; autounfold with tA in *. apply Rmult_lt_compat_r; auto.
  Qed.

  Notation "| a |" := (Aabs a) : A_scope.
  
End OrderedRingElementTypeR.

Module FieldElementTypeR <: FieldElementType.
  Include RingElementTypeR.
  
  Definition Ainv := Rinv.
  Hint Unfold Ainv : tA.
  
  Notation Adiv := (fun x y => Amul x (Ainv y)).

  Lemma Aone_neq_Azero : Aone <> Azero.
  Proof. cbv in *. auto with real. Qed.

  Instance Field : Field Aadd Azero Aopp Amul Aone Ainv.
  Proof.
    constructor. apply ARing. intros.
    autounfold with tA. field. auto.
    apply Aone_neq_Azero.
  Qed.

  (* Add Field Field_inst : (make_field_theory Field). *)
End FieldElementTypeR.

Module OrderedFieldElementTypeR <: OrderedFieldElementType.
  Include FieldElementTypeR.
  
  Definition Ale := Rle.
  Definition Alt := Rlt.
  Hint Unfold Ale Alt : tA.

  Instance Order : Order Alt Ale.
  Proof. apply OrderedElementTypeR.Order. Qed.
  
  Instance OrderedARing
    : OrderedARing Aadd Azero Aopp Amul Aone Alt Ale.
  Proof. apply OrderedRingElementTypeR.OrderedARing. Qed.
  
  Instance OrderedAField
    : OrderedField Aadd Azero Aopp Amul Aone Ainv Alt Ale.
  Proof. constructor. apply Field. apply OrderedRingElementTypeR.OrderedARing. Qed.

  Notation "| a |" := (Aabs a) : A_scope.

End OrderedFieldElementTypeR.

Module NormedOrderedFieldElementTypeR <: NormedOrderedFieldElementType.
  Include OrderedFieldElementTypeR.
  
  Definition a2r := id.
  
  Instance A2R
    : A2R Aadd Azero Aopp Amul Aone Ainv Alt Ale a2r.
  Proof. apply R_A2R. Qed.
End NormedOrderedFieldElementTypeR.

