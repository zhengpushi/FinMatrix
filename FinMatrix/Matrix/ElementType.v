(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Type of Matrix Element
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. Element type is orgainized to several levels
  * ElementType
  * OrderedElementType
  * MonoidElementType, based on ElementType.
  * RingElementType, based on MonoidElementType.
  * OrderedRingElementType, based on RingElementType + OrderedElementType
  * FieldElementType, based on RingElementType.
  * OrderedFieldElementType, based on FieldElementType + OrderedElementType.
  * NormedOrderedFieldElementType, based on OrderedFieldElementType + Normed.

  2. Future plan:
  * SemiRingElementType.
    Because, we can define `add` and `mul` on `nat` type, 
    such that `vcmul` and `vdot` could be defined on natural numbers.
*)

Require NatExt ZExt QExt QcExt RExt RFunExt Complex.
Require Export Hierarchy.



(* ######################################################################### *)
(** * ElementType *)

(** A type with decidable equality and zero element *)
Module Type ElementType.
  Parameter A : Type.
  Parameter Azero : A.
  Notation "0" := Azero : A_scope.

  Axiom AeqDec : Dec (@eq A).
  #[export] Existing Instance AeqDec.
End ElementType.


(** ** Instances *)
Module ElementTypeNat <: ElementType.
  Export NatExt.
  Definition A : Type := nat.
  Definition Azero : A := 0.
  Hint Unfold A Azero : A.

  Lemma AeqDec : Dec (@eq A).
  Proof. apply nat_eq_Dec. Defined.
End ElementTypeNat.

Module ElementTypeZ <: ElementType.
  Export ZExt.
  Definition A : Type := Z.
  Definition Azero : A := 0.
  Hint Unfold A Azero : A.

  Lemma AeqDec : Dec (@eq A).
  Proof. apply Z_eq_Dec. Defined.
End ElementTypeZ.

Module ElementTypeQ <: ElementType.
  Export QExt.
  Definition A : Type := Q.
  Definition Azero : A := 0.
  Hint Unfold A Azero : A.

  Lemma AeqDec : Dec (@eq A).
  Proof. apply Q_eq_Dec. Defined.
End ElementTypeQ.

Module ElementTypeQc <: ElementType.
  Export QcExt.
  Definition A : Type := Qc.
  Definition Azero : A := 0.
  Hint Unfold A Azero : A.

  Lemma AeqDec : Dec (@eq A).
  Proof. apply Qc_eq_Dec. Defined.

End ElementTypeQc.

Module ElementTypeR <: ElementType.
  Export RExt.

  Definition A : Type := R.
  Definition Azero : A := 0.
  Hint Unfold A Azero : A.

  Lemma AeqDec : Dec (@eq A).
  Proof. apply Req_Dec. Defined.
End ElementTypeR.

Module ElementTypeC <: ElementType.
  Export Complex.
  Definition A : Type := C.
  Definition Azero : A := 0.
  Hint Unfold A Azero : A.

  Lemma AeqDec : Dec (@eq A).
  Proof. apply Complex_eq_Dec. Defined.
End ElementTypeC.

Module ElementTypeRFun <: ElementType.
  Export RFunExt.
  Add Ring ring_inst : (make_ring_theory Rfun_ARing).
  
  Definition A : Type := R -> R.
  Definition Azero : A := fzeroR.
  Hint Unfold A Azero : A.

  Lemma AeqDec : Dec (@eq A).
  Proof. constructor. intros a b.
         (* rewrite (functional_extensionality a b). *)
  Admitted.
End ElementTypeRFun.

Module ElementTypeFun (I O : ElementType) <: ElementType.
  Definition A : Type := I.A -> O.A.
  Definition Azero : A := fun _ => O.Azero.
  Hint Unfold A Azero : A.

  Lemma AeqDec : Dec (@eq A).
  Proof. constructor. intros a b. unfold A in *.
  Admitted.
End ElementTypeFun.

Module ElementType_Test.
  Import ElementTypeNat ElementTypeR.
  Module Import ElementTypeFunEx1 :=
    ElementTypeFun ElementTypeNat ElementTypeR.

  Definition f : A := fun i => match i with 0%nat => 1 | 1%nat => 2 | _ => 1 end.
  Definition g : A := fun i => match i with 1%nat => 2 | _ => 1 end.

  Goal f = g.
  Proof. cbv. intros. auto. Qed.
End ElementType_Test.


(* ######################################################################### *)
(** * OrderedElementType *)

(** An extended `ElementType` equipped with order relation *)
Module Type OrderedElementType <: ElementType.
  Include ElementType.
  
  Parameter Alt Ale : A -> A -> Prop.

  Infix "<" := Alt : A_scope.
  Infix "<=" := Ale : A_scope.
  
  Axiom Order : Order Alt Ale.
End OrderedElementType.

(** ** Instances *)
Module OrderedElementTypeNat <: OrderedElementType.
  Include ElementTypeNat.

  Definition Alt := Nat.lt.
  Definition Ale := Nat.le.
  Hint Unfold Ale Alt : A.

  #[export] Instance Order : Order Alt Ale.
  Proof. apply nat_Order. Qed.
End OrderedElementTypeNat.

Module OrderedElementTypeZ <: OrderedElementType.
  Include ElementTypeZ.

  Definition Alt := Z.lt.
  Definition Ale := Z.le.
  Hint Unfold Ale Alt : A.

  #[export] Instance Order : Order Alt Ale.
  Proof. apply Z_Order. Qed.
End OrderedElementTypeZ.

(*
Module OrderedElementTypeQ <: OrderedElementType.
  Include ElementTypeQ.

  Definition Alt := Qlt.
  Definition Ale := Qle.
  Hint Unfold Ale Alt : A.

  #[export] Instance Order : Order Alt Ale.
  Proof.
    constructor; intros; autounfold with A in *; try lia.
  Abort.
End OrderedElementTypeQ.
*)

Module OrderedElementTypeQc <: OrderedElementType.
  Include ElementTypeQc.

  Definition Alt := Qclt.
  Definition Ale := Qcle.
  Hint Unfold Ale Alt : A.

  #[export] Instance Order : Order Alt Ale.
  Proof. apply Qc_Order. Qed.
End OrderedElementTypeQc.

Module OrderedElementTypeR <: OrderedElementType.
  Include ElementTypeR.

  Definition Alt := Rlt.
  Definition Ale := Rle.
  Hint Unfold Ale Alt : A.

  #[export] Instance Order : Order Alt Ale.
  Proof. apply R_Order. Qed.
End OrderedElementTypeR.


(* ######################################################################### *)
(** * Element with abelian-monoid structure *)

(** ** Type of Element with abelian-monoid structure *)
(* Note, we won't use `AMonoidElementType` to emphasize the `abelian` property *)
Module Type MonoidElementType <: ElementType.
  Include ElementType.
  Open Scope A_scope.

  Parameter Aadd : A -> A -> A.
  Infix "+" := Aadd : A_scope.

  Axiom Aadd_AMonoid : AMonoid Aadd Azero.
  #[export] Existing Instance Aadd_AMonoid.
End MonoidElementType.

(** ** Instances *)

Module MonoidElementTypeNat <: MonoidElementType.
  Include ElementTypeNat.

  Definition Aadd := Nat.add.
  Hint Unfold Aadd : A.

  Infix "+" := Aadd : A_scope.

  #[export] Instance Aadd_AMonoid : AMonoid Aadd Azero.
  Proof. intros. repeat constructor; intros; autounfold with A; ring. Qed.
End MonoidElementTypeNat.

Module MonoidElementTypeZ <: MonoidElementType.
  Include ElementTypeZ.

  Definition Aadd := Zplus.
  Hint Unfold Aadd : A.

  Infix "+" := Aadd : A_scope.

  #[export] Instance Aadd_AMonoid : AMonoid Aadd Azero.
  Proof. intros. repeat constructor; intros; autounfold with A; ring. Qed.
End MonoidElementTypeZ.

Module MonoidElementTypeQc <: MonoidElementType.
  Include ElementTypeQc.

  Definition Aadd := Qcplus.
  Hint Unfold Aadd : A.
  
  Infix "+" := Aadd : A_scope.

  #[export] Instance Aadd_AMonoid : AMonoid Aadd Azero.
  Proof. intros. repeat constructor; intros; autounfold with A; ring. Qed.
End MonoidElementTypeQc.

Module MonoidElementTypeR <: MonoidElementType.
  Include ElementTypeR.  
  
  Definition Aadd := Rplus.
  Hint Unfold Aadd : A.
  
  Infix "+" := Aadd : A_scope.

  #[export] Instance Aadd_AMonoid : AMonoid Aadd Azero.
  Proof. intros. repeat constructor; intros; autounfold with A; ring. Qed.
End MonoidElementTypeR.

Module MonoidElementTypeC <: MonoidElementType.
  Include ElementTypeC.

  Definition Aadd := Cadd.
  
  (** Note that, this explicit annotation is must, 
      otherwise, the ring has no effect. (because C and T are different) *)
  (* Definition Aadd : A -> A -> A := fun a b => Cadd a b. *)
  Hint Unfold Aadd : A.
  
  Infix "+" := Aadd : A_scope.

  #[export] Instance Aadd_AMonoid : AMonoid Aadd Azero.
  Proof. intros. repeat constructor; intros; autounfold with A; ring. Qed.
End MonoidElementTypeC.

Module MonoidElementTypeRFun <: MonoidElementType.
  Include ElementTypeRFun.
  
  Definition Aadd := faddR.
  Hint Unfold Aadd : A.
  
  Infix "+" := Aadd : A_scope.

  #[export] Instance Aadd_AMonoid : AMonoid Aadd Azero.
  Proof. intros. repeat constructor; intros; autounfold with A; ring. Qed.
End MonoidElementTypeRFun.

Module MonoidElementTypeFun (I O : MonoidElementType) <: MonoidElementType.
  (* Export I O. *)
  
  Include (ElementTypeFun I O).
  Open Scope A_scope.

  Definition Aadd (f g : A) : A := fun x : I.A => O.Aadd (f x) (g x).
  Hint Unfold Aadd : A.
  
  Infix "+" := Aadd : A_scope.

  Lemma Aadd_Associative : Associative Aadd.
  Proof.
    intros. constructor; intros; autounfold with A.
    extensionality x. apply O.Aadd_AMonoid.
  Qed.
  
  Lemma Aadd_Commutative : Commutative Aadd.
  Proof.
    intros. constructor; intros; autounfold with A.
    extensionality x. apply O.Aadd_AMonoid.
  Qed.
  
  Lemma Aadd_IdentityLeft : IdentityLeft Aadd Azero.
  Proof.
    intros. constructor; intros; autounfold with A.
    extensionality x. apply O.Aadd_AMonoid.
  Qed.
  
  Lemma Aadd_IdentityRight : IdentityRight Aadd Azero.
  Proof.
    intros. constructor; intros; autounfold with A.
    extensionality x. apply O.Aadd_AMonoid.
  Qed.

  #[export] Instance Aadd_AMonoid : AMonoid Aadd Azero.
  Proof.
    intros. constructor; intros; autounfold with A.
    intros. constructor; intros; autounfold with A.
    constructor. apply Aadd_Associative.
    apply Aadd_IdentityLeft. apply Aadd_IdentityRight.
    constructor. apply Aadd_Associative.
    apply Aadd_Commutative.
    constructor. constructor. apply Aadd_Associative.
    apply Aadd_Commutative.
  Qed.
End MonoidElementTypeFun.


Module MonoidElementTypeTest.
  Import MonoidElementTypeQc.
  Import MonoidElementTypeR.
  
  Module Import MonoidElementTypeFunEx1 :=
    MonoidElementTypeFun MonoidElementTypeQc MonoidElementTypeR.

  (* Definition f : A := fun i:Qc => Qc2R i + R1. *)
  (* Definition g : A := fun i:Qc => Qc2R (i+1). *)
  Definition f : A := fun i => 1.
  Definition g : A := fun i => 2.
  Definition h : A := fun i => 3.

  Goal f + g + h = f + (g + h).
  Proof. rewrite associative. auto. Qed.
End MonoidElementTypeTest.


(* ######################################################################### *)
(** * Element with abelian-ring structure *)

(** ** Type of Element with abelian-ring structure *)
(* Note, we won't use `ARingElementType` to emphasize the `abelian` property *)
Module Type RingElementType <: MonoidElementType.
  Include MonoidElementType.
  Open Scope A_scope.

  Parameter Aone : A.
  Parameter Amul : A -> A -> A.
  Parameter Aopp : A -> A.

  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "*" := Amul : A_scope.
  Notation "1" := Aone : A_scope.
  Notation "a ²" := (a * a) : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := Asub : A_scope.

  (** A Ring structure can be derived from the context *)
  Axiom ARing : ARing Aadd 0 Aopp Amul 1.
  
  #[export] Existing Instance ARing.

  (* Add Ring Ring_inst : (make_ring_theory ARing). *)
End RingElementType.

(** ** Instances *)

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

Module RingElementTypeQc <: RingElementType.
  Include MonoidElementTypeQc.

  Definition Aone : A := 1.
  Definition Aopp := Qcopp.
  Definition Amul := Qcmult.
  Hint Unfold Aone Aadd Aopp Amul : A.
  
  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := Asub : A_scope.
  
  #[export] Instance ARing : ARing Aadd Azero Aopp Amul Aone.
  Proof. repeat constructor; autounfold with A; intros; ring. Qed.
  
  Add Ring Ring_inst : (make_ring_theory ARing).
End RingElementTypeQc.

Module RingElementTypeR <: RingElementType.
  Include MonoidElementTypeR.
  
  Definition Aone : A := 1.
  Definition Aopp := Ropp.
  Definition Amul := Rmult.
  Hint Unfold Aone Aadd Aopp Amul : A.
  
  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := Asub : A_scope.

  #[export] Instance ARing : ARing Aadd Azero Aopp Amul Aone.
  Proof. repeat constructor; autounfold with A; intros; ring. Qed.
  
  (* Add Ring Ring_inst : (make_ring_theory ARing). *)
End RingElementTypeR.

Module RingElementTypeC <: RingElementType.
  Include MonoidElementTypeC.

  Definition Aone : A := 1.
  Definition Aopp := Copp.
  Definition Amul := Cmul.
  Hint Unfold Aone Aadd Aopp Amul : A.
  
  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := Asub : A_scope.

  #[export] Instance ARing : ARing Aadd Azero Aopp Amul Aone.
  Proof. repeat constructor; autounfold with A; intros; ring. Qed.
  
  Add Ring Ring_inst : (make_ring_theory ARing).
End RingElementTypeC.


Module RingElementTypeRFun <: RingElementType.
  Include MonoidElementTypeRFun.
  
  Definition Aone : A := foneR.
  Definition Aopp := foppR.
  Definition Amul := fmulR.
  Hint Unfold Aone Aadd Aopp Amul : A.
  
  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := Asub : A_scope.
  
  #[export] Instance ARing : ARing Aadd Azero Aopp Amul Aone.
  Proof.
    repeat constructor; intros;  autounfold with A;
      apply functional_extensionality; intros; cbv; ring.
  Qed.
  
  Add Ring Ring_inst : (make_ring_theory ARing).
End RingElementTypeRFun.


Module RingElementTypeFun (I O : RingElementType) <: RingElementType.
  (* Export I O. *)
  (* Add Ring Ring_thy_inst_i : (make_ring_theory I.ARing). *)
  Add Ring Ring_thy_inst_o : (make_ring_theory O.ARing).
  
  Include (MonoidElementTypeFun I O).

  Definition Aone : A := fun _ => O.Aone.
  Definition Aopp (f : A) : A := fun x : I.A => O.Aopp (f x).
  Definition Amul (f g : A) : A := fun x : I.A => O.Amul (f x) (g x).
  Notation Asub := (fun x y => Aadd x (Aopp y)).

  #[export] Instance ARing : ARing Aadd Azero Aopp Amul Aone.
  Proof.
    repeat constructor; autounfold with A; intros;
      apply functional_extensionality; intros; cbv; ring.
  Qed.
  
  Add Ring Ring_inst : (make_ring_theory ARing).
End RingElementTypeFun.


Module RingElementTypeTest.
  Import RingElementTypeQc.
  Import RingElementTypeR.
  
  Module Import RingElementTypeFunEx1 :=
    RingElementTypeFun RingElementTypeQc RingElementTypeR.
  
  Definition f : A := fun i:Qc => (Qc2R i + R1)%R.
  Definition g : A := fun i:Qc => Qc2R (i+1).

  Goal f = g.
  Proof. Abort.
End RingElementTypeTest.



(* ######################################################################### *)
(** * Element with abelian-ring structure and ordered relation *)

(** ** Type of Element with ordered abelian-ring structure *)
Module Type OrderedRingElementType <: RingElementType <: OrderedElementType.
  Include RingElementType.

  Parameter Alt Ale : A -> A -> Prop.

  Infix "<" := Alt : A_scope.
  Infix "<=" := Ale : A_scope.

  Axiom Order : Order Alt Ale.
  Axiom OrderedARing : OrderedARing Aadd Azero Aopp Amul Aone Alt Ale.
  #[export] Existing Instance OrderedARing.
  
  Notation "| a |" := (Aabs a) : A_scope.
  
End OrderedRingElementType.


(** ** Instances *)

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

Module OrderedRingElementTypeQc <: OrderedRingElementType.
  Include RingElementTypeQc.

  Definition Ale := Qcle.
  Definition Alt := Qclt.
  Hint Unfold Ale Alt : A.
  
  #[export] Instance Order : Order Alt Ale.
  Proof. apply OrderedElementTypeQc.Order. Qed.
  
  #[export] Instance OrderedARing
    : OrderedARing Aadd Azero Aopp Amul Aone Alt Ale.
  Proof.
    constructor. apply ARing. apply Order.
    - intros; autounfold with A in *. apply Qcplus_lt_compat_r; auto.
    - intros; autounfold with A in *. apply Qcmult_lt_compat_r; auto.
  Qed.
End OrderedRingElementTypeQc.

Module OrderedRingElementTypeR <: OrderedRingElementType.
  Include RingElementTypeR.
  
  Definition Ale := Rle.
  Definition Alt := Rlt.
  Hint Unfold Ale Alt : A.

  #[export] Instance Order : Order Alt Ale.
  Proof. apply OrderedElementTypeR.Order. Qed.
  
  #[export] Instance OrderedARing
    : OrderedARing Aadd Azero Aopp Amul Aone Alt Ale.
  Proof.
    constructor. apply ARing. apply Order.
    - intros; autounfold with A in *. lra.
    - intros; autounfold with A in *. apply Rmult_lt_compat_r; auto.
  Qed.

  Notation "| a |" := (Aabs a) : A_scope.
  
End OrderedRingElementTypeR.



(* ######################################################################### *)
(** * Element with field structure *)

(** ** Type of Element with field structure *)

Module Type FieldElementType <: RingElementType.
  Include RingElementType.
  Open Scope A_scope.

  Parameter Ainv : A -> A.

  Notation Adiv := (fun x y => Amul x (Ainv y)).
  Notation "/ a" := (Ainv a) : A_scope.
  Infix "/" := Adiv : A_scope.

  (** 1 <> 0. *)
  Axiom Aone_neq_Azero : Aone <> Azero.

  Axiom Field : Field Aadd Azero Aopp Amul Aone Ainv.

  #[export] Existing Instance Field.
  (* Add Field Field_inst : (make_field_theory Field). *)
End FieldElementType.


(** ** Instances *)

Module FieldElementTypeQc <: FieldElementType.
  Include RingElementTypeQc.

  Definition Ainv := Qcinv.
  Hint Unfold Ainv : A.
  
  Notation Adiv := (fun x y => Amul x (Ainv y)).

  Lemma Aone_neq_Azero : Aone <> Azero.
  Proof. intro. cbv in *. inv H. Qed.
  
  #[export] Instance Field : Field Aadd Azero Aopp Amul Aone Ainv.
  Proof.
    constructor. apply ARing.
    intros. autounfold with A. field. auto.
    apply Aone_neq_Azero.
  Qed.

  Add Field Field_inst : (make_field_theory Field).
End FieldElementTypeQc.

Module FieldElementTypeR <: FieldElementType.
  Include RingElementTypeR.
  
  Definition Ainv := Rinv.
  Hint Unfold Ainv : A.
  
  Notation Adiv := (fun x y => Amul x (Ainv y)).

  Lemma Aone_neq_Azero : Aone <> Azero.
  Proof. cbv in *. auto with real. Qed.

  #[export] Instance Field : Field Aadd Azero Aopp Amul Aone Ainv.
  Proof.
    constructor. apply ARing. intros.
    autounfold with A. field. auto.
    apply Aone_neq_Azero.
  Qed.

  (* Add Field Field_inst : (make_field_theory Field). *)
End FieldElementTypeR.

Module FieldElementTypeC <: FieldElementType.
  Include RingElementTypeC.
  
  Definition Ainv := Cinv.
  Hint Unfold Ainv : A.
  
  Notation Adiv := (fun x y => Amul x (Ainv y)).

  Lemma Aone_neq_Azero : Aone <> Azero.
  Proof. cbv in *. auto with complex. Qed.
  
  #[export] Instance Field : Field Aadd Azero Aopp Amul Aone Ainv.
  Proof.
    constructor. apply ARing. intros.
    autounfold with A. field. auto.
    apply Aone_neq_Azero.
  Qed.

  Add Field Field_inst : (make_field_theory Field).
End FieldElementTypeC.

(* Module FieldElementTypeFun (I O : FieldElementType) <: FieldElementType. *)
(*   Include (RingElementTypeFun I O). *)

(*   Definition Ainv : A -> A. *)
(*     cbv. intros [f Pf]. *)
(*     refine (exist _ (fun x : I.T => O.Ainv (f x)) _). *)
(*     constructor. intros. *)
(*     pose proof (O.Resp_Ainv_Teq). apply respectUnary. apply Pf; easy. *)
(*   Defined. *)
  
(*   Notation Adiv := (fun x y => Amul x (Ainv y)). *)

  (* Lemma Ainv_aeq_mor : Proper (Teq ==> Teq) Ainv. *)
  (* Proof. *)
  (*   unfold Proper, respectful. intros [x Px] [y Py] H1. *)
  (*   cbv in *. intros. apply O.Resp_Ainv_Teq; auto. *)
  (* Qed. *)
  
(*   (* Import FunctionalExtensionality. *) *)
(*   Lemma Aone_neq_Azero : ~(Aone == Azero)%T. *)
(*   Proof. cbv in *. intros. specialize (H I.Azero). apply O.Aone_neq_Azero in H. auto. Qed. *)

(*   Lemma Field_thy: field_theory Azero Aone Aadd Amul Asub Aopp Adiv Ainv Teq. *)
(*   Proof. *)
(*     destruct (I.Field_thy), (O.Field_thy). *)
(*     constructor. *)
(*     - apply Ring_thy. *)
(*     - apply Aone_neq_Azero. *)
(*     - intros. *)
(*       repeat match goal with | x:A |- _ => destruct x end. *)
(*       cbv in *; intros. *)
(*       pose proof (O.Amul_aeq_mor). *)
(*       pose proof (O.Equiv_Teq). *)
(*       apply H; easy. *)
(*     - intros. *)
(*       repeat match goal with | x:A |- _ => destruct x end. *)
(*       cbv in *; intros. *)
(*       apply Finv_l0. revert a. *)
(*       (* Note that, this is not true. *)
(*          H means: ~(x a1 = 0 /\ x a2 = 0 /\ ...) *)
(*          but we need: x a1 <> 0 /\ x a2 <> 0 /\ ... *)
(*          !!this is not provable. *)
(*        *) *)
(*       admit. *)
(*   Admitted. *)
(* End FieldElementTypeFun. *)

Module FieldElementTypeTest.
  Import FunctionalExtensionality.
  Import FieldElementTypeQc.
  Import FieldElementTypeR.

  (* Include (FieldElementTypeFun FieldElementTypeQ FieldElementTypeR). *)
End FieldElementTypeTest.


(* ######################################################################### *)
(** * Element with field structure and ordered relation *)

(** ** Type of Element with ordered field structure *)
Module Type OrderedFieldElementType <: FieldElementType <: OrderedRingElementType.
  Include FieldElementType.

  Parameter Alt Ale : A -> A -> Prop.

  Infix "<" := Alt : A_scope.
  Infix "<=" := Ale : A_scope.
  
  Axiom Order : Order Alt Ale.

  Axiom OrderedARing : OrderedARing Aadd Azero Aopp Amul Aone Alt Ale.
  #[export] Existing Instance OrderedARing.

  Axiom OrderedAField : OrderedField Aadd Azero Aopp Amul Aone Ainv Alt Ale.
  #[export] Existing Instance OrderedAField.

  Notation "| a |" := (Aabs a) : A_scope.
End OrderedFieldElementType.


(** ** Instances *)

Module OrderedFieldElementTypeQc <: OrderedFieldElementType.
  Include FieldElementTypeQc.

  Definition Ale := Qcle.
  Definition Alt := Qclt.
  Hint Unfold Ale Alt : A.

  #[export] Instance Order : Order Alt Ale.
  Proof. apply OrderedElementTypeQc.Order. Qed.
  
  #[export] Instance OrderedARing
    : OrderedARing Aadd Azero Aopp Amul Aone Alt Ale.
  Proof. apply OrderedRingElementTypeQc.OrderedARing. Qed.
  
  #[export] Instance OrderedAField
    : OrderedField Aadd Azero Aopp Amul Aone Ainv Alt Ale.
  Proof. constructor. apply Field. apply OrderedRingElementTypeQc.OrderedARing. Qed.
  
End OrderedFieldElementTypeQc.

Module OrderedFieldElementTypeR <: OrderedFieldElementType.
  Include FieldElementTypeR.
  
  Definition Ale := Rle.
  Definition Alt := Rlt.
  Hint Unfold Ale Alt : A.

  #[export] Instance Order : Order Alt Ale.
  Proof. apply OrderedElementTypeR.Order. Qed.
  
  #[export] Instance OrderedARing
    : OrderedARing Aadd Azero Aopp Amul Aone Alt Ale.
  Proof. apply OrderedRingElementTypeR.OrderedARing. Qed.
  
  #[export] Instance OrderedAField
    : OrderedField Aadd Azero Aopp Amul Aone Ainv Alt Ale.
  Proof. constructor. apply Field. apply OrderedRingElementTypeR.OrderedARing. Qed.

  Notation "| a |" := (Aabs a) : A_scope.

End OrderedFieldElementTypeR.



(* ######################################################################### *)
(** * Element with field structure and ordered relation and normed *)

(** ** Type of Element with normed ordered field structure *)
Module Type NormedOrderedFieldElementType <: OrderedFieldElementType.
  Include OrderedFieldElementType.
  Export RExt RFunExt.

  Parameter a2r : A -> R.
  Axiom A2R : A2R Aadd Azero Aopp Amul Aone Ainv Alt Ale a2r.
  #[export] Existing Instance A2R.
End NormedOrderedFieldElementType.


(** ** Instances *)

Module NormedOrderedFieldElementTypeQc <: NormedOrderedFieldElementType.
  Include OrderedFieldElementTypeQc.
  Export RExt RFunExt.

  Definition a2r := Qc2R.
  
  #[export] Instance A2R
    : A2R Aadd Azero Aopp Amul Aone Ainv Alt Ale a2r.
  Proof. apply Qc_A2R. Qed.
End NormedOrderedFieldElementTypeQc.

Module NormedOrderedFieldElementTypeR <: NormedOrderedFieldElementType.
  Include OrderedFieldElementTypeR.
  
  Definition a2r := id.
  
  #[export] Instance A2R
    : A2R Aadd Azero Aopp Amul Aone Ainv Alt Ale a2r.
  Proof. apply R_A2R. Qed.
End NormedOrderedFieldElementTypeR.
