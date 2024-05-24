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

Module ElementTypeFun (I O : ElementType) <: ElementType.
  Definition A : Type := I.A -> O.A.
  Definition Azero : A := fun _ => O.Azero.
  Hint Unfold A Azero : A.

  Lemma AeqDec : Dec (@eq A).
  Proof. constructor. intros a b. unfold A in *.
  Admitted.
End ElementTypeFun.


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

(* Module FieldElementTypeTest. *)
(*   Import FunctionalExtensionality. *)
(*   Import FieldElementTypeQc. *)
(*   Import FieldElementTypeR. *)

(*   (* Include (FieldElementTypeFun FieldElementTypeQ FieldElementTypeR). *) *)
(* End FieldElementTypeTest. *)


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


(* ######################################################################### *)
(** * Element with field structure and ordered relation and normed *)

(** ** Type of Element with normed ordered field structure *)
Module Type NormedOrderedFieldElementType <: OrderedFieldElementType.
  Include OrderedFieldElementType.
  Import Reals.

  Parameter a2r : A -> R.
  Axiom A2R : A2R Aadd Azero Aopp Amul Aone Ainv Alt Ale a2r.
  #[export] Existing Instance A2R.
End NormedOrderedFieldElementType.

(** ** Instances *)

