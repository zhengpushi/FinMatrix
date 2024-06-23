(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : extension for Qc (canonical rational number).
  author    : Zhengpu Shi
  date      : 2022.07
*)


Require Export Qcanon.
Require Export QExt.
Require Import ListExt.

Open Scope Qc.


(* ######################################################################### *)
(** * Preliminary properties *)

(** - a + a = 0 *)
Lemma Qcplus_opp_l : forall a : Qc, - a + a = 0.
Proof. intros. rewrite Qcplus_comm. rewrite Qcplus_opp_r. auto. Qed.

(** ~ (a < a) *)
Lemma Qclt_irrefl : forall a : Qc, ~ (a < a).
Proof. intros. intro. apply Qclt_not_eq in H. easy. Qed.

(** a <> b -> a <= b -> a < b *)
Lemma Qcle_lt_strong : forall a b : Qc, a <> b -> a <= b -> a < b.
Proof.
  intros.
  destruct (Qc_dec a b) as [[H1|H1]|H1]; auto.
  - apply Qcle_not_lt in H0. easy.
  - subst. easy.
Qed.

(** c + a = c + b -> a = b *)
Lemma Qcplus_reg_l : forall a b c : Qc, c + a = c + b -> a = b.
Proof.
  intros.
  assert (-c + c + a = -c + c + b).
  { rewrite <- Qcplus_assoc. rewrite H. rewrite Qcplus_assoc. auto. }
  rewrite Qcplus_opp_l in H0. rewrite !Qcplus_0_l in H0. auto.
Qed.

(** a + c = b + c -> a = b *)
Lemma Qcplus_reg_r : forall a b c : Qc, a + c = b + c -> a = b.
Proof.
  intros.
  assert (a + c + -c = b + c + -c). { rewrite H. auto. }
  rewrite <- !Qcplus_assoc in H0. rewrite Qcplus_opp_r in H0.
  rewrite !Qcplus_0_r in H0. auto.
Qed.

(** b < c -> a + b < a + c *)
Lemma Qcplus_lt_compat_l : forall a b c : Qc, b < c -> a + b < a + c.
Proof.
  intros. destruct (Qc_eq_dec b c) as [H1|H1].
  - subst. apply Qclt_not_eq in H. easy.
  - pose proof (Qcplus_le_compat a a b c).
    assert (a <= a). apply Qcle_refl.
    assert (b <= c). apply Qclt_le_weak; auto.
    specialize (H0 H2 H3).
    apply Qcle_lt_or_eq in H0. destruct H0; auto.
    assert (-a + (a + b) = -a + (a + c)). rewrite H0; auto.
    rewrite !Qcplus_assoc in H4. rewrite !Qcplus_opp_l,!Qcplus_0_l in H4. easy.
Qed.

(** a < b -> a + c < b + c *)
Lemma Qcplus_lt_compat_r : forall a b c : Qc, a < b -> a + c < b + c.
Proof. intros. rewrite !(Qcplus_comm _ c). apply Qcplus_lt_compat_l; auto. Qed.

(** a < b -> 0 < c -> c * a < c * b *)
Lemma Qcmult_lt_compat_l : forall a b c : Qc, a < b -> 0 < c -> c * a < c * b.
Proof. intros. rewrite !(Qcmult_comm c). apply Qcmult_lt_compat_r; auto. Qed.

  
(* ######################################################################### *)
(** * Algebraic Structures *)

(** equality is equivalence relation: Equivalence eq *)
Hint Resolve eq_equivalence : Qc.

(** operations are well-defined. Eg: Proper (eq ==> eq ==> eq) Qcplus *)

Lemma Qcadd_wd : Proper (eq ==> eq ==> eq) Qcplus.
Proof. repeat (hnf; intros); subst; auto. Qed.

Lemma Qcopp_wd : Proper (eq ==> eq) Qcopp.
Proof. repeat (hnf; intros); subst; auto. Qed.

Lemma Qcsub_wd : Proper (eq ==> eq ==> eq) Qcminus.
Proof. repeat (hnf; intros); subst; auto. Qed.

Lemma Qcmul_wd : Proper (eq ==> eq ==> eq) Qcmult.
Proof. repeat (hnf; intros); subst; auto. Qed.

Lemma Qcinv_wd : Proper (eq ==> eq) Qcinv.
Proof. repeat (hnf; intros); subst; auto. Qed.

Lemma Qcdiv_wd : Proper (eq ==> eq ==> eq) Qcdiv.
Proof. repeat (hnf; intros); subst; auto. Qed.

Hint Resolve
  Qcadd_wd Qcopp_wd Qcsub_wd
  Qcmul_wd Qcinv_wd Qcdiv_wd : Qc.

(** Decidable *)

Instance Qc_eq_Dec : Dec (@eq Qc).
Proof. constructor. apply Qc_eq_dec. Defined.

Instance Qc_lt_Dec : Dec Qclt.
Proof.
  constructor. intros. destruct (Qclt_le_dec a b); auto.
  right. intro. apply Qcle_not_lt in q. easy.
Defined.

Instance Qc_le_Dec : Dec Qcle.
Proof.
  constructor. intros. destruct (Qclt_le_dec b a); auto.
  right. intro. apply Qcle_not_lt in H. easy.
Defined.

(** Associative *)

Instance Qcadd_Assoc : Associative Qcplus.
Proof. constructor; intros; field. Qed.

Instance Qcmul_Assoc : Associative Qcmult.
Proof. constructor; intros; field. Qed.

Hint Resolve Qcadd_Assoc Qcmul_Assoc : Qc.

(** Commutative *)

Instance Qcadd_Comm : Commutative Qcplus.
Proof. constructor; intros; field. Qed.

Instance Qcmul_Comm : Commutative Qcmult.
Proof. constructor; intros; field. Qed.

Hint Resolve Qcadd_Comm Qcmul_Comm : Qc.

(** Identity Left/Right *)

Instance Qcadd_IdL : IdentityLeft Qcplus 0.
Proof. constructor; intros; field. Qed.

Instance Qcadd_IdR : IdentityRight Qcplus 0.
Proof. constructor; intros; field. Qed.

Instance Qcmul_IdL : IdentityLeft Qcmult 1.
Proof. constructor; intros; field. Qed.

Instance Qcmul_IdR : IdentityRight Qcmult 1.
Proof. constructor; intros; field. Qed.

Hint Resolve
  Qcadd_IdL Qcadd_IdR
  Qcmul_IdL Qcmul_IdR : Qc.

(** Inverse Left/Right *)

Instance Qcadd_InvL : InverseLeft Qcplus 0 Qcopp.
Proof. constructor; intros; ring. Qed.

Instance Qcadd_InvR : InverseRight Qcplus 0 Qcopp.
Proof. constructor; intros; ring. Qed.

Hint Resolve Qcadd_InvL Qcadd_InvR : Qc.

(** Distributive *)

Instance Qcmul_add_DistrL : DistrLeft Qcplus Qcmult.
Proof. constructor; intros; field. Qed.

Instance Qcmul_add_DistrR : DistrRight Qcplus Qcmult.
Proof. constructor; intros; field. Qed.

Hint Resolve
  Qcmul_add_DistrL
  Qcmul_add_DistrR
  : Qc.

(** Semigroup *)

Instance Qcadd_SGroup : SGroup Qcplus.
Proof. constructor; auto with Qc. Qed.

Instance Qcmul_SGroup : SGroup Qcmult.
Proof. constructor; auto with Qc. Qed.

Hint Resolve
  Qcadd_SGroup
  Qcmul_SGroup
  : Qc.

(** Abelian semigroup *)

Instance Qcadd_ASGroup : ASGroup Qcplus.
Proof. constructor; auto with Qc. Qed.

Instance Qcmul_ASGroup : ASGroup Qcmult.
Proof. constructor; auto with Qc. Qed.

Hint Resolve
  Qcadd_ASGroup
  Qcmul_ASGroup
  : Qc.

(** Monoid *)
  
Instance Qcadd_Monoid : Monoid Qcplus 0.
Proof. constructor; auto with Qc. Qed.

Instance Qcmul_Monoid : Monoid Qcmult 1.
Proof. constructor; auto with Qc. Qed.

Hint Resolve
  Qcadd_Monoid
  Qcmul_Monoid
  : Qc.

(** Abelian monoid *)
  
Instance Qcadd_AMonoid : AMonoid Qcplus 0.
Proof. constructor; auto with Qc. Qed.
  
Instance Qcmul_AMonoid : AMonoid Qcmult 1.
Proof. constructor; auto with Qc. Qed.

Hint Resolve Qcadd_AMonoid Qcmul_AMonoid : Qc.

(** Group *)

Instance Qcadd_Group : Group Qcplus 0 Qcopp.
Proof. constructor; auto with Qc. Qed.
Hint Resolve Qcadd_Group : Qc.

(** AGroup *)

Instance Qcadd_AGroup : AGroup Qcplus 0 Qcopp.
Proof. constructor; auto with Qc. Qed.
Hint Resolve Qcadd_AGroup : Qc.

(** SRing *)

Instance Qc_SRing : SRing Qcplus 0 Qcmult 1.
Proof. constructor; auto with Qc; intros; ring. Qed.
Hint Resolve Qc_SRing : Qc.

(** Ring *)

Instance Qc_Ring : Ring Qcplus 0 Qcopp Qcmult 1.
Proof. constructor; auto with Qc. Qed.
Hint Resolve Qc_Ring : Qc.

(** ARing *)

Instance Qc_ARing : ARing Qcplus 0 Qcopp Qcmult 1.
Proof. constructor; auto with Qc. Qed.

Hint Resolve Qc_ARing : Qc.

(** Field *)

Instance Qc_Field : Field Qcplus 0 Qcopp Qcmult 1 Qcinv.
Proof.
  constructor; auto with Qc.
  - intros. field; auto.
  - intro. easy.
Qed.

Hint Resolve Qc_Field : Qc.

(** Order *)

Instance Qc_Order : Order Qclt Qcle.
Proof.
  constructor; intros; try lia; auto with Qc; auto with qarith.
  - intro. apply Qclt_not_eq in H. easy.
  - apply Qclt_trans with b; auto.
  - apply Qc_dec.
  - split; intros.
    apply Qcle_lt_or_eq; auto. destruct H.
    apply Qclt_le_weak; auto. subst. apply Qcle_refl.
Qed.

Hint Resolve Qc_Order : Qc.

Instance Qc_OrderedARing :
  OrderedARing Qcplus 0 Qcopp Qcmult 1 Qclt Qcle.
Proof.
  constructor; auto with Qc.
  - apply Qcplus_lt_compat_r.
  - intros. apply Qcmult_lt_compat_r; auto.
Qed.

Hint Resolve Qc_OrderedARing : Qc.

Instance Qc_OrderedField :
  OrderedField Qcplus 0 Qcopp Qcmult 1 Qcinv Qclt Qcle.
Proof. constructor; auto with Qc. Qed.

Hint Resolve Qc_OrderedField : Qc.

(* (** Bool version of "<" and "<=" for Qc *) *)
(* Definition Qcltb (a b : Qc) : bool := if Qclt_le_dec a b then true else false. *)
(* Definition Qcleb (a b : Qc) : bool := if Qclt_le_dec b a then false else true. *)
(* Infix "<?" := Qcltb : Qc_scope. *)
(* Infix "<=?" := Qcleb : Qc_scope. *)

(* Lemma Qcltb_reflect : forall a b : Qc, reflect (a < b) (a <? b). *)
(* Proof. *)
(*   intros. unfold Qcltb. destruct Qclt_le_dec; constructor; auto. *)
(*   apply Qcle_not_lt; auto. *)
(* Qed. *)

(* Lemma Qcleb_reflect : forall a b : Qc, reflect (a <= b) (a <=? b). *)
(* Proof. *)
(*   intros. unfold Qcleb. destruct Qclt_le_dec; constructor; auto. *)
(*   apply Qclt_not_le; auto. *)
(* Qed. *)

(* Instance Qc_Order : Order Qclt Qcle. *)
(* Proof. *)
(*   constructor; intros; auto with Qc. ? *)
(*   - split; intros. apply Qcle_lt_or_eq; auto. destruct H. *)
(*     apply Qclt_le_weak; auto. subst. apply Qcle_refl. *)
(*   - apply Qc_lt_irrefl. *)
(*   - pose proof (Qclt_trans a b a H H0). apply Qc_lt_irrefl in H1. easy. *)
(*   - apply Qclt_trans with b; auto. *)
(*   - apply Qc_dec. *)
(*   - apply Qcltb_reflect. *)
(*   - apply Qcleb_reflect. *)
(* Qed. *)

(* Section test. *)
(*   Goal forall a b : Qc, {a = b} + {a <> b}. *)
(*   Proof. intros. apply Aeqdec. Abort. *)
(* End test. *)


(* ######################################################################### *)
(** * Instances for ElementType *)

Module ElementTypeQc <: ElementType.
  Definition tA : Type := Qc.
  Definition Azero : tA := 0.
  Hint Unfold tA Azero : tA.

  Lemma AeqDec : Dec (@eq tA).
  Proof. apply Qc_eq_Dec. Defined.

End ElementTypeQc.

Module OrderedElementTypeQc <: OrderedElementType.
  Include ElementTypeQc.

  Definition Alt := Qclt.
  Definition Ale := Qcle.
  Hint Unfold Ale Alt : tA.

  Instance Order : Order Alt Ale.
  Proof. apply Qc_Order. Qed.
End OrderedElementTypeQc.

Module MonoidElementTypeQc <: MonoidElementType.
  Include ElementTypeQc.

  Definition Aadd := Qcplus.
  Hint Unfold Aadd : tA.
  
  Infix "+" := Aadd : A_scope.

  Instance Aadd_AMonoid : AMonoid Aadd Azero.
  Proof. intros. repeat constructor; intros; autounfold with tA; ring. Qed.
End MonoidElementTypeQc.

Module RingElementTypeQc <: RingElementType.
  Include MonoidElementTypeQc.

  Definition Aone : tA := 1.
  Definition Aopp := Qcopp.
  Definition Amul := Qcmult.
  Hint Unfold Aone Aadd Aopp Amul : tA.
  
  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := Asub : A_scope.

  Instance SRing : SRing Aadd Azero Amul Aone.
  Proof. repeat constructor; autounfold with tA; intros; ring. Qed.
  
  Instance ARing : ARing Aadd Azero Aopp Amul Aone.
  Proof. repeat constructor; autounfold with tA; intros; ring. Qed.
  
  Add Ring Ring_inst : (make_ring_theory ARing).
End RingElementTypeQc.

Module OrderedRingElementTypeQc <: OrderedRingElementType.
  Include RingElementTypeQc.

  Definition Ale := Qcle.
  Definition Alt := Qclt.
  Hint Unfold Ale Alt : tA.
  
  Instance Order : Order Alt Ale.
  Proof. apply OrderedElementTypeQc.Order. Qed.
  
  Instance OrderedARing
    : OrderedARing Aadd Azero Aopp Amul Aone Alt Ale.
  Proof.
    constructor. apply ARing. apply Order.
    - intros; autounfold with tA in *. apply Qcplus_lt_compat_r; auto.
    - intros; autounfold with tA in *. apply Qcmult_lt_compat_r; auto.
  Qed.
End OrderedRingElementTypeQc.

Module FieldElementTypeQc <: FieldElementType.
  Include RingElementTypeQc.

  Definition Ainv := Qcinv.
  Hint Unfold Ainv : tA.
  
  Notation Adiv := (fun x y => Amul x (Ainv y)).

  Lemma Aone_neq_Azero : Aone <> Azero.
  Proof. intro. cbv in *. inv H. Qed.
  
  Instance Field : Field Aadd Azero Aopp Amul Aone Ainv.
  Proof.
    constructor. apply ARing.
    intros. autounfold with tA. field. auto.
    apply Aone_neq_Azero.
  Qed.

  Add Field Field_inst : (make_field_theory Field).
End FieldElementTypeQc.

Module OrderedFieldElementTypeQc <: OrderedFieldElementType.
  Include FieldElementTypeQc.

  Definition Ale := Qcle.
  Definition Alt := Qclt.
  Hint Unfold Ale Alt : tA.

  Instance Order : Order Alt Ale.
  Proof. apply OrderedElementTypeQc.Order. Qed.
  
  Instance OrderedARing
    : OrderedARing Aadd Azero Aopp Amul Aone Alt Ale.
  Proof. apply OrderedRingElementTypeQc.OrderedARing. Qed.
  
  Instance OrderedAField
    : OrderedField Aadd Azero Aopp Amul Aone Ainv Alt Ale.
  Proof. constructor. apply Field. apply OrderedRingElementTypeQc.OrderedARing. Qed.
  
End OrderedFieldElementTypeQc.


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
(** ** Convertion between Qc and other types *)

(** If two Q type value are equal, then its canonical form are equal *)
Lemma Qcmake_inversion : forall (q1 q2 : Q) (H1 : Qred q1 = q1) (H2 : Qred q2 = q2),
    q1 = q2 -> Qcmake q1 H1 = Qcmake q2 H2.
Proof.
  intros.
  f_equal.  (* Tips, f_equal has no effect on recrods of dependent types  *)
  subst. 
  f_equal. apply proof_irrelevance.
Qed.

(** Q2Qc q1 = Q2Qc q2 -> q1 == q2 *)
Lemma Q2Qc_inj : forall (q1 q2 : Qc), Q2Qc q1 = Q2Qc q2 -> q1 == q2.
Proof. intros. apply Q2Qc_eq_iff in H. auto. Qed.


(** Qc to Q *)
Definition Qc2Q (x : Qc) : Q := this x.

(** Qc2Q qc1 = Qc2Q qc2 -> qc1 = qc2 *)
Lemma Qc2Q_inj : forall (qc1 qc2 : Qc), Qc2Q qc1 = Qc2Q qc2 -> qc1 = qc2.
Proof.
  intros. destruct qc1,qc2. simpl in *. subst. f_equal. apply proof_irrelevance.
Qed.

(** Q2Qc (Qc2Q qc) = qc *)
Lemma Q2Qc_Qc2Q : forall (qc : Qc), Q2Qc (Qc2Q qc) = qc.
Proof.
  intros. unfold Qc2Q. unfold Q2Qc. destruct qc. simpl.
  f_equal.  (* Tips, f_equal has no effect on recrods of dependent types  *)
  apply Qcmake_inversion. auto.
Qed.

(** list Q to list Qc *)
Definition listQ2Qc l := map Q2Qc l.

(** list Qc to list Q, for better printing *)
Definition listQc2Q l := map Qc2Q l.

(** listQ2Qc (listQc2Q l) = l *)
Lemma listQ2Qc_listQc2Q : forall (l : list Qc), listQ2Qc (listQc2Q l) = l.
Proof.
  intros. unfold listQ2Qc, listQc2Q. rewrite map_map.
  rewrite map_ext with (g:=fun x => x). apply map_id; auto.
  intros. rewrite Q2Qc_Qc2Q. auto.
Qed.

(** dlist Q to dlist Qc *)
Definition dlistQ2Qc dl := map listQ2Qc dl.

(** dlist Qc to dlist Q *)
Definition dlistQc2Q dl := map listQc2Q dl.

(** dlistQ2Qc (dlistQc2Q dl) = dl *)
Lemma dlistQ2Qc_dlistQc2Q : forall (dl : list (list Qc)), dlistQ2Qc (dlistQc2Q dl) = dl.
Proof.
  intros. unfold dlistQ2Qc, dlistQc2Q. rewrite map_map.
  rewrite map_ext with (g:=fun x => x). apply map_id; auto.
  intros. rewrite listQ2Qc_listQc2Q. auto.
Qed.


(** Z to Qc *)
Definition Z2Qc (x : Z) : Qc := Q2Qc (Z2Q x).

(** nat to Qc *)
Definition nat2Qc (x : nat) : Qc := Q2Qc (nat2Q x).

(** Qc to Z *)
Definition Qc2Z_ceiling (q : Qc) : Z := Q2Z_ceiling (Qc2Q q).
Definition Qc2Z_floor (q : Qc) : Z := Q2Z_floor (Qc2Q q).


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
(** ** Others *)


(** ** Sqrt of Q *)

(* Definition Qsqrt (q : Q) := Qmake (Z.sqrt (Qnum q)) (Pos.sqrt (Qden q)). *)

(* Example *)
(* Compute Qsqrt 1.21. *)
