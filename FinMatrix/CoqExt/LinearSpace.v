(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector Space
  author    : ZhengPu Shi
  date      : 2024.01

  reference :
  1. 丘维声《高等代数》，第2版，清华大学出版社，2019
  2. Handbook of linear algebra, Leslie Hogben
Linear Algebra As an Introduction to Abstract Mathematics
  
  remark    :
  1. 向量空间推广到一般情形后称为线性空间，也简称为向量空间。
  2. ref : https://www.maths.tcd.ie/~dwilkins/Courses/111/vspace.pdf
 *)

Require Export Hierarchy.
(* Require Export Matrix. *)
(* Require Export MatrixInv. *)

Set Implicit Arguments.
Unset Strict Implicit.

Generalizable Variables A Aadd Azero Aopp Amul Aone Ainv Adiv Alt Ale
  V Vadd Vzero Vopp Vcmul
  W Wadd Wzero Wopp Wcmul.
Generalizable Variables B Badd Bzero.
Generalizable Variables C Cadd Czero.

Declare Scope VectorSpace_scope.
Delimit Scope VectorSpace_scope with VS.

Open Scope A_scope.
(* Open Scope vec_scope. *)
Open Scope VectorSpace_scope.

(* ===================================================================== *)
(** ** Additional properties *)
Section vsum.
(*   Context `{AMonoid : Monoid A Aadd Azero}. *)
(*   Context `{BMonoid : Monoid B Badd Bzero}. *)

(*   (** ∑(f a.i) = f (∑a) *) *)
(*   Lemma vsum_vmap : forall {n} (f : A -> B) (a : @vec A n), *)
(*       (f Azero = Bzero) -> *)
(*       (forall a b : A, f (Aadd a b) = Badd (f a) (f b)) -> *)
(*       @vsum _ Badd Bzero _ (vmap f a) = f (@vsum _ Aadd Azero _ a). *)
(*   Proof. *)
(*     intros. unfold vmap. unfold vec in *. induction n. *)
(*     - cbv. auto. *)
(*     - rewrite vsumS_tail. rewrite IHn. rewrite <- H0. f_equal. *)
(*       rewrite vsumS_tail. auto. *)
(*   Qed. *)

  Context {C : Type}.
  Context `{CMonoid : Monoid C Cadd Czero}.
  
  (* (** ∑(f u.i v.i) = f (∑u) (∑v) *) *)
  (* Lemma vsum_vmap2 : forall {n m} (f : A -> B -> E) (u : @vec A n) (v : @vec B m), *)
  (*     (* (f Azero = Bzero) -> *) *)
  (*     (* (forall a b : A, f (Aadd a b) = Badd (f a) (f b)) -> *) *)
  (*     @vsum _ Badd Bzero _ (vmap2 f u v) = *)
  (*     f (@vsum _ Aadd Azero _ u) (@vsum _ Badd Bzero _ v). *)
  (* Proof. *)
  (*   intros. unfold vec in *. induction n. *)
  (*   - cbv. auto. *)
  (*   - rewrite vsumS_tail. rewrite H0. rewrite IHn. *)
  (*     rewrite vsumS_tail. unfold vmap. auto. *)
  (* Qed. *)
  
End vsum.


(* ===================================================================== *)
(** ** Linear Space *)

(* elements of V called vectors, and elements of K called scalars  *)
Class VectorSpace `{F : Field} {V : Type} (Vadd : V -> V -> V) (Vzero : V)
  (Vopp : V -> V) (Vcmul : A -> V -> V) := {
    vs_vaddC :: Commutative Vadd;
    vs_vaddA :: Associative Vadd;
    vs_vaddIdR :: IdentityRight Vadd Vzero;
    vs_vaddInvR :: InverseRight Vadd Vzero Vopp;
    vs_vcmul_1_l : forall v : V, Vcmul Aone v = v;
    vs_vcmul_assoc : forall a b v, Vcmul (Amul a b) v = Vcmul a (Vcmul b v);
    vs_vcmul_aadd : forall a b v, Vcmul (Aadd a b) v = Vadd (Vcmul a v) (Vcmul b v);
    vs_vcmul_vadd : forall a u v, Vcmul a (Vadd u v) = Vadd (Vcmul a u) (Vcmul a v);
  }.

(** A field itself is a linear space *)
Section field_VectorSpace.
  Context `{HField : Field}.
  Add Field field_inst : (make_field_theory HField).
  
  #[export] Instance field_VectorSpace : VectorSpace Aadd Azero Aopp Amul.
  Proof. split_intro; try field. Qed.
End field_VectorSpace.

(** a real function is a linear space *)
(* ToDo *)

Section props.
  Context `{HVectorSpace : VectorSpace}.
  Add Field field_inst : (make_field_theory F).
  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + -b).
  Infix "-" := Asub : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "1" := Aone : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv := (fun a b => a * (/b)).
  Infix "/" := Adiv : A_scope.

  Infix "+" := Vadd : VectorSpace_scope.
  Notation "0" := Vzero : VectorSpace_scope.
  Notation "- v" := (Vopp v) : VectorSpace_scope.
  Notation Vsub u v := (u + -v).
  Infix "-" := Vsub : VectorSpace_scope.
  Infix "c*" := Vcmul : VectorSpace_scope.

  (** 0 + v = v *)
  #[export] Instance vs_vaddIdL : IdentityLeft Vadd 0.
  Proof. constructor; intros. rewrite commutative, identityRight; auto. Qed.
  
  (** -v + v = 0 *)
  #[export] Instance vs_vaddInvL : InverseLeft Vadd 0 Vopp.
  Proof. constructor; intros. rewrite commutative, inverseRight; auto. Qed.
  
  (** 0 + v = v *)
  Lemma vs_vadd_0_l : forall v : V, 0 + v = v.
  Proof. intros. apply identityLeft. Qed.
  
  (** v + 0 = v *)
  Lemma vs_vadd_0_r : forall v : V, v + 0 = v.
  Proof. intros. apply identityRight. Qed.
  
  (** - v + v = 0 *)
  Lemma vs_vadd_vopp_l : forall v : V, - v + v = 0.
  Proof. intros. apply inverseLeft. Qed.
  
  (** v + - v = 0 *)
  Lemma vs_vadd_vopp_r : forall v : V, v + - v = 0.
  Proof. intros. apply inverseRight. Qed.
  
  (** <+,0,-v> forms an abelian-group *)
  #[export] Instance vs_vadd_AGroup : AGroup Vadd 0 Vopp.
  Proof.
    repeat constructor; intros;
      try apply vs_vaddA;
      try apply vs_vadd_0_l;
      try apply vs_vadd_0_r;
      try apply vs_vadd_vopp_l;
      try apply vs_vadd_vopp_r;
      try apply vs_vaddC.
  Qed.

  (** Cancellation law *)
  
  (** u + v = u + w -> v = w *)
  Theorem vs_cancel_l : forall u v w, u + v = u + w -> v = w.
  Proof. intros. apply group_cancel_l in H; auto. Qed.
  
  (** v + u = w + u -> v = w *)
  Theorem vs_cancel_r : forall u v w, v + u = w + u -> v = w.
  Proof. intros. apply group_cancel_r in H; auto. Qed.

  (** u + v = v -> u = 0 *)
  Theorem vs_add_eqR_imply0 : forall u v, u + v = v -> u = 0.
  Proof.
    intros. apply vs_cancel_r with (u:=v). rewrite H.
    pose proof vs_vadd_AGroup. agroup.
  Qed.
  
  (** u + v = u -> v = 0 *)
  Theorem vs_add_eqL_imply0 : forall u v, u + v = u -> v = 0.
  Proof.
    intros. apply vs_cancel_l with (u:=u). rewrite H.
    pose proof vs_vadd_AGroup. agroup.
  Qed.

  (** Vzero is unique *)
  Theorem vs_vzero_uniq_l : forall v0, (forall v, v0 + v = v) -> v0 = 0.
  Proof. intros. apply group_id_uniq_l; auto. Qed.
  
  Theorem vs_vzero_uniq_r : forall v0, (forall v, v + v0 = v) -> v0 = 0.
  Proof. intros. apply group_id_uniq_r; auto. Qed.

  (** (-v) is unique *)
  Theorem vs_vopp_uniq_l : forall v v', v + v' = 0 -> -v = v'.
  Proof. intros. eapply group_opp_uniq_l; auto. Qed.
  
  Theorem vs_vopp_uniq_r : forall v v', v' + v = 0 -> -v = v'.
  Proof. intros. eapply group_opp_uniq_r; auto. Qed.
  
  (** 0 .* v = 0 *)
  Theorem vs_vcmul_0_l : forall v : V, 0%A c* v = 0.
  Proof.
    (* 0 .* v = (0 + 0) .* v = 0 .* v + 0 .* v, 0 .* v = 0 + 0 .* v,
       Hence, 0 .* v + 0 .* v = 0 + 0 .* v. By the cancellation law, then ... *)
    intros. pose proof vs_vadd_AGroup as HAGroup_vadd.
    assert (0%A c* v + 0%A c* v = 0%A c* v + 0).
    - rewrite <- vs_vcmul_aadd. agroup. f_equal. field.
    - apply vs_cancel_l in H. auto.
  Qed.

  (** a .* 0 = 0 *)
  Theorem vs_vcmul_0_r : forall a : A, a c* 0 = 0.
  Proof.
    (* a*0 = a*0 + 0, a*0 = a*(0 + 0) = a*0 + a*0,
       Thus, a*0 + 0 = a*0 + a*0. By the cancellation law, then ... *)
    intros. pose proof vs_vadd_AGroup as HAGroup_vadd.
    assert (a c* 0 = a c* 0 + a c* 0).
    { rewrite <- vs_vcmul_vadd. f_equal. agroup. }
    assert (a c* 0 = a c* 0 + 0). agroup.
    rewrite H in H0 at 1. apply vs_cancel_l in H0. auto.
  Qed.

  (** u + v = w -> u = w + - v *)
  Theorem vs_sol_l : forall u v w, u + v = w -> u = w + - v.
  Proof. intros. apply group_sol_l; auto. Qed.

  (** u + v = w -> v = - u + w *)
  Theorem vs_sol_r : forall u v w, u + v = w -> v = - u + w.
  Proof. intros. apply group_sol_r; auto. Qed.
  
  (** (- c) * v = - (c * v) *)
  Theorem vs_vcmul_opp : forall c v, (- c)%A c* v = - (c c* v).
  Proof.
    (* c*v + (-c)*v = 0, So, ... *)
    intros. symmetry. apply vs_vopp_uniq_l; auto.
    rewrite <- vs_vcmul_aadd. rewrite inverseRight, vs_vcmul_0_l; auto.
  Qed.
  
  (** c * (- v) = - (c * v) *)
  Theorem vs_vcmul_vopp : forall c v, c c* (- v) = - (c c* v).
  Proof.
    (* c*v + c*(-v) = 0, So, ... *)
    intros. symmetry. apply vs_vopp_uniq_l; auto.
    rewrite <- vs_vcmul_vadd. rewrite inverseRight, vs_vcmul_0_r; auto.
  Qed.
  
  (** (-1) * v = - v *)
  Theorem vs_vcmul_opp1 : forall v : V, (-(1))%A c* v = -v.
  Proof. intros. rewrite vs_vcmul_opp, vs_vcmul_1_l; auto. Qed.

  (** v - v = 0 *)
  Theorem vs_vsub_self : forall v : V, v - v = 0.
  Proof. intros. pose proof vs_vadd_AGroup as HAGroup_vadd. agroup. Qed.

  Section AeqDec.
    Context {AeqDec : Dec (@eq A)}.
    
    (** a .* v = 0 -> a = 0 \/ v = 0 *)
    Theorem vs_vcmul_eq0_imply_k0_or_v0 : forall a v, a c* v = 0 -> a = 0%A \/ v = 0.
    Proof.
      intros. destruct (Aeqdec a 0%A); auto. right.
      assert (/a c* (a c* v) = /a c* 0) by (rewrite H; auto).
      rewrite <- vs_vcmul_assoc in H0.
      rewrite field_mulInvL in H0; auto.
      rewrite vs_vcmul_1_l, vs_vcmul_0_r in H0. auto.
    Qed.

    (** a <> 0 -> v <> 0 -> a .* v <> 0 *)
    Corollary vs_vcmul_neq0_if_neq0_neq0 : forall a v, a <> 0%A -> v <> 0 -> a c* v <> 0.
    Proof.
      intros. intro. apply vs_vcmul_eq0_imply_k0_or_v0 in H1. destruct H1; auto.
    Qed.
  End AeqDec.
  
End props.


(* ===================================================================== *)
(** ** Linear subspace (simply called subspace) from a linear space *)

(* A subset of vectors H ⊆ V from a linear space (V,F) forms a vector 
   subspace if the following three properties hold:
   1. The zero vector of V is in H
   2. H is closed under vector addition.
   3. H is closed under scalar multiplication. *)

(* The struct of a subspace. Here, H := {x | P x} *)
Class SubSpaceStruct `{HVectorSpace : VectorSpace} (P : V -> Prop) := {
    ss_zero_keep : P Vzero;
    ss_add_closed : forall {u v : sig P}, P (Vadd u.val v.val);
    ss_cmul_closed : forall {a : A} {v : sig P}, P (Vcmul a v.val);
  }.

(* Is an element belong to H *)
Definition Hbelong `{ss: SubSpaceStruct} (v : V) : Prop := P v.

Section makeSubSpace.
  Context `{ss : SubSpaceStruct}.
  
  (* A subst of vectors H ⊆ V *)
  Notation H := (sig P).

  (* operations on H *)
  Definition Hadd (u v : H) : H := exist _ (Vadd u.val v.val) ss_add_closed.
  Definition Hzero : H := exist _ Vzero ss_zero_keep.
  Definition Hopp (v : H) : H.
    refine (exist _ (Vopp v.val) _). rewrite <- vs_vcmul_opp1.
    apply ss_cmul_closed.
  Defined.
  Definition Hcmul (a : A) (v : H) : H := exist _ (Vcmul a v.val) ss_cmul_closed.

  Lemma makeSubSpace : VectorSpace Hadd Hzero Hopp Hcmul.
  Proof.
    repeat constructor; unfold Hadd, Hcmul; intros.
    - apply sig_eq_iff. apply commutative.
    - apply sig_eq_iff. simpl. apply associative.
    - destruct a. apply sig_eq_iff. simpl. apply identityRight.
    - destruct a. apply sig_eq_iff. simpl. apply vs_vadd_vopp_r.
    - destruct v. apply sig_eq_iff. simpl. apply vs_vcmul_1_l.
    - destruct v. apply sig_eq_iff. simpl. apply vs_vcmul_assoc.
    - destruct v. apply sig_eq_iff. simpl. apply vs_vcmul_aadd.
    - destruct v. apply sig_eq_iff. simpl. apply vs_vcmul_vadd.
  Qed.
End makeSubSpace.
Arguments makeSubSpace {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} ss.


(** 零子空间 *)
Section zero_SubSpace.
  Context `{HVectorSpace : VectorSpace}.
  
  Instance zero_SubSpaceStruct : SubSpaceStruct (fun v => v = Vzero).
  Proof.
    constructor; auto.
    - intros. rewrite u.prf, v.prf. apply vs_vadd_0_l.
    - intros. rewrite v.prf. apply vs_vcmul_0_r.
  Qed.

  #[export] Instance zero_SubSpace : VectorSpace Hadd Hzero Hopp Hcmul :=
    makeSubSpace zero_SubSpaceStruct.
End zero_SubSpace.

(** 线性空间本身也是其子空间 *)
Section self_SubSpace.
  Context `{HVectorSpace : VectorSpace}.
  
  Instance self_SubSpaceStruct : SubSpaceStruct (fun v => True).
  Proof. constructor; auto. Qed.

  #[export] Instance self_SubSpace : VectorSpace Hadd Hzero Hopp Hcmul :=
    makeSubSpace self_SubSpaceStruct.
  
End self_SubSpace.

