(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Gauss elimination of matrix
  author    : ZhengPu Shi
  date      : 2023.12

  remark    :
  1. First stage, we use a simple case of `n × n` matrix
  2. Second stage, we should consider the case of `m × n` matrix
 *)

Require Import NatExt.
Require Import Hierarchy.
Require Import MyExtrOCamlR.
Require Export Matrix MatrixGauss MatrixInvBase.
Require QcExt RExt.

Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv.


(* ############################################################################ *)
(** * Inverse matrix based on Gauss elimination (Typeclass version) *)
Section minv.
  Context `{HField : Field} {AeqDec : Dec (@eq A)}.
  Add Field field_thy_inst : (make_field_theory HField).
  Open Scope A_scope.
  Open Scope mat_scope.

  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation "a - b" := ((a + -b)%A) : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation "a / b" := ((a * /b)%A) : A_scope.
  
  Notation smat n := (smat A n).
  Notation mat1 := (@mat1 _ Azero Aone).
  Notation mcmul := (@mcmul _ Amul).
  Infix "\.*" := mcmul : mat_scope.
  Notation mmul := (@mmul _ Aadd Azero Amul).
  Infix "*" := mmul : mat_scope.
  Infix "*" := mmul : mat_scope.
  Notation mmulv := (@mmulv _ Aadd 0 Amul).
  Infix "*v" := mmulv : mat_scope.
  Notation minvtble := (@minvtble _ Aadd 0 Amul 1).
  Notation msingular := (@msingular _ Aadd 0 Amul 1).

  Notation toREF := (@toREF _ Aadd 0 Aopp Amul Ainv _).
  Notation toRREF := (@toRREF _ Aadd 0 Aopp Amul _).
  Notation rowOps2mat := (@rowOps2mat _ Aadd 0 Amul 1).
  Notation rowOps2matInv := (@rowOps2matInv _ Aadd 0 Aopp Amul 1 Ainv).
  
  (* ======================================================================= *)
  (** ** Check matrix invertibility *)

  (** Check the invertibility of matrix `M` *)
  Definition minvtbleb {n} : smat n -> bool :=
    match n with
    | O => fun _ => true   (* zero-dims matrix is considered invertible *)
    | S n' =>
        fun M =>
          match toREF M (S n') with
          | None => false
          | Some (l1, M1) => true
          end
    end.

  (* M * N = mat1 -> (exists (l1, M1), toREF M (S n) = Some (l1,M1) *)
  Lemma mmul_eq1_imply_toREF_Some_l : forall {n} (M N : smat (S n)),
      M * N = mat1 -> (exists '(l1, M1), toREF M (S n) = Some (l1, M1)).
  Proof.
  Admitted.

  (* M * N = mat1 -> (exists (l1, N1), toREF N (S n) = Some (l1,N1) *)
  Lemma mmul_eq1_imply_toREF_Some_r : forall {n} (M N : smat (S n)),
      M * N = mat1 -> (exists '(l1, N1), toREF N (S n) = Some (l1, N1)).
  Proof.
  Admitted.
  
  (** minvtble M <-> minvtbleb M = true *)
  Lemma minvtble_iff_minvtbleb_true : forall {n} (M : smat n),
      minvtble M <-> minvtbleb M = true.
  Proof.
    intros. split; intros.
    - hnf in H. destruct H as [M' [Hl Hr]]. destruct n; auto.
      apply (mmul_eq1_imply_toREF_Some_r) in Hl. destruct Hl as [[l1 M1]].
      unfold minvtbleb. rewrite H. auto.
    - apply minvtble_iff_minvtbleL. hnf.
      unfold minvtbleb in H. destruct n.
      + exists M. apply v0eq.
      + destruct toREF as [[l1 M1]|] eqn:T1; try easy.
        destruct (toRREF M1 (S n)) as [l2 M2] eqn:T2.
        apply toRREF_eq in T2 as H3.
        apply toREF_eq in T1 as H4.
        apply toRREF_mat1 in T2 as H5.
        * subst. rewrite <- mmul_assoc in H5.
          exists (rowOps2mat l2 * rowOps2mat l1); auto.
        * apply toREF_mUnitUpperTrig in T1. auto.
  Qed.
  
  (** msingular M <-> minvtbleb M = false *)
  Lemma msingular_iff_minvtbleb_false : forall {n} (M : smat n),
      msingular M <-> minvtbleb M = false.
  Proof.
    intros. unfold msingular. rewrite minvtble_iff_minvtbleb_true.
    rewrite not_true_iff_false. tauto.
  Qed.


  (* ******************************************************************* *)
  (** ** Inverse matrix (option version) *)
  
  (** Inverse matrix (option version) *)
  Definition minvo {n} : smat n -> option (smat n) :=
    match n with
    | O => fun M => Some mat1 (* zero-dims matrix has a dummy inverse, any value is OK *)
    | S n' =>
        fun (M : smat (S n')) =>
          match toREF M (S n') with
          | None => None
          | Some (l1, M1) =>
              let (l2, M2) := toRREF M1 (S n') in
              Some (rowOps2mat (l2 ++ l1))
          end
    end.
  
  (** `minvo` return `Some`, iff M is invertible *)
  Lemma minvo_Some_iff_minvtble : forall {n} (M : smat n),
      (exists M', minvo M = Some M') <-> minvtble M.
  Proof.
    intros. rewrite minvtble_iff_minvtbleb_true.
    unfold minvo, minvtbleb. destruct n.
    - split; intros; auto. exists M. f_equal. apply v0eq.
    - split; intros.
      + destruct H as [M' H]. destruct toREF as [[l1 M1]|]; try easy.
      + destruct toREF as [[l1 M1]|] eqn:T1; try easy.
        destruct toRREF as [l2 M2] eqn:T2. eexists; auto.
  Qed.

  (** `minvo` return `None`, iff M is singular *)
  Lemma minvo_None_iff_msingular : forall {n} (M : smat n),
      minvo M = None <-> msingular M.
  Proof.
    intros. unfold msingular. rewrite <- minvo_Some_iff_minvtble.
    unfold minvo. destruct n.
    - split; intros; try easy. destruct H. exists mat1; auto.
    - split; intros; try easy.
      + intro. destruct H0 as [M' H0]. rewrite H in H0. easy.
      + destruct toREF as [[l1 M1]|] eqn:T1; try easy.
        destruct toRREF as [l2 M2] eqn:T2. destruct H. eexists; auto.
  Qed.

  (** If `minvo M` return `Some M'`, then `M' * M = mat1` *)
  Lemma minvo_Some_imply_eq1_l : forall {n} (M M' : smat n),
      minvo M = Some M' -> M' * M = mat1.
  Proof.
    intros. unfold minvo in H. destruct n.
    - apply v0eq.
    - destruct toREF as [[l1 M1]|] eqn:T1; try easy.
      destruct toRREF as [l2 M2] eqn:T2. inv H.
      copy T1. copy T2.
      apply toREF_eq in T1.
      apply toRREF_eq in T2.
      rewrite rowOps2mat_app. rewrite mmul_assoc. rewrite T1,T2.
      apply toRREF_mat1 in HC0; auto.
      apply toREF_mUnitUpperTrig in HC; auto.
  Qed.

  (** If `minvo M` return `Some M'`, then `M * M' = mat1` *)
  Lemma minvo_Some_imply_eq1_r : forall {n} (M M' : smat n),
      minvo M = Some M' -> M * M' = mat1.
  Proof.
    intros.
    (* Quickly finished the proof (but, we need Adjoint Matrix method) *)
    (* apply minvo_Some_imply_eq1_l in H as H'. *)
    (* apply mmul_eq1_comm in H'. auto. *)

    (* Let's proof it directly *)
    unfold minvo in H. destruct n.
    - apply v0eq.
    - destruct toREF as [[l1 M1]|] eqn:T1; try easy.
      destruct toRREF as [l2 M2] eqn:T2.
      apply toREF_eq_inv in T1 as T1'.
      apply toRREF_eq_inv in T2 as T2'.
      apply toRREF_mat1 in T2 as T2''; auto.
      2:{ apply toREF_mUnitUpperTrig in T1; auto. }
      rewrite <- T1'. rewrite <- T2'. rewrite T2''.
      inversion H. rewrite mmul_1_r.
      rewrite <- rowOps2matInv_app.
      rewrite mmul_rowOps2matInv_rowOps2mat_eq1. auto.
      apply Forall_app. split.
      apply toRREF_rowOpValid in T2; auto.
      apply toREF_rowOpValid in T1; auto.
  Qed.

  (* ******************************************************************* *)
  (** ** Inverse matrix (default value version) *)
  
  (** Inverse matrix (with identity matrix as default value) *)
  Definition minv {n} : smat n -> smat n :=
    match n with
    | O => fun _ => mat1
    | S n' =>
        fun (M : smat (S n')) =>
          match toREF M n with
          | None => mat1
          | Some (l1, M1) =>
              let (l2, M2) := toRREF M1 n in
              rowOps2mat (l2 ++ l1)
          end
    end.
  Notation "M \-1" := (minv M) : mat_scope.

  (** If `minvo M` return `Some N`, then `M\-1` equal to `N` *)
  Lemma minvo_Some_imply_minv : forall {n} (M N : smat n), minvo M = Some N -> M\-1 = N.
  Proof.
    intros. unfold minvo, minv in *. destruct n. inv H. auto.
    destruct toREF as [[l1 M1]|] eqn:T1; try easy.
    destruct toRREF as [l2] eqn:T2.
    inv H. auto.
  Qed.

  (** If `minvo M` return `None`, then `M\-1` equal to `mat1` *)
  Lemma minvo_None_imply_minv : forall {n} (M  : smat n), minvo M = None -> M\-1 = mat1.
  Proof.
    intros. unfold minvo, minv in *. destruct n. easy.
    destruct toREF as [[l1 M1]|] eqn:T1; try easy.
    destruct toRREF as [l2] eqn:T2. easy.
  Qed.
  
  (** M\-1 * M = mat1 *)
  Lemma mmul_minv_l : forall {n} (M : smat n), minvtble M -> M\-1 * M = mat1.
  Proof.
    intros. apply minvtble_iff_minvtbleb_true in H as H1.
    unfold minvtbleb, minv in *. destruct n. apply v0eq.
    destruct toREF as [[l1 M1]|] eqn:T1; try easy.
    destruct toRREF as [l2 M2] eqn:T2.
    rewrite rowOps2mat_app. rewrite mmul_assoc.
    apply toREF_eq in T1 as T1'. rewrite T1'.
    apply toRREF_eq in T2 as T2'. rewrite T2'.
    apply toRREF_mat1 in T2; auto.
    apply toREF_mUnitUpperTrig in T1; auto.
  Qed.
  
End minv.


(* ############################################################################ *)
(** * Inverse matrix based on Gauss elimination (module version) *)
Module MinvCoreGE (E : FieldElementType) <: MinvCore E.
  Import E.
  Open Scope A_scope.
  Open Scope mat_scope.
  
  Add Field field_inst : (make_field_theory Field).

  Local Notation "0" := Azero : A_scope.
  Local Notation "1" := Aone : A_scope.
  Local Infix "+" := Aadd : A_scope.
  Local Notation "- a" := (Aopp a) : A_scope.
  Local Notation "a - b" := ((a + -b)%A) : A_scope.
  Local Infix "*" := Amul : A_scope.
  Local Notation "/ a" := (Ainv a) : A_scope.
  Local Notation "a / b" := ((a * /b)%A) : A_scope.

  Local Notation smat n := (smat A n).
  Local Notation mat1 := (@mat1 _ Azero Aone).
  Local Notation mcmul := (@mcmul _ Amul).
  Local Infix "\.*" := mcmul : mat_scope.
  Local Notation mmul := (@mmul _ Aadd Azero Amul).
  Local Infix "*" := mmul : mat_scope.
  Local Infix "*" := mmul : mat_scope.
  Local Notation mmulv := (@mmulv _ Aadd 0 Amul).
  Local Infix "*v" := mmulv : mat_scope.
  
  Notation minvtble := (@minvtble _ Aadd 0 Amul 1).
  Notation msingular := (@msingular _ Aadd 0 Amul 1).

  Notation toREF := (@toREF _ Aadd 0 Aopp Amul Ainv _).
  Notation toRREF := (@toRREF _ Aadd 0 Aopp Amul _).
  Notation rowOps2mat := (@rowOps2mat _ Aadd 0 Amul 1).
  Notation rowOps2matInv := (@rowOps2matInv _ Aadd 0 Aopp Amul 1 Ainv).
  
  (* ======================================================================= *)
  (** ** Check matrix invertibility *)

  (** Check the invertibility of matrix `M` *)
  Definition minvtbleb {n} (M : smat n) : bool :=
    @minvtbleb _ Aadd 0 Aopp Amul Ainv _ _ M.

  (* M * N = mat1 -> (exists (l1, M1), toREF M (S n) = Some (l1,M1) *)
  Lemma mmul_eq1_imply_toREF_Some_l : forall {n} (M N : smat (S n)),
      M * N = mat1 -> (exists '(l1, M1), toREF M (S n) = Some (l1, M1)).
  Proof. intros. apply mmul_eq1_imply_toREF_Some_l in H; auto. Qed.

  (* M * N = mat1 -> (exists (l1, N1), toREF N (S n) = Some (l1,N1) *)
  Lemma mmul_eq1_imply_toREF_Some_r : forall {n} (M N : smat (S n)),
      M * N = mat1 -> (exists '(l1, N1), toREF N (S n) = Some (l1, N1)).
  Proof. intros. apply mmul_eq1_imply_toREF_Some_r in H; auto. Qed.
  
  (** minvtble M <-> minvtbleb M = true *)
  Lemma minvtble_iff_minvtbleb_true : forall {n} (M : smat n),
      minvtble M <-> minvtbleb M = true.
  Proof. intros. apply minvtble_iff_minvtbleb_true. Qed.
  
  (** msingular M <-> minvtbleb M = false *)
  Lemma msingular_iff_minvtbleb_false : forall {n} (M : smat n),
      msingular M <-> minvtbleb M = false.
  Proof. intros. apply msingular_iff_minvtbleb_false. Qed.


  (* ******************************************************************* *)
  (** ** Inverse matrix (option version) *)
  
  (** Inverse matrix (option version) *)
  Definition minvo {n} (M : smat n) : option (smat n) :=
    @minvo _ Aadd 0 Aopp Amul 1 Ainv _ _ M.

  (** `minvo` return `Some`, iff M is invertible *)
  Lemma minvo_Some_iff_minvtble : forall {n} (M : smat n),
      (exists M', minvo M = Some M') <-> minvtble M.
  Proof. intros. apply minvo_Some_iff_minvtble. Qed.

  (** `minvo` return `None`, iff M is singular *)
  Lemma minvo_None_iff_msingular : forall {n} (M : smat n),
      minvo M = None <-> msingular M.
  Proof. intros. apply minvo_None_iff_msingular. Qed.

  (** If `minvo M` return `Some M'`, then `M' * M = mat1` *)
  Lemma minvo_Some_imply_eq1_l : forall {n} (M M' : smat n),
      minvo M = Some M' -> M' * M = mat1.
  Proof. intros. apply minvo_Some_imply_eq1_l; auto. Qed.

  (** If `minvo M` return `Some M'`, then `M * M' = mat1` *)
  Lemma minvo_Some_imply_eq1_r : forall {n} (M M' : smat n),
      minvo M = Some M' -> M * M' = mat1.
  Proof. intros. apply minvo_Some_imply_eq1_r; auto. Qed.

  (* ******************************************************************* *)
  (** ** Inverse matrix (default value version) *)
  
  (** Inverse matrix (with identity matrix as default value) *)
  Definition minv {n} (M : smat n) : smat n :=
    @minv _ Aadd 0 Aopp Amul 1 Ainv _ _ M.
  Notation "M \-1" := (minv M) : mat_scope.

  (** If `minvo M` return `Some N`, then `M\-1` equal to `N` *)
  Lemma minvo_Some_imply_minv : forall {n} (M N : smat n), minvo M = Some N -> M\-1 = N.
  Proof. intros. apply minvo_Some_imply_minv; auto. Qed.

  (** If `minvo M` return `None`, then `M\-1` equal to `mat1` *)
  Lemma minvo_None_imply_minv : forall {n} (M  : smat n), minvo M = None -> M\-1 = mat1.
  Proof. intros. apply minvo_None_imply_minv; auto. Qed.
  
  (** M\-1 * M = mat1 *)
  Lemma mmul_minv_l : forall {n} (M : smat n), minvtble M -> M\-1 * M = mat1.
  Proof. intros. apply mmul_minv_l; auto. Qed.
  
End MinvCoreGE.


(* ############################################################################ *)
(** * Matrix inversion by Gauss Elimination *)
Module MinvGE (E : FieldElementType).
  Module MinvCore_inst := MinvCoreGE E.
  Module Minv_inst := Minv E MinvCore_inst.
  Export Minv_inst.

End MinvGE.
