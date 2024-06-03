(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Inverse matrix by Adjoint Matrix
  author    : ZhengPu Shi
  date      : 2023.06
  
  remark    :
  * we use `AM` to denote `Adjoint Matrix method`
  * there are two equivalent methods to get determinant, `mdet` and `mdetEx':
    `mdet` is full expansion which have better consistency, and will be used 
    in proposition for proof; 
    `mdetEx` is one-row expansion which have better performance, and will be
    used in definition for computation.
 *)

Require Import Extraction.
Require Import NatExt.
Require Export Matrix MatrixDet MatrixInvBase.
Require ZArith Reals.

Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv.


(* ############################################################################ *)
(** * Matrix Inversion by Adjoint Matrix (Typeclass version) *)

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
  Infix "c*" := mcmul : mat_scope.
  Notation mmul := (@mmul _ Aadd Azero Amul).
  Infix "*" := mmul : mat_scope.
  Notation mmulv := (@mmulv _ Aadd 0 Amul).
  Infix "*v" := mmulv : mat_scope.

  Notation minvtble := (@minvtble _ Aadd 0 Amul 1).
  Notation msingular := (@msingular _ Aadd 0 Amul 1).
  Notation mdet := (@mdet _ Aadd 0 Aopp Amul 1).
  Notation mdetEx := (@mdetEx _ Aadd 0 Aopp Amul 1).
  Notation madj := (@madj _ Aadd 0 Aopp Amul 1).
  Notation "M \A" := (madj M) : mat_scope.
  Notation mcofactorEx := (@mcofactorEx _ Aadd 0 Aopp Amul 1).
  Notation mdet1 := (@mdet1 A).
  Notation mdet2 := (@mdet2 _ Aadd Aopp Amul).
  Notation mdet3 := (@mdet3 _ Aadd Aopp Amul).
  Notation mdet4 := (@mdet4 _ Aadd Aopp Amul).
  Notation cramerRule := (@cramerRule _ Aadd 0 Aopp Amul 1 Ainv).

  (* ======================================================================= *)
  (** ** Check matrix invertibility *)

  (** Check the invertibility of matrix `M` *)
  Definition minvtbleb {n} (M : smat n) : bool :=
    if Aeqdec (mdetEx M) 0 then false else true.

  (** minvtble M <-> minvtbleb M = true *)
  Lemma minvtble_iff_minvtbleb_true : forall {n} (M : smat n),
      minvtble M <-> minvtbleb M = true.
  Proof.
    intros. rewrite minvtble_iff_mdet_neq0.
    unfold minvtbleb. rewrite mdetEx_eq_mdet.
    destruct Aeqdec; easy.
  Qed.
  
  (** msingular M <-> minvtbleb M = false *)
  Lemma msingular_iff_minvtbleb_false : forall {n} (M : smat n),
      msingular M <-> minvtbleb M = false.
  Proof.
    intros. unfold msingular. rewrite minvtble_iff_minvtbleb_true.
    rewrite not_true_iff_false. tauto.
  Qed.


  (* ======================================================================= *)
  (** ** Inverse matrix (option version) *)

  (** Inverse matrix (option version) *)
  Definition minvo {n} (M : smat n) : option (smat n) :=
    if minvtbleb M
    then Some ((/ mdetEx M) c* (madj M))
    else None.

  (** `minvo` return `Some`, iff M is invertible *)
  Lemma minvo_Some_iff_minvtble : forall {n} (M : smat n),
      (exists M', minvo M = Some M') <-> minvtble M.
  Proof.
    intros. rewrite minvtble_iff_minvtbleb_true. split; intros.
    - destruct H as [M' H]. unfold minvo in H.
      destruct minvtbleb; try easy.
    - exists ((/ mdetEx M) c* (madj M)). unfold minvo.
      destruct minvtbleb; try easy.
  Qed.

  (** `minvo` return `None`, iff M is singular *)
  Lemma minvo_None_iff_msingular : forall {n} (M : smat n),
      minvo M = None <-> msingular M.
  Proof.
    intros. rewrite msingular_iff_minvtbleb_false. split; intros.
    - unfold minvo in H. destruct minvtbleb; try easy.
    - unfold minvo. destruct minvtbleb; try easy.
  Qed.

  (** If `minvo M` return `Some M'`, then `M' * M = mat1` *)
  Lemma minvo_Some_imply_eq1_l : forall {n} (M M' : smat n),
      minvo M = Some M' -> M' * M = mat1.
  Proof.
    intros. unfold minvo in H. destruct minvtbleb eqn:E; try easy. inv H.
    rewrite mdetEx_eq_mdet. apply mmul_det_cmul_adj_l.
    apply minvtble_iff_minvtbleb_true in E.
    apply minvtble_iff_mdet_neq0; auto.
  Qed.

  (** If `minvo M` return `Some M'`, then `M * M' = mat1` *)
  Lemma minvo_Some_imply_eq1_r : forall {n} (M M' : smat n),
      minvo M = Some M' -> M * M' = mat1.
  Proof.
    intros. apply minvo_Some_imply_eq1_l in H.
    apply mmul_eq1_comm; auto.
  Qed.
  
  
  (* ======================================================================= *)
  (** ** Inverse matrix (default value version) *)
  
  (** Inverse matrix (with identity matrix as default value) *)
  Definition minv {n} (M : smat n) :=
    if minvtbleb M then (/ mdetEx M) c* (madj M) else mat1.
  Notation "M \-1" := (minv M) : mat_scope.

  (** If `minvo M` return `Some N`, then `M\-1` equal to `N` *)
  Lemma minvo_Some_imply_minv : forall {n} (M N : smat n), minvo M = Some N -> M\-1 = N.
  Proof.
    intros. unfold minvo, minv in *.
    destruct minvtbleb eqn:E; try easy. inv H. auto.
  Qed.

  (** If `minvo M` return `None`, then `M\-1` equal to `mat1` *)
  Lemma minvo_None_imply_minv : forall {n} (M  : smat n), minvo M = None -> M\-1 = mat1.
  Proof.
    intros. unfold minvo, minv in *.
    destruct minvtbleb eqn:E; try easy.
  Qed.
  
  (** M\-1 * M = mat1 *)
  Lemma mmul_minv_l : forall {n} (M : smat n), minvtble M -> M\-1 * M = mat1.
  Proof.
    intros. unfold minv. rewrite mdetEx_eq_mdet.
    apply minvtble_iff_minvtbleb_true in H as H1. rewrite H1.
    apply mmul_det_cmul_adj_l. apply minvtble_iff_mdet_neq0 in H. auto.
  Qed.


  (* ======================================================================= *)
  (** ** Inverse matrix (No-check version) *)

  (** Inverse matrix (won't check the inversibility) *)
  Definition minvNoCheck {n} (M : smat n) := (/ mdetEx M) c* (madj M).

  (** If `M` is invertible, then [minvNoCheckAM] is equivalent to [minvAM] *)
  Lemma minvNoCheck_spec : forall {n} (M : smat n), minvtble M -> minvNoCheck M = M\-1.
  Proof.
    intros. unfold minvNoCheck, minv in *.
    apply minvtble_iff_minvtbleb_true in H. rewrite H. auto.
  Qed.

  
  (* ======================================================================= *)
  (** ** Get one element of inverse matrix *)

  (* Note: the purpose of this function is to support quickly evaluation *)

  (** Get (i,j) element of inverse matrix of matrix `M` *)
  Definition minvElement {n} (M : smat (S n)) (i j : 'I_(S n)) : A :=
    ((/ (mdetEx M)) * mcofactorEx M j i)%A.

  (** If `M` is invertible, minvElement M i j = (M\-1).[i].[j] *)
  Lemma minvElement_spec : forall {n} (M : smat (S n)) (i j : 'I_(S n)),
      minvtble M -> minvElement M i j = (M\-1).[i].[j].
  Proof.
    intros. unfold minvElement, minv in *.
    apply minvtble_iff_minvtbleb_true in H. rewrite H.
    rewrite mnth_mcmul. unfold madj. auto.
  Qed.

  (* ======================================================================= *)
  (** ** Direct formulas of inverse matrix *)

  (* Get the formulas by computation *)
  Section formulas_by_computtation.
    Variable a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44 : A.
    Let M1 : smat 1 := l2m 0 [[a11]].
    Let M2 : smat 2 := l2m 0 [[a11;a12];[a21;a22]].
    Let M3 : smat 3 := l2m 0 [[a11;a12;a13];[a21;a22;a23];[a31;a32;a33]].
    Let M4 : smat 4 := l2m 0 [[a11;a12;a13;a14];[a21;a22;a23;a24];
                              [a31;a32;a33;a34];[a41;a42;a43;a44]].

    (* Compute m2l (minvNoCheck M1). *)
    (* Compute m2l (minvNoCheck M2). *)
    (* Compute m2l (minvNoCheck M3). *)
    (* Compute m2l (minvNoCheck M4). *)
    (* Althouhg these formulas are correct, but the expression is too long.
       To get simple formulas, there are two ideas:
       1. use a simplifier to proces the result, liek RAST.
       2. only provide commonly used formulas on specific dimensions. *)
  End formulas_by_computtation.

  (* a <> 0 |- b <> 0 ==> b = 0 |- a = 0 *)
  Ltac solve_neq0_neq0 :=
    let H1 := fresh "H1" in
    match goal with
    | H: ?e1 = 0 -> False |- ?e2 <> Azero => intros H1; destruct H
    end.

  (* a = 0 |- b = 0 ==> a = b, and try to solve it *)
  Ltac solve_eq0_eq0 :=
    match goal with
    | H: ?a = Azero |- ?b = Azero => symmetry; rewrite <- H at 1; try ring
    end.
    
  Definition minv1 (M : smat 1) : smat 1 := l2m 0 [[1/M.11]].

  (** minvtble M -> minv1 M = inv M *)
  Lemma minv1_eq_minv : forall M, minvtble M -> minv1 M = M\-1.
  Proof.
    intros. apply minvtble_iff_mdet_neq0 in H.
    rewrite <- minvNoCheck_spec; [|apply minvtble_iff_mdet_neq0; auto].
    rewrite <- mdetEx_eq_mdet in H.
    apply m2l_inj; cbv in *; rewrite <- !(nth_m2f 0) in *; list_eq;
      field; solve_neq0_neq0; solve_eq0_eq0.
  Qed.

  Definition minv2 (M : smat 2) : smat 2 :=
    /(mdet2 M) c*
      l2m 0 [[M.22; -M.12]; [-M.21; M.11]].

  (** minvtble M -> minv2 M = inv M *)
  Lemma minv2_eq_minv : forall M, minvtble M -> minv2 M = M\-1.
  Proof.
    intros. apply minvtble_iff_mdet_neq0 in H.
    rewrite <- minvNoCheck_spec; [|apply minvtble_iff_mdet_neq0; auto].
    rewrite <- mdetEx_eq_mdet in H.
    apply m2l_inj; cbv in *; rewrite <- !(nth_m2f 0) in *; list_eq;
      field; solve_neq0_neq0; solve_eq0_eq0.
  Qed.
  
  (* Note, this formula come from matlab, needn't manual work *)
  Definition minv3 (M : smat 3) : smat 3 :=
    /(mdet3 M) c*
      l2m 0 [[(M.22*M.33-M.23*M.32); -(M.12*M.33-M.13*M.32); (M.12*M.23-M.13*M.22)];
             [-(M.21*M.33-M.23*M.31); (M.11*M.33-M.13*M.31); -(M.11*M.23-M.13*M.21)];
             [(M.21*M.32-M.22*M.31); -(M.11*M.32-M.12*M.31); (M.11*M.22-M.12*M.21)]]%A.

  (** minvtble M -> minv3 M = inv M *)
  Lemma minv3_eq_minv : forall M, minvtble M -> minv3 M = M\-1.
    (* TO SPEED UP THE COMPILATION *)
  Admitted.
  (* Proof. *)
  (*   intros. apply minvtble_iff_mdet_neq0 in H. *)
  (*   rewrite <- minvNoCheck_spec; [|apply minvtble_iff_mdet_neq0; auto]. *)
  (*   rewrite <- mdetEx_eq_mdet in H. *)
  (*   apply m2l_inj; cbv in *; rewrite <- !(nth_m2f 0) in *; list_eq; *)
  (*     field; solve_neq0_neq0; solve_eq0_eq0. *)
  (* Qed. *)

  Definition minv4 (M : smat 4) : smat 4 :=
    /(mdet4 M) c*
      l2m 0 [[(M.22*M.33*M.44 - M.22*M.34*M.43 - M.23*M.32*M.44 + M.23*M.34*M.42 +
                 M.24*M.32*M.43 - M.24*M.33*M.42);
              -(M.12*M.33*M.44 - M.12*M.34*M.43 - M.13*M.32*M.44 + M.13*M.34*M.42 +
                  M.14*M.32*M.43 - M.14*M.33*M.42);
              (M.12*M.23*M.44 - M.12*M.24*M.43 - M.13*M.22*M.44 + M.13*M.24*M.42 +
                 M.14*M.22*M.43 - M.14*M.23*M.42);
              -(M.12*M.23*M.34 - M.12*M.24*M.33 - M.13*M.22*M.34 + M.13*M.24*M.32 +
                  M.14*M.22*M.33 - M.14*M.23*M.32)];

             [-(M.21*M.33*M.44 - M.21*M.34*M.43 - M.23*M.31*M.44 + M.23*M.34*M.41 +
                  M.24*M.31*M.43 - M.24*M.33*M.41);
              (M.11*M.33*M.44 - M.11*M.34*M.43 - M.13*M.31*M.44 + M.13*M.34*M.41 +
                 M.14*M.31*M.43 - M.14*M.33*M.41);
              -(M.11*M.23*M.44 - M.11*M.24*M.43 - M.13*M.21*M.44 + M.13*M.24*M.41 +
                  M.14*M.21*M.43 - M.14*M.23*M.41);
              (M.11*M.23*M.34 - M.11*M.24*M.33 - M.13*M.21*M.34 + M.13*M.24*M.31 +
                 M.14*M.21*M.33 - M.14*M.23*M.31)];

             [(M.21*M.32*M.44 - M.21*M.34*M.42 - M.22*M.31*M.44 + M.22*M.34*M.41
               + M.24*M.31*M.42 - M.24*M.32*M.41);
              -(M.11*M.32*M.44 - M.11*M.34*M.42 - M.12*M.31*M.44 + M.12*M.34*M.41 +
                  M.14*M.31*M.42 - M.14*M.32*M.41);
              (M.11*M.22*M.44 - M.11*M.24*M.42 - M.12*M.21*M.44 + M.12*M.24*M.41 +
                 M.14*M.21*M.42 - M.14*M.22*M.41);
              -(M.11*M.22*M.34 - M.11*M.24*M.32 - M.12*M.21*M.34 + M.12*M.24*M.31 +
                  M.14*M.21*M.32 - M.14*M.22*M.31)];
             
             [-(M.21*M.32*M.43 - M.21*M.33*M.42 - M.22*M.31*M.43 + M.22*M.33*M.41 +
                  M.23*M.31*M.42 - M.23*M.32*M.41);
              (M.11*M.32*M.43 - M.11*M.33*M.42 - M.12*M.31*M.43 + M.12*M.33*M.41 +
                 M.13*M.31*M.42 - M.13*M.32*M.41);
              -(M.11*M.22*M.43 - M.11*M.23*M.42 - M.12*M.21*M.43 + M.12*M.23*M.41 +
                  M.13*M.21*M.42 - M.13*M.22*M.41);
              (M.11*M.22*M.33 - M.11*M.23*M.32 - M.12*M.21*M.33 + M.12*M.23*M.31 +
                 M.13*M.21*M.32 - M.13*M.22*M.31)]]%A.
  
  (** minvtble M -> minv4 M = inv M *)
  Lemma minv4_eq_minv : forall M, minvtble M -> minv4 M = M\-1.
    (* TO SPEED UP THE COMPILATION *)
  Admitted.
  (* Proof. *)
  (*   intros. apply minvtble_iff_mdet_neq0 in H. *)
  (*   rewrite <- minvNoCheck_spec; [|apply minvtble_iff_mdet_neq0; auto]. *)
  (*   rewrite <- mdetEx_eq_mdet in H. *)
  (*   apply m2l_inj; cbv in *; rewrite <- !(nth_m2f 0) in *; list_eq; *)
  (*     field; solve_neq0_neq0; solve_eq0_eq0. *)
  (* Qed. *)
  

End minv.


(* ############################################################################ *)
(** * Matrix Inversion by Adjoint Matrix (module version)  *)

Module MinvCoreAM (E : FieldElementType) <: MinvCore E.
  Export E.
  Add Field field_thy_inst : (make_field_theory Field).
  Open Scope A_scope.
  Open Scope mat_scope.

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
  Local Infix "c*" := mcmul : mat_scope.
  Local Notation mmul := (@mmul _ Aadd Azero Amul).
  Local Infix "*" := mmul : mat_scope.
  Local Notation mmulv := (@mmulv _ Aadd 0 Amul).
  Local Infix "*v" := mmulv : mat_scope.
  Local Notation madj := (@madj _ Aadd 0 Aopp Amul 1).
  Local Notation "M \A" := (madj M) : mat_scope.

  Local Notation mdet := (@mdet _ Aadd 0 Aopp Amul 1).
  Local Notation mdetEx := (@mdetEx _ Aadd 0 Aopp Amul 1).
  Local Notation minvtble := (@minvtble _ Aadd 0 Amul 1).
  Local Notation msingular := (@msingular _ Aadd 0 Amul 1).
    
  (* ======================================================================= *)
  (** ** Check matrix invertibility *)

  (** Check the invertibility of matrix `M` *)
  Definition minvtbleb {n} (M : smat n) : bool :=
    @minvtbleb _ Aadd 0 Aopp Amul 1 _ _ M.

  (** minvtble M <-> minvtbleb M = true *)
  Lemma minvtble_iff_minvtbleb_true : forall {n} (M : smat n),
      minvtble M <-> minvtbleb M = true.
  Proof. intros. apply minvtble_iff_minvtbleb_true. Qed.
  
  (** msingular M <-> minvtbleb M = false *)
  Lemma msingular_iff_minvtbleb_false : forall {n} (M : smat n),
      msingular M <-> minvtbleb M = false.
  Proof. intros. apply msingular_iff_minvtbleb_false. Qed.


  (* ======================================================================= *)
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
  
  (* ======================================================================= *)
  (** ** Inverse matrix (default value version) *)
  
  (** Inverse matrix (with identity matrix as default value) *)
  Definition minv {n} (M : smat n) := @minv _ Aadd 0 Aopp Amul 1 Ainv _ _ M.
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


  (* ======================================================================= *)
  (** ** Inverse matrix (No-check version) *)

  (** Inverse matrix (won't check the inversibility) *)
  Definition minvNoCheck {n} (M : smat n) :=
    @minvNoCheck _ Aadd 0 Aopp Amul 1 Ainv _ M.

  (** If `M` is invertible, then [minvNoCheckAM] is equivalent to [minvAM] *)
  Lemma minvNoCheck_spec : forall {n} (M : smat n), minvtble M -> minvNoCheck M = M\-1.
  Proof. intros. apply minvNoCheck_spec; auto. Qed.
  
End MinvCoreAM.


(* ############################################################################ *)
(** * Matrix inversion by Adjoint Matrix *)
Module MinvAM (E : FieldElementType).
  Module MinvCore_inst := MinvCoreAM E.
  Module Minv_inst := Minv E MinvCore_inst.
  Export Minv_inst.

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
  Local Infix "c*" := mcmul : mat_scope.
  Local Notation mmul := (@mmul _ Aadd Azero Amul).
  Local Infix "*" := mmul : mat_scope.
  Local Notation mmulv := (@mmulv _ Aadd 0 Amul).
  Local Infix "*v" := mmulv : mat_scope.
  Local Notation madj := (@madj _ Aadd 0 Aopp Amul 1).
  Local Notation "M \A" := (madj M) : mat_scope.

  Local Notation mdet := (@mdet _ Aadd 0 Aopp Amul 1).
  Local Notation mdetEx := (@mdetEx _ Aadd 0 Aopp Amul 1).
  Local Notation minvtble := (@minvtble _ Aadd 0 Amul 1).
  Local Notation msingular := (@msingular _ Aadd 0 Amul 1).
  
  Notation mcofactorEx := (@mcofactorEx _ Aadd 0 Aopp Amul 1).
  Notation mdet1 := (@mdet1 A).
  Notation mdet2 := (@mdet2 _ Aadd Aopp Amul).
  Notation mdet3 := (@mdet3 _ Aadd Aopp Amul).
  Notation mdet4 := (@mdet4 _ Aadd Aopp Amul).
  Notation cramerRule := (@cramerRule _ Aadd 0 Aopp Amul 1 Ainv).


  (* ======================================================================= *)
  (** ** Solve equation by inverse matrix without check the inversibility *)

  (** Solve the equation with the form of C*x=b, but without check the inversibility. *)
  Definition solveEqNoCheck {n} (C : smat n) (b : vec n) : vec n :=
    (minvNoCheck C) *v b.

  (** minvtble C -> solveEqNoCheck C b = solveEq C b *)
  Theorem solveEqNoCheck_spec : forall {n} (C : smat n) (b : @vec A n),
      minvtble C -> solveEqNoCheck C b = solveEq C b.
  Proof. intros. unfold solveEqNoCheck. rewrite minvNoCheck_spec; auto. Qed.

  (** Solve the equation with the form of C*x=b over list, but without check the 
      inversibility *)
  Definition solveEqListNoCheck (n : nat) (lC : dlist A) (lb : list A) : list A :=
    let C : smat n := l2m 0 lC in
    let b : vec n := l2v 0 lb in
    let x := solveEqNoCheck C b in
    v2l x.

  (** minvtble {lC} -> {solveEqListNoCheck lC lb} = solveEqList {lC} {lb} *)
  Theorem solveEqListNoCheck_spec : forall n (lC : dlist A) (lb : list A),
      let C : smat n := l2m 0 lC in
      minvtble C -> solveEqListNoCheck n lC lb = solveEqList n lC lb.
  Proof. intros. unfold solveEqListNoCheck. rewrite solveEqNoCheck_spec; auto. Qed.

  
  (* ======================================================================= *)
  (** ** Get one element of inverse matrix *)

  (* Note: the purpose of this function is to support quickly evaluation *)

  (** Get (i,j) element of inverse matrix of matrix `M` *)
  Definition minvElement {n} (M : smat (S n)) (i j : 'I_(S n)) : A :=
    @minvElement _ Aadd 0 Aopp Amul 1 Ainv _ M i j.

  (** If `M` is invertible, minvElement M i j = (M\-1).[i].[j] *)
  Lemma minvElement_spec : forall {n} (M : smat (S n)) (i j : 'I_(S n)),
      minvtble M -> minvElement M i j = (M\-1).[i].[j].
  Proof. intros. apply minvElement_spec; auto. Qed.

  (* ======================================================================= *)
  (** ** Direct formulas of inverse matrix *)
    
  Definition minv1 (M : smat 1) : smat 1 := @minv1 _ 0 Amul 1 Ainv M.

  (** minvtble M -> minv1 M = inv M *)
  Lemma minv1_eq_minv : forall M, minvtble M -> minv1 M = M\-1.
  Proof. intros. apply minv1_eq_minv; auto. Qed.

  Definition minv2 (M : smat 2) : smat 2 := @minv2 _ Aadd 0 Aopp Amul Ainv M.

  (** minvtble M -> minv2 M = inv M *)
  Lemma minv2_eq_minv : forall M, minvtble M -> minv2 M = M\-1.
  Proof. intros. apply minv2_eq_minv; auto. Qed.
  
  Definition minv3 (M : smat 3) : smat 3 := @minv3 _ Aadd 0 Aopp Amul Ainv M.

  (** minvtble M -> minv3 M = inv M *)
  Lemma minv3_eq_minv : forall M, minvtble M -> minv3 M = M\-1.
  Proof. intros. apply minv3_eq_minv; auto. Qed.

  Definition minv4 (M : smat 4) : smat 4 := @minv4 _ Aadd 0 Aopp Amul Ainv M.
  
  (** minvtble M -> minv4 M = inv M *)
  Lemma minv4_eq_minv : forall M, minvtble M -> minv4 M = M\-1.
  Proof. intros. apply minv4_eq_minv; auto. Qed.
  
End MinvAM.
