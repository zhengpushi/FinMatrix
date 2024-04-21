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
  Infix "\.*" := mcmul : mat_scope.
  Notation mmul := (@mmul _ Aadd Azero Amul).
  Infix "*" := mmul : mat_scope.
  Notation mmulv := (@mmulv _ Aadd 0 Amul).
  Infix "*v" := mmulv : mat_scope.

  Notation minvertible := (@minvertible _ Aadd 0 Amul 1).
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
  Definition minvertibleb {n} (M : smat n) : bool :=
    if Aeqdec (mdetEx M) 0 then false else true.

  (** minvertible M <-> minvertibleb M = true *)
  Lemma minvertible_iff_minvertibleb_true : forall {n} (M : smat n),
      minvertible M <-> minvertibleb M = true.
  Proof.
    intros. rewrite minvertible_iff_mdet_neq0.
    unfold minvertibleb. rewrite mdetEx_eq_mdet.
    destruct Aeqdec; easy.
  Qed.
  
  (** msingular M <-> minvertibleb M = false *)
  Lemma msingular_iff_minvertibleb_false : forall {n} (M : smat n),
      msingular M <-> minvertibleb M = false.
  Proof.
    intros. unfold msingular. rewrite minvertible_iff_minvertibleb_true.
    rewrite not_true_iff_false. tauto.
  Qed.


  (* ======================================================================= *)
  (** ** Inverse matrix (option version) *)

  (** Inverse matrix (option version) *)
  Definition minvo {n} (M : smat n) : option (smat n) :=
    if minvertibleb M
    then Some ((/ mdetEx M) \.* (madj M))
    else None.

  (** `minvo` return `Some`, iff M is invertible *)
  Lemma minvo_Some_iff_minvertible : forall {n} (M : smat n),
      (exists M', minvo M = Some M') <-> minvertible M.
  Proof.
    intros. rewrite minvertible_iff_minvertibleb_true. split; intros.
    - destruct H as [M' H]. unfold minvo in H.
      destruct minvertibleb; try easy.
    - exists ((/ mdetEx M) \.* (madj M)). unfold minvo.
      destruct minvertibleb; try easy.
  Qed.

  (** `minvo` return `None`, iff M is singular *)
  Lemma minvo_None_iff_msingular : forall {n} (M : smat n),
      minvo M = None <-> msingular M.
  Proof.
    intros. rewrite msingular_iff_minvertibleb_false. split; intros.
    - unfold minvo in H. destruct minvertibleb; try easy.
    - unfold minvo. destruct minvertibleb; try easy.
  Qed.

  (** If `minvo M` return `Some M'`, then `M' * M = mat1` *)
  Lemma minvo_Some_imply_eq1_l : forall {n} (M M' : smat n),
      minvo M = Some M' -> M' * M = mat1.
  Proof.
    intros. unfold minvo in H. destruct minvertibleb eqn:E; try easy. inv H.
    rewrite mdetEx_eq_mdet. apply mmul_det_cmul_adj_l.
    apply minvertible_iff_minvertibleb_true in E.
    apply minvertible_iff_mdet_neq0; auto.
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
    if minvertibleb M then (/ mdetEx M) \.* (madj M) else mat1.
  Notation "M \-1" := (minv M) : mat_scope.

  (** If `minvo M` return `Some N`, then `M\-1` equal to `N` *)
  Lemma minvo_Some_imply_minv : forall {n} (M N : smat n), minvo M = Some N -> M\-1 = N.
  Proof.
    intros. unfold minvo, minv in *.
    destruct minvertibleb eqn:E; try easy. inv H. auto.
  Qed.

  (** If `minvo M` return `None`, then `M\-1` equal to `mat1` *)
  Lemma minvo_None_imply_minv : forall {n} (M  : smat n), minvo M = None -> M\-1 = mat1.
  Proof.
    intros. unfold minvo, minv in *.
    destruct minvertibleb eqn:E; try easy.
  Qed.
  
  (** M\-1 * M = mat1 *)
  Lemma mmul_minv_l : forall {n} (M : smat n), minvertible M -> M\-1 * M = mat1.
  Proof.
    intros. unfold minv. rewrite mdetEx_eq_mdet.
    apply minvertible_iff_minvertibleb_true in H as H1. rewrite H1.
    apply mmul_det_cmul_adj_l. apply minvertible_iff_mdet_neq0 in H. auto.
  Qed.


  (* ======================================================================= *)
  (** ** Inverse matrix (No-check version) *)

  (** Inverse matrix (won't check the inversibility) *)
  Definition minvNoCheck {n} (M : smat n) := (/ mdetEx M) \.* (madj M).

  (** If `M` is invertible, then [minvNoCheckAM] is equivalent to [minvAM] *)
  Lemma minvNoCheck_spec : forall {n} (M : smat n), minvertible M -> minvNoCheck M = M\-1.
  Proof.
    intros. unfold minvNoCheck, minv in *.
    apply minvertible_iff_minvertibleb_true in H. rewrite H. auto.
  Qed.

  
  (* ======================================================================= *)
  (** ** Get one element of inverse matrix *)

  (* Note: the purpose of this function is to support quickly evaluation *)

  (** Get (i,j) element of inverse matrix of matrix `M` *)
  Definition minvElement {n} (M : smat (S n)) (i j : fin (S n)) : A :=
    ((/ (mdetEx M)) * mcofactorEx M j i)%A.

  (** If `M` is invertible, minvElement M i j = (M\-1).[i].[j] *)
  Lemma minvElement_spec : forall {n} (M : smat (S n)) (i j : fin (S n)),
      minvertible M -> minvElement M i j = (M\-1).[i].[j].
  Proof.
    intros. unfold minvElement, minv in *.
    apply minvertible_iff_minvertibleb_true in H. rewrite H.
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

  (** minvertible M -> minv1 M = inv M *)
  Lemma minv1_eq_minv : forall M, minvertible M -> minv1 M = M\-1.
  Proof.
    intros. apply minvertible_iff_mdet_neq0 in H.
    rewrite <- minvNoCheck_spec; [|apply minvertible_iff_mdet_neq0; auto].
    rewrite <- mdetEx_eq_mdet in H.
    apply m2l_inj; cbv in *; rewrite <- !(nth_m2f 0) in *; list_eq;
      field; solve_neq0_neq0; solve_eq0_eq0.
  Qed.

  Definition minv2 (M : smat 2) : smat 2 :=
    /(mdet2 M) \.*
      l2m 0 [[M.22; -M.12]; [-M.21; M.11]].

  (** minvertible M -> minv2 M = inv M *)
  Lemma minv2_eq_minv : forall M, minvertible M -> minv2 M = M\-1.
  Proof.
    intros. apply minvertible_iff_mdet_neq0 in H.
    rewrite <- minvNoCheck_spec; [|apply minvertible_iff_mdet_neq0; auto].
    rewrite <- mdetEx_eq_mdet in H.
    apply m2l_inj; cbv in *; rewrite <- !(nth_m2f 0) in *; list_eq;
      field; solve_neq0_neq0; solve_eq0_eq0.
  Qed.
  
  (* Note, this formula come from matlab, needn't manual work *)
  Definition minv3 (M : smat 3) : smat 3 :=
    /(mdet3 M) \.*
      l2m 0 [[(M.22*M.33-M.23*M.32); -(M.12*M.33-M.13*M.32); (M.12*M.23-M.13*M.22)];
             [-(M.21*M.33-M.23*M.31); (M.11*M.33-M.13*M.31); -(M.11*M.23-M.13*M.21)];
             [(M.21*M.32-M.22*M.31); -(M.11*M.32-M.12*M.31); (M.11*M.22-M.12*M.21)]]%A.

  (** minvertible M -> minv3 M = inv M *)
  Lemma minv3_eq_minv : forall M, minvertible M -> minv3 M = M\-1.
    (* TO SPEED UP THE COMPILATION *)
  Admitted.
  (* Proof. *)
  (*   intros. apply minvertible_iff_mdet_neq0 in H. *)
  (*   rewrite <- minvNoCheck_spec; [|apply minvertible_iff_mdet_neq0; auto]. *)
  (*   rewrite <- mdetEx_eq_mdet in H. *)
  (*   apply m2l_inj; cbv in *; rewrite <- !(nth_m2f 0) in *; list_eq; *)
  (*     field; solve_neq0_neq0; solve_eq0_eq0. *)
  (* Qed. *)

  Definition minv4 (M : smat 4) : smat 4 :=
    /(mdet4 M) \.*
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
  
  (** minvertible M -> minv4 M = inv M *)
  Lemma minv4_eq_minv : forall M, minvertible M -> minv4 M = M\-1.
    (* TO SPEED UP THE COMPILATION *)
  Admitted.
  (* Proof. *)
  (*   intros. apply minvertible_iff_mdet_neq0 in H. *)
  (*   rewrite <- minvNoCheck_spec; [|apply minvertible_iff_mdet_neq0; auto]. *)
  (*   rewrite <- mdetEx_eq_mdet in H. *)
  (*   apply m2l_inj; cbv in *; rewrite <- !(nth_m2f 0) in *; list_eq; *)
  (*     field; solve_neq0_neq0; solve_eq0_eq0. *)
  (* Qed. *)
  

End minv.


(* ############################################################################ *)
(** * Matrix Inversion by Adjoint Matrix (module version)  *)

Module MinvAM (E : FieldElementType) <: Minv E.
  Export E.
  Add Field field_thy_inst : (make_field_theory Field).
  Open Scope A_scope.
  Open Scope mat_scope.

  Module Import AMNotations.
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
    Notation mmulv := (@mmulv _ Aadd 0 Amul).
    Infix "*v" := mmulv : mat_scope.

    Notation madj := (@madj _ Aadd 0 Aopp Amul 1).
    Notation "M \A" := (madj M) : mat_scope.
  End AMNotations.
  
  Notation mdet := (@mdet _ Aadd 0 Aopp Amul 1).
  Notation mdetEx := (@mdetEx _ Aadd 0 Aopp Amul 1).
  Notation minvertible := (@minvertible _ Aadd 0 Amul 1).
  Notation msingular := (@msingular _ Aadd 0 Amul 1).
    
  (* ======================================================================= *)
  (** ** Check matrix invertibility *)

  (** Check the invertibility of matrix `M` *)
  Definition minvertibleb {n} (M : smat n) : bool :=
    @minvertibleb _ Aadd 0 Aopp Amul 1 _ _ M.

  (** minvertible M <-> minvertibleb M = true *)
  Lemma minvertible_iff_minvertibleb_true : forall {n} (M : smat n),
      minvertible M <-> minvertibleb M = true.
  Proof. intros. apply minvertible_iff_minvertibleb_true. Qed.
  
  (** msingular M <-> minvertibleb M = false *)
  Lemma msingular_iff_minvertibleb_false : forall {n} (M : smat n),
      msingular M <-> minvertibleb M = false.
  Proof. intros. apply msingular_iff_minvertibleb_false. Qed.


  (* ======================================================================= *)
  (** ** Inverse matrix (option version) *)

  (** Inverse matrix (option version) *)
  Definition minvo {n} (M : smat n) : option (smat n) :=
    @minvo _ Aadd 0 Aopp Amul 1 Ainv _ _ M.

  (** `minvo` return `Some`, iff M is invertible *)
  Lemma minvo_Some_iff_minvertible : forall {n} (M : smat n),
      (exists M', minvo M = Some M') <-> minvertible M.
  Proof. intros. apply minvo_Some_iff_minvertible. Qed.

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
  Lemma mmul_minv_l : forall {n} (M : smat n), minvertible M -> M\-1 * M = mat1.
  Proof. intros. apply mmul_minv_l; auto. Qed.


  (* ======================================================================= *)
  (** ** Inverse matrix (No-check version) *)

  (** Inverse matrix (won't check the inversibility) *)
  Definition minvNoCheck {n} (M : smat n) :=
    @minvNoCheck _ Aadd 0 Aopp Amul 1 Ainv _ M.

  (** If `M` is invertible, then [minvNoCheckAM] is equivalent to [minvAM] *)
  Lemma minvNoCheck_spec : forall {n} (M : smat n), minvertible M -> minvNoCheck M = M\-1.
  Proof. intros. apply minvNoCheck_spec; auto. Qed.
  
End MinvAM.


(* ############################################################################ *)
(** * More theory of matrix inversion by Adjoint Matrix *)
Module MinvMoreAM (E : FieldElementType).
  Module Minv_inst := MinvAM E.
  Module MinvMore_inst := MinvMore E Minv_inst.
  Export Minv_inst.
  Import AMNotations.
  Export MinvMore_inst.

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

  (** minvertible C -> solveEqNoCheck C b = solveEq C b *)
  Theorem solveEqNoCheck_spec : forall {n} (C : smat n) (b : @vec A n),
      minvertible C -> solveEqNoCheck C b = solveEq C b.
  Proof. intros. unfold solveEqNoCheck. rewrite minvNoCheck_spec; auto. Qed.

  (** Solve the equation with the form of C*x=b over list, but without check the 
      inversibility *)
  Definition solveEqListNoCheck (n : nat) (lC : dlist A) (lb : list A) : list A :=
    let C : smat n := l2m 0 lC in
    let b : vec n := l2v 0 lb in
    let x := solveEqNoCheck C b in
    v2l x.

  (** minvertible {lC} -> {solveEqListNoCheck lC lb} = solveEqList {lC} {lb} *)
  Theorem solveEqListNoCheck_spec : forall n (lC : dlist A) (lb : list A),
      let C : smat n := l2m 0 lC in
      minvertible C -> solveEqListNoCheck n lC lb = solveEqList n lC lb.
  Proof. intros. unfold solveEqListNoCheck. rewrite solveEqNoCheck_spec; auto. Qed.

  
  (* ======================================================================= *)
  (** ** Get one element of inverse matrix *)

  (* Note: the purpose of this function is to support quickly evaluation *)

  (** Get (i,j) element of inverse matrix of matrix `M` *)
  Definition minvElement {n} (M : smat (S n)) (i j : fin (S n)) : A :=
    @minvElement _ Aadd 0 Aopp Amul 1 Ainv _ M i j.

  (** If `M` is invertible, minvElement M i j = (M\-1).[i].[j] *)
  Lemma minvElement_spec : forall {n} (M : smat (S n)) (i j : fin (S n)),
      minvertible M -> minvElement M i j = (M\-1).[i].[j].
  Proof. intros. apply minvElement_spec; auto. Qed.

  (* ======================================================================= *)
  (** ** Direct formulas of inverse matrix *)
    
  Definition minv1 (M : smat 1) : smat 1 := @minv1 _ 0 Amul 1 Ainv M.

  (** minvertible M -> minv1 M = inv M *)
  Lemma minv1_eq_minv : forall M, minvertible M -> minv1 M = M\-1.
  Proof. intros. apply minv1_eq_minv; auto. Qed.

  Definition minv2 (M : smat 2) : smat 2 := @minv2 _ Aadd 0 Aopp Amul Ainv M.

  (** minvertible M -> minv2 M = inv M *)
  Lemma minv2_eq_minv : forall M, minvertible M -> minv2 M = M\-1.
  Proof. intros. apply minv2_eq_minv; auto. Qed.
  
  Definition minv3 (M : smat 3) : smat 3 := @minv3 _ Aadd 0 Aopp Amul Ainv M.

  (** minvertible M -> minv3 M = inv M *)
  Lemma minv3_eq_minv : forall M, minvertible M -> minv3 M = M\-1.
  Proof. intros. apply minv3_eq_minv; auto. Qed.

  Definition minv4 (M : smat 4) : smat 4 := @minv4 _ Aadd 0 Aopp Amul Ainv M.
  
  (** minvertible M -> minv4 M = inv M *)
  Lemma minv4_eq_minv : forall M, minvertible M -> minv4 M = M\-1.
  Proof. intros. apply minv4_eq_minv; auto. Qed.
  
End MinvMoreAM.


(* ############################################################################ *)
(** * Test *)

(* ======================================================================= *)
(** ** Test inverse matrix over Qc type *)

Module MinvMoreAM_Qc := MinvMoreAM FieldElementTypeQc.

Section inv_Qc.
  Import MinvMoreAM_Qc.
  
  (** Example 1: inverse matrix of a `3x3` matrix over Qc type *)
  Section ex1.
    (* [1 3 1]     [-1 -1  2]
     [2 1 1] <-> [ 0 -1  1]
     [2 2 1]     [ 2  4 -5] *)

    (* Input a matrix with list. Note that we need `Q2Qc` fuction for `Qc` type *)
    Let d1 := Q2Qc_dlist [[1;3;1];[2;1;1];[2;2;1]]%Q.
    Let d2 := Q2Qc_dlist [[-1;-1;2];[0;-1;1];[2;4;-5]]%Q.

    (* We can get the result immediately *)
    (* Compute minvertiblebList 3 d1. *)
    (* Compute minvList 3 d1. *)
    (* Compute minvList 3 d2. *)
    
    (* Note that the `canon` part is unnecessary for users, we can remove them *)
    (* Compute Qc2Q_dlist (minvList 3 d1). *)

    (* Proof for equality of inverse matrix *)
    (* inverse of [d1] is [d2] *)
    Goal minvList 3 d1 = d2.
    Proof.
      cbv.
      (* Here, two sides are completely equal.
       But this is not always true, when the input data is become complex. *)
      auto.
      
      (* For complex cases, these script are helpful. *)
      (* list_eq; f_equal; apply proof_irrelevance. *)
    Qed.
  End ex1.
  
(* In summary, for inverse matrix over Qc type:
   1. Pros
      - canonical form enable leibniz equality
   2. Cons
      - the input need `Q2Qc` function
      - the output has unnecessary proofs. *)
End inv_Qc.


(* ======================================================================= *)
(** ** Test inverse matrix over Q type *)

(* The idea:
   1. Considering Q or Qc type: Qc is canonical but a bit complex, Q is simple but 
      not canonical.
   2. Meawhile, Q type is not a field structure over `eq` relation, thus the 
      MinvAM module cannot be usd.
   3. We can mixed use two types, the user-level use Q type, and the inner-level
      use Qc type. *)
Section inv_Q.

  Import MinvMoreAM_Qc.
  Import AMNotations.
  Open Scope Q_scope.

  (** Check matrix invertibility with rational number lists *)
  Definition minvertiblebListQ (n : nat) (d : dlist Q) : bool :=
    minvertiblebList n (Q2Qc_dlist d).

  (** Inverse matrix with rational number lists *)
  Definition minvListQ (n : nat) (dl : dlist Q) : dlist Q :=
    Qc2Q_dlist (minvList n (Q2Qc_dlist dl)).

  (** Example 2: inverse matrix of a `3x3` matrix over Q type *)
  Section ex2.
  
    (* [1 3 1]     [-1 -1  2]
       [2 1 1] <-> [ 0 -1  1]
       [2 2 1]     [ 2  4 -5] *)
    Let d1 := [[1;3;1];[2;1;1];[2;2;1]].
    Let d2 := [[-1;-1;2];[0;-1;1];[2;4;-5]].
    
    (* Now, we can get a friendly experience for typing and printing *)
    (* Compute minvertiblebListQ 3 d1. *)
    (* Compute minvListQ 3 d1. *)
    (* Compute minvListQ 3 d2. *)

    (* Meanwhile, the equality of the result with Q type also satisfy canonical form,
       that means we can use Leibniz equal instad of setoid equal `Qeq` *)
    Goal minvListQ 3 d1 = d2.
    Proof. cbv. auto. Qed.

    (* But, note that the input data should be typing directly.
       For example, "1" is equivalent to "2/2" under `Qeq` relation,
       But, "1" is not equal to "2/2" under `eq` relation. *)
    Goal 1 == Qmake 2 2.
    Proof. cbv. auto. Qed.
    
    Goal 1 <> Qmake 2 2.
    Proof. cbv. intros. easy. Qed.

    (* Thus, if we give an equivalent matrix d2' respect to d2, such as: *)
    Let d2' : dlist Q := [[-1;-1;2];[0;-1;Qmake 2 2];[2;4;-5]].
    (* Here, the (2,3) element in d2' is different with d2, and the others are same.
       d2(2,3) = 1
       d2'(2,3) = Qmake 2 2 
     *)

    (* Now, this previous proof is False *)
    Goal minvListQ 3 d1 <> d2'.
    Proof. cbv. intro. inv H. Qed.

    (* But we can verify that they are setoid equal *)
    Infix "==" := (dlistSetoidEq Qeq).
    Goal minvListQ 3 d1 == d2.
    Proof. Local Opaque Qeq. cbv. repeat constructor. Qed.
  End ex2.
  
  (* Example 3: inverse matrix of a bigger matrix *)
  Section ex3.
    (* A manually given random `8x8` matrix *)
    Let d1 : dlist Q :=
      [[1;2;3;4;5;6;7;8];
       [2;4;5;6;7;8;9;1];
       [3;5;7;6;8;4;2;1];
       [4;5;7;6;9;8;3;2];
       [5;4;3;7;9;6;8;1];
       [6;5;3;4;7;8;9;2];
       [7;8;6;5;9;2;1;3];
       [8;9;6;3;4;5;2;1]].

    (* Time Compute minvListQ 6 d1. (* 0.13s *) *)
    (* Time Compute minvListQ 7 d1. (* 1.0s *) *)
    (* Time Compute minvListQ 8 d1. (* 11s *) *)
    
    (* Note that many elements are in the fraction format of rational numbers.
       This is reasonable, as fractions typically do not possess a finite decimal 
       representation. *)
    
    (* How to verify the inverse matrix in MATLAB ?
     (1) change the format of rational numbers between fractions and floating
         point numbers.
     >> format rat
     >> format short

     (2) inverse matrix of a 6x6 matrix
     >> M = [1 2 3 4 5 6; ...
             2 4 5 6 7 8; ...
             3 5 7 6 8 4; ...
             4 5 7 6 9 8; ...
             5 4 3 7 9 6; ...
             6 5 3 4 7 8]
     >> M1 = inv(M)
     Note that, the result is equal.

     (3) inverse matrix of a 7x7 matrix
     >> M = [1 2 3 4 5 6 7; ...
             2 4 5 6 7 8 9; ...
             3 5 7 6 8 4 2; ...
             4 5 7 6 9 8 3; ...
             5 4 3 7 9 6 8; ...
             6 5 3 4 7 8 9; ...
             7 8 6 5 9 2 1]
     >> M1 = inv(M) 
     Note that, the result is equal.

     (3) inverse matrix of a 8x8 matrix
     >> M = [1 2 3 4 5 6 7 8; ...
             2 4 5 6 7 8 9 1; ...
             3 5 7 6 8 4 2 1; ...
             4 5 7 6 9 8 3 2; ...
             5 4 3 7 9 6 8 1; ...
             6 5 3 4 7 8 9 2; ...
             7 8 6 5 9 2 1 3; ...
             8 9 6 3 4 5 2 1]
     >> M1 = inv(M) 
     Note that, the result is a bit different with in Coq.
     For example:
         in COQ,     M1(1,3)=41846/50943 = 0.8214278704
         in MATLAB,  M1(1,3)=23/28       = 0.8214285714
     *)

    (* We can get the (1,3) element quickly, instead of get all elements *)
    Open Scope Qc_scope.
    Let M : smat 8 := l2m 0 (Q2Qc_dlist d1).

    (* method 1 *)
    Let M1 := @minv 8 (l2m 0 (Q2Qc_dlist d1)).
    (* Time Compute M1.1.3.              (* 2.21 s *) *)
    (* Time Compute (minvElement M).1.3. (* 1.16 s  *) *)

    (* Thes two rational numbers are not equal even over Qeq  *)
    Goal ~(Qmake 41846 50943 == Qmake 23 28).
    Proof.
      intro. cbv in H.          (* 1171688%Z = 1171689%Z *)
      easy.
    Qed.
    
    (* The possible reason is that MATLAB performs calculations using floating-point 
       numbers, and converting the inaccurate results into fractions cannot compensate
       for the difference.
       On the contrary, Coq uses completely precise results.
       While the exact benefits are unclear, this precision could be beneficial. *)
  End ex3.

  (* Example 4 : inverse matrix over bigger matrix with decimal numbers *)
  Section ex4.
    (* In MATLAB, use these commands for comparison experiment:
     >> format short
     >> M = rand(8,8)
     Or, manually use these numbers:
     >> M = [0.8001  0.5797  0.0760  0.9448  0.3897  0.0598  0.7317  0.1835; ...
             0.4314  0.5499  0.2399  0.4909  0.2417  0.2348  0.6477  0.3685; ...
             0.9106  0.1450  0.1233  0.4893  0.4039  0.3532  0.4509  0.6256; ...
             0.1818  0.8530  0.1839  0.3377  0.0965  0.8212  0.5470  0.7802; ...
             0.2638  0.6221  0.2400  0.9001  0.1320  0.0154  0.2963  0.0811; ...
             0.1455  0.3510  0.4173  0.3692  0.9421  0.0430  0.7447  0.9294; ...
             0.1361  0.5132  0.0497  0.1112  0.9561  0.1690  0.1890  0.7757; ...
             0.8693  0.4018  0.9027  0.7803  0.5752  0.6491  0.6868  0.4868]
     Compute the inverse matrix
     >> M1 = inv(M)
   *)
    Let d1 := 
          [[0.8001;0.5797;0.0760;0.9448;0.3897;0.0598;0.7317;0.1835];
           [0.4314;0.5499;0.2399;0.4909;0.2417;0.2348;0.6477;0.3685];
           [0.9106;0.1450;0.1233;0.4893;0.4039;0.3532;0.4509;0.6256];
           [0.1818;0.8530;0.1839;0.3377;0.0965;0.8212;0.5470;0.7802];
           [0.2638;0.6221;0.2400;0.9001;0.1320;0.0154;0.2963;0.0811];
           [0.1455;0.3510;0.4173;0.3692;0.9421;0.0430;0.7447;0.9294];
           [0.1361;0.5132;0.0497;0.1112;0.9561;0.1690;0.1890;0.7757];
           [0.8693;0.4018;0.9027;0.7803;0.5752;0.6491;0.6868;0.4868]].

    (* Time Compute minvertiblebListQ 8 d1. (* 6.5 s *) *)
    (* Time Compute minvListQ 5 d1.         (* 0.29 s *) *)
    (* Time Compute minvListQ 6 d1.         (* 1.19 s *) *)
  End ex4.
  
  (* In summary, for inverse matrices with Q (with the help of Qc):
     1. simple input format, and relatively simple output format.
     2. accuately result compared to MATLAB, but fractions are not intuitive.
     3. Leibniz equal is supported.
   *)
End inv_Q.


(* ======================================================================= *)
(** ** Test solveEq and cramerRule over Qc type *)
Section solveEq_cramerRule_Qc.
  Import MinvMoreAM_Qc.
  Import AMNotations.

  Let M1 : smat 2 := l2m 0 (Q2Qc_dlist [[1;2];[3;4]]%Q).
  Let b1 : vec 2 := l2v 0 (Q2Qc_list [5;6]%Q).
  (* Compute v2l (solveEq M1 b1). *)
  (* Compute v2l (cramerRule M1 b1). *)
  (* Tips: here, these two methods have different computational cost *)

  Let M2 : smat 5 :=
        l2m 0 (Q2Qc_dlist
                 [[1;2;3;4;5];
                  [2;4;3;5;1];
                  [3;1;5;2;4];
                  [4;5;2;3;1];
                  [5;4;1;2;3]]%Q).
  Let b2 : vec 5 := l2v 0 (Q2Qc_list [1;2;3;5;4]%Q).
  (* Compute v2l (solveEq M2 b2). *)
  (* Compute v2l (cramerRule M2 b2). *)
End solveEq_cramerRule_Qc.
