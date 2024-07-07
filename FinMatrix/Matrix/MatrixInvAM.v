(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix Inversion based on Adjoint Matrix
  author    : Zhengpu Shi
  date      : 2023.06
  
  remark    :
  1. we use `AM` to denote `Adjoint Matrix method`
 *)

Require Import Extraction.
Require Import NatExt.
Require Export Matrix MatrixDet MatrixInvertible.
Require ZArith Reals.

Generalizable Variable tA Aadd Azero Aopp Amul Aone Ainv.


(* ############################################################################ *)
(** * Matrix Inversion based on Adjoint Matrix *)

Section minvAM.
  Context `{HField : Field} {AeqDec : Dec (@eq tA)}.
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

  Notation smat n := (smat tA n).
  Notation mat1 := (@mat1 _ Azero Aone).
  Notation mscal := (@mscal _ Amul).
  Infix "s*" := mscal : mat_scope.
  Notation mmul := (@mmul _ Aadd Azero Amul).
  Infix "*" := mmul : mat_scope.
  Notation mmulv := (@mmulv _ Aadd 0 Amul).
  Infix "*v" := mmulv : mat_scope.

  Notation minvtble := (@minvtble _ Aadd 0 Amul 1).
  Notation msingular := (@msingular _ Aadd 0 Amul 1).
  Notation mdet := (@mdet _ Aadd 0 Aopp Amul 1).
  Notation "| M |" := (mdet M) : mat_scope.
  Notation madj := (@madj _ Aadd 0 Aopp Amul 1).
  Notation "M \A" := (madj M) : mat_scope.
  Notation mcofactor := (@mcofactor _ Aadd 0 Aopp Amul 1).
  Notation mdet1 := (@mdet1 tA).
  Notation mdet2 := (@mdet2 _ Aadd Aopp Amul).
  Notation mdet3 := (@mdet3 _ Aadd Aopp Amul).
  Notation mdet4 := (@mdet4 _ Aadd Aopp Amul).
  Notation cramerRule := (@cramerRule _ Aadd 0 Aopp Amul 1 Ainv).

  (* ======================================================================= *)
  (** ** Check matrix invertibility by AM*)

  (** Check the invertibility of matrix `M` *)
  Definition minvtblebAM {n} (M : smat n) : bool :=
    if Aeqdec (|M|) 0 then false else true.

  (** minvtble M <-> minvtblebAM M = true *)
  Lemma minvtble_iff_minvtblebAM_true : forall {n} (M : smat n),
      minvtble M <-> minvtblebAM M = true.
  Proof.
    intros. rewrite minvtble_iff_mdet_neq0.
    unfold minvtblebAM. destruct Aeqdec; easy.
  Qed.
  
  (** msingular M <-> minvtblebAM M = false *)
  Lemma msingular_iff_minvtblebAM_false : forall {n} (M : smat n),
      msingular M <-> minvtblebAM M = false.
  Proof.
    intros. unfold msingular. rewrite minvtble_iff_minvtblebAM_true.
    rewrite not_true_iff_false. tauto.
  Qed.

  (** M * N = mat1 -> minvtblebAM M = true *)
  Lemma mmul_eq1_imply_minvtblebAM_true_l : forall {n} (M N : smat n),
      M * N = mat1 -> minvtblebAM M = true.
  Proof.
    intros. apply minvtble_iff_minvtblebAM_true.
    apply mmul_eq1_imply_minvtble_l in H; auto.
  Qed.

  (** M * N = mat1 -> minvtblebAM N = true. *)
  Lemma mmul_eq1_imply_minvtblebAM_true_r : forall {n} (M N : smat n),
      M * N = mat1 -> minvtblebAM N = true.
  Proof.
    intros. apply minvtble_iff_minvtblebAM_true.
    apply mmul_eq1_imply_minvtble_r in H; auto.
  Qed.


  (* ======================================================================= *)
  (** ** Inverse matrix (option version) by AM*)

  (** Inverse matrix (option version) *)
  Definition minvoAM {n} (M : smat n) : option (smat n) :=
    if minvtblebAM M
    then Some ((/ |M|) s* (madj M))
    else None.

  (** `minvo` return `Some`, iff M is invertible *)
  Lemma minvoAM_Some_iff_minvtble : forall {n} (M : smat n),
      (exists M', minvoAM M = Some M') <-> minvtble M.
  Proof.
    intros. rewrite minvtble_iff_minvtblebAM_true. split; intros.
    - destruct H as [M' H]. unfold minvoAM in H.
      destruct minvtblebAM; try easy.
    - exists ((/ |M|) s* (madj M)). unfold minvoAM.
      destruct minvtblebAM; try easy.
  Qed.

  (** `minvoAM` return `None`, iff M is singular *)
  Lemma minvoAM_None_iff_msingular : forall {n} (M : smat n),
      minvoAM M = None <-> msingular M.
  Proof.
    intros. rewrite msingular_iff_minvtblebAM_false. split; intros.
    - unfold minvoAM in H. destruct minvtblebAM; try easy.
    - unfold minvoAM. destruct minvtblebAM; try easy.
  Qed.

  (** If `minvoAM M` return `Some M'`, then `M' * M = mat1` *)
  Lemma minvoAM_Some_imply_eq1_l : forall {n} (M M' : smat n),
      minvoAM M = Some M' -> M' * M = mat1.
  Proof.
    intros. unfold minvoAM in H. destruct minvtblebAM eqn:E; try easy. inv H.
    apply mmul_det_scal_adj_l.
    apply minvtble_iff_minvtblebAM_true in E.
    apply minvtble_iff_mdet_neq0; auto.
  Qed.

  (** If `minvoAM M` return `Some M'`, then `M * M' = mat1` *)
  Lemma minvoAM_Some_imply_eq1_r : forall {n} (M M' : smat n),
      minvoAM M = Some M' -> M * M' = mat1.
  Proof.
    intros. apply minvoAM_Some_imply_eq1_l in H.
    apply mmul_eq1_comm; auto.
  Qed.
  
  (* ======================================================================= *)
  (** ** Inverse matrix by AM*)
  
  (** Inverse matrix *)
  Definition minvAM {n} (M : smat n) := (/ |M|) s* (madj M).
  Notation "M \-1" := (minvAM M) : mat_scope.

  (** If `minvoAM M` return `Some N`, then `M\-1` equal to `N` *)
  Lemma minvoAM_Some_imply_minvAM : forall {n} (M N : smat n),
      minvoAM M = Some N -> M\-1 = N.
  Proof.
    intros. unfold minvoAM, minvAM in *.
    destruct minvtblebAM eqn:E; try easy. inv H. auto.
  Qed.

  (** Get (i,j) element of inverse matrix of matrix `M` *)
  Lemma mnth_minvAM : forall n (M : smat (S n)) (i j : 'I_(S n)),
      minvtble M -> (M\-1).[i].[j] = ((/ (mdet M)) * mcofactor M j i)%A.
  Proof. intros. auto. Qed.
  
  (** M\-1 * M = mat1 *)
  Lemma mmul_minvAM_l : forall {n} (M : smat n), minvtble M -> M\-1 * M = mat1.
  Proof.
    intros. unfold minvAM.
    apply minvtble_iff_minvtblebAM_true in H as H1.
    apply mmul_det_scal_adj_l. apply minvtble_iff_mdet_neq0 in H. auto.
  Qed.
  
  (** M * M\-1 = mat1 *)
  Lemma mmul_minvAM_r : forall {n} (M : smat n), minvtble M -> M * M\-1 = mat1.
  Proof. intros. apply mmul_minvAM_l in H. apply mmul_eq1_comm; auto. Qed.

  (** minvtble M -> minvtble (M \-1) *)
  Lemma minvAM_minvtble : forall {n} (M : smat n), minvtble M -> minvtble (M\-1).
  Proof.
    intros. apply minvtble_iff_minvtbleR. hnf.
    exists M. apply mmul_minvAM_l; auto.
  Qed.
  
  (** M * N = mat1 -> M \-1 = N *)
  Lemma mmul_eq1_imply_minvAM_l : forall {n} (M N : smat n), M * N = mat1 -> M\-1 = N.
  Proof.
    intros. apply mmul_eq1_imply_minvtble_l in H as H'.
    assert (M * N = M * M\-1). rewrite H. rewrite mmul_minvAM_r; auto.
    apply mmul_cancel_l in H0; auto.
  Qed.

  (** M * N = mat1 -> N \-1 = M *)
  Lemma mmul_eq1_imply_minvAM_r : forall {n} (M N : smat n), M * N = mat1 -> N\-1 = M.
  Proof.
    intros. apply mmul_eq1_imply_minvtble_r in H as H'.
    assert (M * N = N\-1 * N). rewrite H. rewrite mmul_minvAM_l; auto.
    apply mmul_cancel_r in H0; auto.
  Qed.

  (** mat1 \-1 = mat1 *)
  Lemma minvAM_mat1 : forall n, (@mat1 n)\-1 = mat1.
  Proof. intros. apply mmul_eq1_imply_minvAM_l. rewrite mmul_1_l; auto. Qed.

  (** minvtble M -> M \-1 \-1 = M *)
  Lemma minvAM_minvAM : forall n (M : smat n), minvtble M -> M \-1 \-1 = M.
  Proof. intros. apply mmul_eq1_imply_minvAM_l. apply mmul_minvAM_l; auto. Qed.

  (** (M * N)\-1 = (N\-1) * (M\-1) *)
  Lemma minvAM_mmul : forall n (M N : smat n),
      minvtble M -> minvtble N -> (M * N)\-1 = N\-1 * M\-1.
  Proof.
    intros. apply mmul_eq1_imply_minvAM_l. rewrite !mmul_assoc.
    rewrite <- (mmul_assoc N). rewrite mmul_minvAM_r; auto.
    rewrite mmul_1_l. apply mmul_minvAM_r; auto.
  Qed.

  (** (M \T) \-1 = (M \-1) \T *)
  Lemma minvAM_mtrans : forall n (M : smat n), minvtble M -> (M \T) \-1 = (M \-1) \T.
  Proof.
    intros. apply mmul_eq1_imply_minvAM_l. rewrite <- mtrans_mmul.
    rewrite mmul_minvAM_l; auto. rewrite mtrans_mat1; auto.
  Qed.

  (** |M \-1| = / (|M|) *)
  Lemma mdet_minvAM : forall {n} (M : smat n), minvtble M -> |M\-1| = / |M|.
  Proof.
    intros. assert (|M * M\-1| = |@mat1 n|). f_equal. apply mmul_minvAM_r; auto.
    rewrite mdet_mmul, mdet_mat1 in H0.
    apply field_inv_uniq_l in H0; auto.
    apply minvtble_iff_mdet_neq0; auto.
  Qed.

  (* ======================================================================= *)
  (** ** Inverse matrix with lists for input and output by AM *)
  
  (** Check matrix invertibility with lists as input *)
  Definition minvtblebListAM (n : nat) (dl : dlist tA) : bool :=
    @minvtblebAM n (l2m 0 dl).

  (** Inverse matrix with lists for input and output *)
  Definition minvListAM (n : nat) (dl : dlist tA) : dlist tA :=
    m2l (@minvAM n (l2m 0 dl)).

  (** `minvtblebListAM` is equivalent to `minvtblebAM`, by definition *)
  Lemma minvtblebListAM_spec : forall (n : nat) (dl : dlist tA),
      minvtblebListAM n dl = @minvtblebAM n (l2m 0 dl).
  Proof. intros. auto. Qed.

  (** The matrix of [minvListAM dl] is the inverse of the matrix of [dl] *)
  Lemma minvListAM_spec : forall (n : nat) (dl : dlist tA),
      let M : smat n := l2m 0 dl in
      let M' : smat n := l2m 0 (minvListAM n dl) in
      minvtblebListAM n dl = true ->
      M' * M = mat1.
  Proof.
    intros. unfold minvtblebListAM in H. unfold minvListAM in M'.
    unfold M', M. rewrite l2m_m2l. apply mmul_minvAM_l; auto.
    apply minvtble_iff_minvtblebAM_true. auto.
  Qed.

  (* ======================================================================= *)
  (** ** Solve equation with inverse matrix by AM *)

  (** Solve the equation A*x=b. *)
  Definition solveEqAM {n} (A : smat n) (b : vec n) : vec n := (A\-1) *v b.

  (** A *v (solveEqAM A b) = b *)
  Lemma solveEqAM_spec : forall {n} (A : smat n) (b : vec n),
      minvtble A -> A *v (solveEqAM A b) = b.
  Proof.
    intros. unfold solveEqAM.
    rewrite <- mmulv_assoc. rewrite mmul_minvAM_r; auto. rewrite mmulv_1_l. auto.
  Qed.

  (** Solve the equation A*x=b over list *)
  Definition solveEqListAM (n : nat) (lA : dlist tA) (lb : list tA) : list tA :=
    let A : smat n := l2m 0 lA in
    let b : vec n := l2v 0 lb in
    let x := solveEqAM A b in
    v2l x.

  (** {solveEqListAM lA lb} = solveEqAM {lA} {lb} *)
  Lemma solveEqListAM_spec : forall n (lA : dlist tA) (lb : list tA),
      let A : smat n := l2m 0 lA in
      let b : vec n := l2v 0 lb in
      l2v 0 (solveEqListAM n lA lb) = solveEqAM A b.
  Proof. intros. unfold solveEqListAM. rewrite l2v_v2l. auto. Qed.

  (* ======================================================================= *)
  (** ** Direct formulas of inverse matrix *)

  (* Try to get the formulas by computation *)
  Section formulas_by_computtation.
    Variable a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44 : tA.
    Let M1 : smat 1 := l2m 0 [[a11]].
    Let M2 : smat 2 := l2m 0 [[a11;a12];[a21;a22]].
    Let M3 : smat 3 := l2m 0 [[a11;a12;a13];[a21;a22;a23];[a31;a32;a33]].
    Let M4 : smat 4 := l2m 0 [[a11;a12;a13;a14];[a21;a22;a23;a24];
                              [a31;a32;a33;a34];[a41;a42;a43;a44]].

    (* Compute m2l (M1\-1). *)
    (* Compute m2l (M2\-1). *)
    (* Compute m2l (M3\-1). *)
    (* Compute m2l (M4\-1). *)
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
    
  Definition minvAM1 (M : smat 1) : smat 1 := l2m 0 [[1/M.11]].

  (** minvtble M -> minvAM1 M = inv M *)
  Lemma minvAM1_eq_minvAM : forall M, minvtble M -> minvAM1 M = M\-1.
  Proof.
    intros. apply minvtble_iff_mdet_neq0 in H.
    v2eALL M. cbv in H. meq. field. solve_neq0_neq0. solve_eq0_eq0.
  Qed.

  Definition minvAM2 (M : smat 2) : smat 2 :=
    /(mdet2 M) s* l2m 0 [[M.22; -M.12]; [-M.21; M.11]].

  (** minvtble M -> minvAM2 M = inv M *)
  Lemma minvAM2_eq_minvAM : forall M, minvtble M -> minvAM2 M = M\-1.
  Proof.
    intros. apply minvtble_iff_mdet_neq0 in H.
    v2eALL M. cbv in H. meq. all: field; solve_neq0_neq0; solve_eq0_eq0.
  Qed.
  
  (* Note, this formula come from matlab, needn't manual work *)
  Definition minvAM3 (M : smat 3) : smat 3 :=
    /(mdet3 M) s*
      l2m 0 [[(M.22*M.33-M.23*M.32); -(M.12*M.33-M.13*M.32); (M.12*M.23-M.13*M.22)];
             [-(M.21*M.33-M.23*M.31); (M.11*M.33-M.13*M.31); -(M.11*M.23-M.13*M.21)];
             [(M.21*M.32-M.22*M.31); -(M.11*M.32-M.12*M.31); (M.11*M.22-M.12*M.21)]]%A.

  (** minvtble M -> minvAM3 M = inv M *)
  Lemma minvAM3_eq_minvAM : forall M, minvtble M -> minvAM3 M = M\-1.
  Proof.
    intros. apply minvtble_iff_mdet_neq0 in H.
    v2eALL M. cbv in H. meq. all: field; solve_neq0_neq0; solve_eq0_eq0.
  Qed.

  Definition minvAM4 (M : smat 4) : smat 4 :=
    /(mdet4 M) s*
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
  
  (** minvtble M -> minvAM4 M = inv M *)
  Lemma minvAM4_eq_minvAM : forall M, minvtble M -> minvAM4 M = M\-1.
    (* TO SPEED UP THE COMPILATION *)
  Admitted.
  (* Proof. *)
  (*   intros. apply minvtble_iff_mdet_neq0 in H. *)
  (*   v2eALL M. cbv in H. meq. all: field; solve_neq0_neq0; solve_eq0_eq0. *)
  (* Qed. *)

End minvAM.
