(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Base for matrix inversion
  author    : ZhengPu Shi
  date      : 2023.12

  content   :
  1. invertible, left invertible, right invertible
     https://en.wikipedia.org/wiki/Invertible_matrix
  2. interface for matrix inversion

  remark    :
  1. 有多种逆矩阵计算方法
     (1) minvGE: 基于高斯消元(Gauss Elimination)的逆矩阵。
         适合于数值计算，不可符号计算。
         适用于 r*c 的任意形状的矩阵，所以可以计算左逆和右逆。
         不过目前只支持了 n*n 方阵的情形。
     (2) minvAM: 基于伴随矩阵(Adjoint)的逆矩阵。
         适合于符号计算，也可数值计算(但可能效率较低)。
         仅适用于 n*n 的方阵。
  2. 在Coq中计算的不同方式及其速度比较
     (1) 直接查看结果，不保存
         Eval cbn/cbv/compute in exp. 速度慢
         Eval vm_compute/native_compute in exp. 速度快
         Compute exp.  速度快
     (2) 不查看结果，而是保存到一个标识符。
         Let a := Eval cbn/cbv/compute in exp. 速度慢
         Let a := Eval vm_compute/native_compute in exp. 速度快
     (3) 原因：
         Compute xx 是 Eval vm_compute in xx 的缩写。
         vm_compute 是基于字节码的虚拟机执行
         native_compute 默认是 vm_compute，还可以进一步定制

 *)

Require Export ElementType Matrix MatrixDet.


(* ############################################################################ *)
(** * Matrix is invertible  *)

Section minvtble.
  Context `{HARing : ARing} `{HAeqDec : Dec _ (@eq A)}.
  Add Ring ring_inst : (make_ring_theory HARing).

  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Infix "*" := Amul : A_scope.

  Notation vdot := (@vdot _ Aadd 0 Amul).
  Notation "< a , b >" := (vdot a b) : vec_scope.

  Notation mat r c := (mat A r c).
  Notation smat n := (smat A n).
  Notation mmul := (@mmul _ Aadd 0 Amul).
  Infix "*" := mmul : mat_scope.
  Notation mat1 := (@mat1 _ Azero Aone).
  Notation mmulv := (@mmulv _ Aadd 0 Amul).
  Infix "*v" := mmulv : mat_scope.
  Notation mvmul := (@mvmul _ Aadd 0 Amul).
  Infix "v*" := mvmul : mat_scope.
  Notation mcmul := (@mcmul _ Amul).
  Infix "\.*" := mcmul : mat_scope.
  Notation mdet := (@mdet _ Aadd 0 Aopp Amul 1).
  Notation "| M |" := (mdet M) : mat_scope.
  Notation madj := (@madj _ Aadd 0 Aopp Amul 1).
  Notation "M \A" := (madj M) : mat_scope.
  
  (* ======================================================================= *)
  (** ** Invertible (nonsingular, nondegenerate) matrix *)
  
  (** The matrix `M` is invertible *)
  Definition minvtble {n} (M : smat n) : Prop :=
    exists M', M' * M = mat1 /\ M * M' = mat1.

  (** The matrix `M` is left invertible (i.e., exist a left inverse) *)
  Definition minvtbleL {n} (M : smat n) : Prop := exists N, N * M = mat1.

  (** The matrix `M` is right invertible (i.e., exist a right inverse) *)
  Definition minvtbleR {n} (M : smat n) : Prop := exists N, M * N = mat1.

  (** matrix `M` is invertible, imply `M` is left invertible *)
  Lemma minvtble_imply_minvtbleL : forall {n} (M : smat n),
      minvtble M -> minvtbleL M.
  Proof. intros. hnf in *. destruct H as [M' [H H0]]. exists M'; auto. Qed.

  (** matrix `M` is invertible, imply `M` is right invertible *)
  Lemma minvtble_imply_minvtbleR : forall {n} (M : smat n),
      minvtble M -> minvtbleR M.
  Proof. intros. hnf in *. destruct H as [M' [H H0]]. exists M'; auto. Qed.


  Context `{HField : Field A Aadd 0 Aopp Amul 1}.
  Add Field field_thy_inst : (make_field_theory HField).
  Notation "/ a" := (Ainv a) : A_scope.
  Notation "a / b" := ((a * /b)%A) : A_scope.
  
  (** matrix `M` is left invertible, if and only if the determinant is not zero *)
  Lemma minvtbleL_iff_mdet_neq0 : forall {n} (M : smat n), minvtbleL M <-> |M| <> 0.
  Proof.
    intros. split; intros.
    - hnf in H. destruct H as [M' H].
      apply mmul_eq1_imply_mdet_neq0_r in H. auto.
    - hnf. apply mdet_neq0_imply_mmul_eq1_l. auto.
  Qed.

  (** matrix `M` is right invertible, if and only if the determinant is not zero *)
  Lemma minvtbleR_iff_mdet_neq0 : forall {n} (M : smat n), minvtbleR M <-> |M| <> 0.
  Proof.
    intros. split; intros.
    - hnf in H. destruct H as [M' H].
      apply mmul_eq1_imply_mdet_neq0_l in H. auto.
    - hnf. apply mdet_neq0_imply_mmul_eq1_r. auto.
  Qed.

  (** A matrix `M` is invertible, if and only if the determinant is not zero *)
  Lemma minvtble_iff_mdet_neq0 : forall {n} (M : smat n), minvtble M <-> |M| <> 0.
  Proof.
    intros. split; intros.
    - apply minvtble_imply_minvtbleL in H.
      apply minvtbleL_iff_mdet_neq0; auto.
    - hnf. apply mdet_neq0_imply_mmul_eq1. auto.
  Qed.

  (** matrix `M` is left invertible, imply `M` is invertible *)
  Lemma minvtbleL_imply_minvtble : forall {n} (M : smat n),
      minvtbleL M -> minvtble M.
  Proof.
    intros. rewrite minvtbleL_iff_mdet_neq0 in H.
    rewrite minvtble_iff_mdet_neq0. auto.
  Qed.

  (** matrix `M` is right invertible, imply `M` is invertible *)
  Lemma minvtbleR_imply_minvtble : forall {n} (M : smat n),
      minvtbleR M -> minvtble M.
  Proof.
    intros. rewrite minvtbleR_iff_mdet_neq0 in H.
    rewrite minvtble_iff_mdet_neq0. auto.
  Qed.

  (** matrix `M` is invertible, if and only if `M` is left invertible *)
  Lemma minvtble_iff_minvtbleL : forall {n} (M : smat n),
      minvtble M <-> minvtbleL M.
  Proof.
    intros. split; intros.
    apply minvtble_imply_minvtbleL; auto.
    apply minvtbleL_imply_minvtble; auto.
  Qed.

  (** matrix `M` is invertible, if and only if `M` is right invertible *)
  Lemma minvtble_iff_minvtbleR : forall {n} (M : smat n),
      minvtble M <-> minvtbleR M.
  Proof.
    intros. split; intros.
    apply minvtble_imply_minvtbleR; auto.
    apply minvtbleR_imply_minvtble; auto.
  Qed.

  (** matrix `M` is left invertible, if and only if `M` is right invertible *)
  Lemma minvtbleL_iff_minvtbleR : forall {n} (M : smat n),
      minvtbleL M <-> minvtbleR M.
  Proof.
    intros. rewrite <- minvtble_iff_minvtbleL.
    rewrite <- minvtble_iff_minvtbleR. tauto.
  Qed.

  (** `M * N = mat1` imply `M` is invertible *)
  Lemma mmul_eq1_imply_minvtble_l : forall {n} (M N : smat n),
      M * N = mat1 -> minvtble M.
  Proof. intros. rewrite minvtble_iff_minvtbleR. hnf. exists N; auto. Qed.

  (** `M * N = mat1` imply `N` is invertible *)
  Lemma mmul_eq1_imply_minvtble_r : forall {n} (M N : smat n),
      M * N = mat1 -> minvtble N.
  Proof. intros. rewrite minvtble_iff_minvtbleL. hnf. exists M; auto. Qed.


  (** Transpose preserve `invertible` property *)
  Lemma mtrans_minvtble : forall n (M : smat n),
      minvtble M -> minvtble (M\T).
  Proof.
    intros. hnf in *. destruct H as [E [Hl Hr]]. exists (E\T). split.
    - hnf. rewrite <- mtrans_mmul. rewrite Hr. apply mtrans_mat1.
    - hnf. rewrite <- mtrans_mmul. rewrite Hl. apply mtrans_mat1.
  Qed.

  (** Multiplication preserve `invertible` property *)
  Lemma mmul_minvtble: forall {n} (M N : smat n), 
      minvtble M -> minvtble N -> minvtble (M * N).
  Proof.
    intros. hnf in *. destruct H as [M' [HL HR]], H0 as [N' [HL1 HR1]]; hnf in *.
    exists (N' * M'). split; hnf.
    - rewrite mmul_assoc. rewrite <- (mmul_assoc M' M). rewrite HL, mmul_1_l; auto.
    - rewrite mmul_assoc. rewrite <- (mmul_assoc N N'). rewrite HR1, mmul_1_l; auto.
  Qed.

  (** mat1 is invertible *)
  Lemma mat1_minvtble : forall {n}, minvtble (@mat1 n).
  Proof. intros. hnf. exists mat1. split; hnf; rewrite mmul_1_l; auto. Qed.


  (** Left cancellation law of matrix multiplication *)
  Lemma mmul_cancel_l : forall {r c} (M : smat r) (N1 N2 : mat r c) ,
      minvtble M -> M * N1 = M * N2 -> N1 = N2.
  Proof.
    intros. hnf in H. destruct H as [N [Hl Hr]].
    assert (N * M * N1 = N * M * N2). rewrite !mmul_assoc. rewrite H0. auto.
    rewrite Hl in H. rewrite !mmul_1_l in H. auto.
  Qed.

  (** Right cancellation law of matrix multiplication *)
  Lemma mmul_cancel_r : forall {r c} (M : smat c) (N1 N2 : mat r c) ,
      minvtble M -> N1 * M = N2 * M -> N1 = N2.
  Proof.
    intros. hnf in H. destruct H as [N [Hl Hr]].
    assert (N1 * M * N = N2 * M * N). rewrite H0. auto.
    rewrite !mmul_assoc in H. rewrite Hr in H. rewrite !mmul_1_r in H. auto.
  Qed.

  (** Cancellation law of matrix multiply vector *)
  Lemma mmulv_cancel : forall {n} (M : smat n) (a b : vec n),
      minvtble M -> M *v a = M *v b -> a = b.
  Proof.
    intros. hnf in *. destruct H as [N [Hl Hr]].
    assert (N *v (M *v a) = N *v (M *v b)). rewrite H0. auto.
    rewrite <- !mmulv_assoc in H. rewrite Hl in H. rewrite !mmulv_1_l in H. auto.
  Qed.

  (** Cancellation law of vector multipliy matrix *)
  Lemma mvmul_cancel : forall {n} (M : smat n) (a b : vec n),
      minvtble M -> a v* M = b v* M -> a = b.
  Proof.
    intros. hnf in *. destruct H as [N [Hl Hr]].
    assert (a v* M v* N = b v* M v* N). rewrite H0; auto.
    rewrite <- !mvmul_assoc in H. rewrite Hr in H. rewrite !mvmul_1_r in H. auto.
  Qed.

  (** N1 * M = mat1 -> N2 * M = mat1 -> N1 = N2 *)
  Lemma mmul_eq1_uniq_l : forall {n} (M N1 N2 : smat n),
      N1 * M = mat1 -> N2 * M = mat1 -> N1 = N2.
  Proof.
    intros. rewrite <- H in H0. apply mmul_cancel_r in H0; auto.
    apply mmul_eq1_imply_minvtble_r in H. auto.
  Qed.

  (** M * N1 = mat1 -> M * N2 = mat1 -> N1 = N2 *)
  Lemma mmul_eq1_uniq_r : forall {n} (M N1 N2 : smat n),
      M * N1 = mat1 -> M * N2 = mat1 -> N1 = N2.
  Proof.
    intros. rewrite <- H in H0. apply mmul_cancel_l in H0; auto.
    apply mmul_eq1_imply_minvtble_l in H. auto.
  Qed.

  (** M * N = mat1 -> M = /|N| .* N\A *)
  Lemma mmul_eq1_imply_det_cmul_adj_l : forall {n} (M N : smat n),
      M * N = mat1 -> M = /|N| \.* N\A.
  Proof.
    intros. apply mmul_eq1_uniq_l with (M:=N); auto.
    apply mmul_det_cmul_adj_l. apply mmul_eq1_imply_mdet_neq0_r in H. auto.
  Qed.

  (** M * N = mat1 -> N = /|M| .* M\A *)
  Lemma mmul_eq1_imply_det_cmul_adj_r : forall {n} (M N : smat n),
      M * N = mat1 -> N = /|M| \.* M\A.
  Proof.
    intros. apply mmul_eq1_uniq_r with (M:=M); auto.
    apply mmul_det_cmul_adj_r. apply mmul_eq1_imply_mdet_neq0_l in H. auto.
  Qed.
    
  (** M1 * M2 = mat1 -> M2 * M1 = mat1 *)
  Lemma mmul_eq1_comm : forall {n} (M1 M2 : smat n),
      M1 * M2 = mat1 -> M2 * M1 = mat1.
  Proof.
    (* Tips: I CAN'T PROVE IT ONLY USE INDUCTION *)
    intros.
    apply mmul_eq1_imply_det_cmul_adj_l in H as H0. rewrite H0.
    apply mmul_det_cmul_adj_r. apply mmul_eq1_imply_mdet_neq0_r in H. auto.
  Qed.

  
  (* ======================================================================= *)
  (** ** Singular (degenerate, not invertible) matrix *)
  
  (** The matrix `M` is singular (i.e., not invertible) *)
  Definition msingular {n} (M : smat n) : Prop := ~(minvtble M).
  
End minvtble.


(* ############################################################################ *)
(** * Interface of matrix inversion core theory *)
Module Type MinvCore (E : FieldElementType).
  Export E.
  Open Scope A_scope.
  Open Scope mat_scope.

  (* Add Field field_thy_inst : (make_field_theory Field). *)
  
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation "a / b" := ((a * /b)%A) : A_scope.

  Notation vdot := (@vdot _ Aadd 0 Amul).
  Notation "< a , b >" := (vdot a b) : vec_scope.

  Notation mat r c := (mat A r c).
  Notation smat n := (smat A n).
  Notation mmul := (@mmul _ Aadd 0 Amul).
  Infix "*" := mmul : mat_scope.
  Notation mat1 := (@mat1 _ Azero Aone).
  Notation mmulv := (@mmulv _ Aadd 0 Amul).
  Infix "*v" := mmulv : mat_scope.
  Notation mvmul := (@mvmul _ Aadd 0 Amul).
  Infix "v*" := mvmul : mat_scope.
  Notation mcmul := (@mcmul _ Amul).
  Infix "\.*" := mcmul : mat_scope.
  Notation mdet := (@mdet _ Aadd 0 Aopp Amul 1).
  Notation "| M |" := (mdet M) : mat_scope.
  Notation madj := (@madj _ Aadd 0 Aopp Amul 1).
  Notation "M \A" := (madj M) : mat_scope.
  Notation minvtble := (@minvtble _ Aadd 0 Amul 1).
  Notation msingular := (@msingular _ Aadd 0 Amul 1).
  

  (* ======================================================================= *)
  (** ** Check matrix invertibility *)

  (** Check the invertibility of matrix `M` *)
  Parameter minvtbleb : forall {n} (M : smat n), bool.

  (** minvtble M <-> minvtbleb M = true *)
  Axiom minvtble_iff_minvtbleb_true : forall {n} (M : smat n),
      minvtble M <-> minvtbleb M = true.
  
  (** msingular M <-> minvtbleb M = false *)
  Axiom msingular_iff_minvtbleb_false : forall {n} (M : smat n),
      msingular M <-> minvtbleb M = false.


  (* ======================================================================= *)
  (** ** Inverse matrix (option version) *)

  (** Inverse matrix (option version) *)
  Parameter minvo : forall {n} (M : smat n), option (smat n).
  
  (** `minvo` return `Some`, iff M is invertible *)
  Axiom minvo_Some_iff_minvtble : forall {n} (M : smat n),
      (exists M', minvo M = Some M') <-> minvtble M.

  (** `minvo` return `None`, iff M is singular *)
  Axiom minvo_None_iff_msingular : forall {n} (M : smat n),
      minvo M = None <-> msingular M.

  (** If `minvo M` return `Some M'`, then `M' * M = mat1` *)
  Axiom minvo_Some_imply_eq1_l : forall {n} (M M' : smat n),
      minvo M = Some M' -> M' * M = mat1.

  (** If `minvo M` return `Some M'`, then `M * M' = mat1` *)
  Axiom minvo_Some_imply_eq1_r : forall {n} (M M' : smat n),
      minvo M = Some M' -> M * M' = mat1.

  
  (* ======================================================================= *)
  (** ** Inverse matrix (default value version) *)

  (** Inverse matrix (with identity matrix as default value) *)
  Parameter minv : forall {n} (M : smat n), smat n.
  Notation "M \-1" := (minv M) : mat_scope.

  (** If `minvo M` return `Some N`, then `M\-1` equal to `N` *)
  Axiom minvo_Some_imply_minv : forall {n} (M N : smat n), minvo M = Some N -> M\-1 = N.

  (** If `minvo M` return `None`, then `M\-1` equal to `mat1` *)
  Axiom minvo_None_imply_minv : forall {n} (M  : smat n), minvo M = None -> M\-1 = mat1.
  
  (** M\-1 * M = mat1 *)
  Axiom mmul_minv_l : forall {n} (M : smat n), minvtble M -> M\-1 * M = mat1.
  
End MinvCore.


(* ############################################################################ *)
(** * Matrix inversion theory *)

(** Matrix inversion theory, dependent on `MinvCore` *)
Module Minv (F : FieldElementType) (M : MinvCore F).
  Export F.
  Export M.

  (* ======================================================================= *)
  (** ** More properties for minvtbleb,minvo,minv *)
  
  (** M * N = mat1 -> minvtbleb M = true *)
  Lemma mmul_eq1_imply_minvtbleb_true_l : forall {n} (M N : smat n),
      M * N = mat1 -> minvtbleb M = true.
  Proof.
    intros. apply minvtble_iff_minvtbleb_true.
    apply mmul_eq1_imply_minvtble_l in H; auto.
  Qed.

  (** M * N = mat1 -> minvtbleb N = true. *)
  Lemma mmul_eq1_imply_minvtbleb_true_r : forall {n} (M N : smat n),
      M * N = mat1 -> minvtbleb N = true.
  Proof.
    intros. apply minvtble_iff_minvtbleb_true.
    apply mmul_eq1_imply_minvtble_r in H; auto.
  Qed.

  (** minvtble M -> minvtble (M \-1) *)
  Lemma minv_minvtble : forall {n} (M : smat n),
      minvtble M -> minvtble (M\-1).
  Proof.
    intros. apply minvtble_iff_minvtbleR. hnf.
    exists M. apply mmul_minv_l; auto.
  Qed.
  
  (** M * M\-1 = mat1 *)
  Lemma mmul_minv_r : forall {n} (M : smat n), minvtble M -> M * M\-1 = mat1.
  Proof. intros. apply mmul_minv_l in H. apply mmul_eq1_comm; auto. Qed.
  
  (** M * N = mat1 -> M \-1 = N *)
  Lemma mmul_eq1_imply_minv_l : forall {n} (M N : smat n), M * N = mat1 -> M\-1 = N.
  Proof.
    intros.
    apply mmul_eq1_imply_minvtble_l in H as H'.
    assert (M * N = M * M\-1). rewrite H. rewrite mmul_minv_r; auto.
    apply mmul_cancel_l in H0; auto.
  Qed.

  (** M * N = mat1 -> N \-1 = M *)
  Lemma mmul_eq1_imply_minv_r : forall {n} (M N : smat n), M * N = mat1 -> N\-1 = M.
  Proof.
    intros.
    apply mmul_eq1_imply_minvtble_r in H as H'.
    assert (M * N = N\-1 * N). rewrite H. rewrite mmul_minv_l; auto.
    apply mmul_cancel_r in H0; auto.
  Qed.

  (** mat1 \-1 = mat1 *)
  Lemma minv_mat1 : forall n, @minv n mat1 = mat1.
  Proof.
    intros. apply mmul_eq1_imply_minv_l. rewrite mmul_1_l; auto.
  Qed.

  (** minvtble M -> M \-1 \-1 = M *)
  Lemma minv_minv : forall n (M : smat n), minvtble M -> M \-1 \-1 = M.
  Proof.
    intros. apply mmul_eq1_imply_minv_l. apply mmul_minv_l; auto.
  Qed.

  (** (M * N)\-1 = (N\-1) * (M\-1) *)
  Lemma minv_mmul : forall n (M N : smat n),
      minvtble M -> minvtble N -> (M * N)\-1 = N\-1 * M\-1.
  Proof.
    intros. apply mmul_eq1_imply_minv_l. rewrite !mmul_assoc.
    rewrite <- (mmul_assoc N). rewrite mmul_minv_r; auto.
    rewrite mmul_1_l. apply mmul_minv_r; auto.
  Qed.

  (** (M \T) \-1 = (M \-1) \T *)
  Lemma minv_mtrans : forall n (M : smat n),
      minvtble M -> (M \T) \-1 = (M \-1) \T.
  Proof.
    intros. apply mmul_eq1_imply_minv_l. rewrite <- mtrans_mmul.
    rewrite mmul_minv_l; auto. rewrite mtrans_mat1; auto.
  Qed.

  (** |M \-1| = / (|M|) *)
  Lemma mdet_minv : forall {n} (M : smat n), minvtble M -> |M\-1| = / |M|.
  Proof.
    intros.
    assert (|M * M\-1| = |@mat1 n|). f_equal. apply mmul_minv_r; auto.
    rewrite mdet_mmul, mdet_mat1 in H0.
    apply field_inv_eq_l in H0; auto.
    apply minvtble_iff_mdet_neq0; auto.
  Qed.
  

  (* ======================================================================= *)
  (** ** Inverse matrix with lists for input and output *)
  
  (** Check matrix invertibility with lists as input *)
  Definition minvtblebList (n : nat) (dl : dlist A) : bool :=
    @minvtbleb n (l2m 0 dl).

  (** Inverse matrix with lists for input and output *)
  Definition minvList (n : nat) (dl : dlist A) : dlist A :=
    m2l (@minv n (l2m 0 dl)).

  (** `minvtbleb_list` is equal to `minvtbleb`, by definition *)
  Lemma minvtblebList_spec : forall (n : nat) (dl : dlist A),
      minvtblebList n dl = @minvtbleb n (l2m 0 dl).
  Proof. intros. auto. Qed.

  (** The matrix of [minv_list dl] is the inverse of the matrix of [dl] *)
  Theorem minvList_spec : forall (n : nat) (dl : dlist A),
      let M : smat n := l2m 0 dl in
      let M' : smat n := l2m 0 (minvList n dl) in
      minvtblebList n dl = true ->
      M' * M = mat1.
  Proof.
    intros. unfold minvtblebList in H. unfold minvList in M'.
    unfold M', M. rewrite l2m_m2l. apply mmul_minv_l; auto.
    apply minvtble_iff_minvtbleb_true. auto.
  Qed.


  (* ======================================================================= *)
  (** ** Solve equation by inverse matrix *)

  (** Solve the equation with the form of C*x=b. *)
  Definition solveEq {n} (C : smat n) (b : vec n) : vec n := (C\-1) *v b.

  (** C *v (solveEqAM C b) = b *)
  Theorem solveEq_spec : forall {n} (C : smat n) (b : @vec A n),
      minvtble C -> C *v (solveEq C b) = b.
  Proof.
    intros. unfold solveEq.
    rewrite <- mmulv_assoc. rewrite mmul_minv_r; auto. rewrite mmulv_1_l. auto.
  Qed.

  (** Solve the equation with the form of C*x=b over list *)
  Definition solveEqList (n : nat) (lC : dlist A) (lb : list A) : list A :=
    let C : smat n := l2m 0 lC in
    let b : vec n := l2v 0 lb in
    let x := solveEq C b in
    v2l x.

  (** {solveEqList lC lb} = solveEq {lC} {lb} *)
  Theorem solveEqList_spec : forall n (lC : dlist A) (lb : list A),
      let C : smat n := l2m 0 lC in
      let b : vec n := l2v 0 lb in
      l2v 0 (solveEqList n lC lb) = solveEq C b.
  Proof. intros. unfold solveEqList. rewrite l2v_v2l. auto. Qed.
  
End Minv.
