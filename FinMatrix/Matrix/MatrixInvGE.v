(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix Inversion based on Gauss Elimination
  author    : Zhengpu Shi
  date      : 2023.12

  remark    :
  1. First stage, we use a simple case of `n × n` matrix
  2. Second stage, we should consider the case of `m × n` matrix
 *)

Require Import NatExt.
Require Export Matrix MatrixGauss MatrixInvertible.

Generalizable Variable tA Aadd Azero Aopp Amul Aone Ainv.


(* ############################################################################ *)
(** * Matrix Inversion based on Gauss Elimination *)
Section minvGE.
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

  Notation mdet := (@mdet _ Aadd 0 Aopp Amul 1 _).
  Notation "| M |" := (mdet M) : mat_scope.
  
  (* ======================================================================= *)
  (** ** Check matrix invertibility *)

  (** Check the invertibility of matrix `M` *)
  Definition minvtblebGE {n} : smat n -> bool :=
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
  
  (** minvtble M <-> minvtblebGE M = true *)
  Lemma minvtble_iff_minvtblebGE_true : forall {n} (M : smat n),
      minvtble M <-> minvtblebGE M = true.
  Proof.
    intros. split; intros.
    - hnf in H. destruct H as [M' [Hl Hr]]. destruct n; auto.
      apply (mmul_eq1_imply_toREF_Some_r) in Hl. destruct Hl as [[l1 M1]].
      unfold minvtblebGE. rewrite H. auto.
    - apply minvtble_iff_minvtbleL. hnf.
      unfold minvtblebGE in H. destruct n.
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
  
  (** msingular M <-> minvtblebGE M = false *)
  Lemma msingular_iff_minvtblebGE_false : forall {n} (M : smat n),
      msingular M <-> minvtblebGE M = false.
  Proof.
    intros. unfold msingular. rewrite minvtble_iff_minvtblebGE_true.
    rewrite not_true_iff_false. tauto.
  Qed.

  (** M * N = mat1 -> minvtblebGE M = true *)
  Lemma mmul_eq1_imply_minvtblebGE_true_l : forall {n} (M N : smat n),
      M * N = mat1 -> minvtblebGE M = true.
  Proof.
    intros. apply minvtble_iff_minvtblebGE_true.
    apply mmul_eq1_imply_minvtble_l in H; auto.
  Qed.

  (** M * N = mat1 -> minvtblebGE N = true. *)
  Lemma mmul_eq1_imply_minvtblebGE_true_r : forall {n} (M N : smat n),
      M * N = mat1 -> minvtblebGE N = true.
  Proof.
    intros. apply minvtble_iff_minvtblebGE_true.
    apply mmul_eq1_imply_minvtble_r in H; auto.
  Qed.


  (* ******************************************************************* *)
  (** ** Inverse matrix (option version) *)
  
  (** Inverse matrix (option version) *)
  Definition minvoGE {n} : smat n -> option (smat n) :=
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
  
  (** `minvoGE` return `Some`, iff M is invertible *)
  Lemma minvoGE_Some_iff_minvtble : forall {n} (M : smat n),
      (exists M', minvoGE M = Some M') <-> minvtble M.
  Proof.
    intros. rewrite minvtble_iff_minvtblebGE_true.
    unfold minvoGE, minvtblebGE. destruct n.
    - split; intros; auto. exists M. f_equal. apply v0eq.
    - split; intros.
      + destruct H as [M' H]. destruct toREF as [[l1 M1]|]; try easy.
      + destruct toREF as [[l1 M1]|] eqn:T1; try easy.
        destruct toRREF as [l2 M2] eqn:T2. eexists; auto.
  Qed.

  (** `minvoGE` return `None`, iff M is singular *)
  Lemma minvoGE_None_iff_msingular : forall {n} (M : smat n),
      minvoGE M = None <-> msingular M.
  Proof.
    intros. unfold msingular. rewrite <- minvoGE_Some_iff_minvtble.
    unfold minvoGE. destruct n.
    - split; intros; try easy. destruct H. exists mat1; auto.
    - split; intros; try easy.
      + intro. destruct H0 as [M' H0]. rewrite H in H0. easy.
      + destruct toREF as [[l1 M1]|] eqn:T1; try easy.
        destruct toRREF as [l2 M2] eqn:T2. destruct H. eexists; auto.
  Qed.

  (** If `minvoGE M` return `Some M'`, then `M' * M = mat1` *)
  Lemma minvoGE_Some_imply_eq1_l : forall {n} (M M' : smat n),
      minvoGE M = Some M' -> M' * M = mat1.
  Proof.
    intros. unfold minvoGE in H. destruct n.
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

  (** If `minvoGE M` return `Some M'`, then `M * M' = mat1` *)
  Lemma minvoGE_Some_imply_eq1_r : forall {n} (M M' : smat n),
      minvoGE M = Some M' -> M * M' = mat1.
  Proof.
    intros.
    (* Quickly finished the proof (but, we need Adjoint Matrix method) *)
    (* apply minvoGE_Some_imply_eq1_l in H as H'. *)
    (* apply mmul_eq1_comm in H'. auto. *)

    (* Let's proof it directly *)
    unfold minvoGE in H. destruct n.
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
  Definition minvGE {n} : smat n -> smat n :=
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
  Notation "M \-1" := (minvGE M) : mat_scope.

  (** If `minvoGE M` return `Some N`, then `M\-1` equal to `N` *)
  Lemma minvoGE_Some_imply_minvGE : forall {n} (M N : smat n),
      minvoGE M = Some N -> M\-1 = N.
  Proof.
    intros. unfold minvoGE, minvGE in *. destruct n. inv H. auto.
    destruct toREF as [[l1 M1]|] eqn:T1; try easy.
    destruct toRREF as [l2] eqn:T2.
    inv H. auto.
  Qed.
  
  (** M\-1 * M = mat1 *)
  Lemma mmul_minvGE_l : forall {n} (M : smat n), minvtble M -> M\-1 * M = mat1.
  Proof.
    intros. apply minvtble_iff_minvtblebGE_true in H as H1.
    unfold minvtblebGE, minvGE in *. destruct n. apply v0eq.
    destruct toREF as [[l1 M1]|] eqn:T1; try easy.
    destruct toRREF as [l2 M2] eqn:T2.
    rewrite rowOps2mat_app. rewrite mmul_assoc.
    apply toREF_eq in T1 as T1'. rewrite T1'.
    apply toRREF_eq in T2 as T2'. rewrite T2'.
    apply toRREF_mat1 in T2; auto.
    apply toREF_mUnitUpperTrig in T1; auto.
  Qed.
  
  (** M * M\-1 = mat1 *)
  Lemma mmul_minvGE_r : forall {n} (M : smat n), minvtble M -> M * M\-1 = mat1.
  Proof. intros. apply mmul_minvGE_l in H. apply mmul_eq1_comm; auto. Qed.

  (** minvtble M -> minvtble (M \-1) *)
  Lemma minvGE_minvtble : forall {n} (M : smat n), minvtble M -> minvtble (M\-1).
  Proof.
    intros. apply minvtble_iff_minvtbleR. hnf.
    exists M. apply mmul_minvGE_l; auto.
  Qed.
  
  (** M * N = mat1 -> M \-1 = N *)
  Lemma mmul_eq1_imply_minvGE_l : forall {n} (M N : smat n), M * N = mat1 -> M\-1 = N.
  Proof.
    intros. apply mmul_eq1_imply_minvtble_l in H as H'.
    assert (M * N = M * M\-1). rewrite H. rewrite mmul_minvGE_r; auto.
    apply mmul_cancel_l in H0; auto.
  Qed.

  (** M * N = mat1 -> N \-1 = M *)
  Lemma mmul_eq1_imply_minvGE_r : forall {n} (M N : smat n), M * N = mat1 -> N\-1 = M.
  Proof.
    intros. apply mmul_eq1_imply_minvtble_r in H as H'.
    assert (M * N = N\-1 * N). rewrite H. rewrite mmul_minvGE_l; auto.
    apply mmul_cancel_r in H0; auto.
  Qed.

  (** mat1 \-1 = mat1 *)
  Lemma minvGE_mat1 : forall n, (@mat1 n)\-1 = mat1.
  Proof. intros. apply mmul_eq1_imply_minvGE_l. rewrite mmul_1_l; auto. Qed.

  (** minvtble M -> M \-1 \-1 = M *)
  Lemma minvGE_minvGE : forall n (M : smat n), minvtble M -> M \-1 \-1 = M.
  Proof. intros. apply mmul_eq1_imply_minvGE_l. apply mmul_minvGE_l; auto. Qed.

  (** (M * N)\-1 = (N\-1) * (M\-1) *)
  Lemma minvGE_mmul : forall n (M N : smat n),
      minvtble M -> minvtble N -> (M * N)\-1 = N\-1 * M\-1.
  Proof.
    intros. apply mmul_eq1_imply_minvGE_l. rewrite !mmul_assoc.
    rewrite <- (mmul_assoc N). rewrite mmul_minvGE_r; auto.
    rewrite mmul_1_l. apply mmul_minvGE_r; auto.
  Qed.

  (** (M \T) \-1 = (M \-1) \T *)
  Lemma minvGE_mtrans : forall n (M : smat n), minvtble M -> (M \T) \-1 = (M \-1) \T.
  Proof.
    intros. apply mmul_eq1_imply_minvGE_l. rewrite <- mtrans_mmul.
    rewrite mmul_minvGE_l; auto. rewrite mtrans_mat1; auto.
  Qed.

  (** |M \-1| = / (|M|) *)
  Lemma mdet_minvGE : forall {n} (M : smat n), minvtble M -> |M\-1| = / |M|.
  Proof.
    intros. assert (|M * M\-1| = |@mat1 n|). f_equal. apply mmul_minvGE_r; auto.
    rewrite mdet_mmul, mdet_mat1 in H0.
    apply field_inv_uniq_l in H0; auto.
    apply minvtble_iff_mdet_neq0; auto.
  Qed.

  (* ======================================================================= *)
  (** ** Inverse matrix with lists for input and output by GE *)
  
  (** Check matrix invertibility with lists as input *)
  Definition minvtblebListGE (n : nat) (dl : dlist tA) : bool :=
    @minvtblebGE n (l2m 0 dl).

  (** Inverse matrix with lists for input and output *)
  Definition minvListGE (n : nat) (dl : dlist tA) : dlist tA :=
    m2l (@minvGE n (l2m 0 dl)).

  (** `minvtblebListGE` is equivalent to `minvtblebGE`, by definition *)
  Lemma minvtblebListGE_spec : forall (n : nat) (dl : dlist tA),
      minvtblebListGE n dl = @minvtblebGE n (l2m 0 dl).
  Proof. intros. auto. Qed.

  (** The matrix of [minvListGE dl] is the inverse of the matrix of [dl] *)
  Lemma minvListGE_spec : forall (n : nat) (dl : dlist tA),
      let M : smat n := l2m 0 dl in
      let M' : smat n := l2m 0 (minvListGE n dl) in
      minvtblebListGE n dl = true ->
      M' * M = mat1.
  Proof.
    intros. unfold minvtblebListGE in H. unfold minvListGE in M'.
    unfold M', M. rewrite l2m_m2l. apply mmul_minvGE_l; auto.
    apply minvtble_iff_minvtblebGE_true. auto.
  Qed.

  (* ======================================================================= *)
  (** ** Solve equation with inverse matrix by GE *)

  (** Solve the equation A*x=b. *)
  Definition solveEqGE {n} (A : smat n) (b : vec n) : vec n := (A\-1) *v b.

  (** A *v (solveEqGE A b) = b *)
  Lemma solveEqGE_spec : forall {n} (A : smat n) (b : vec n),
      minvtble A -> A *v (solveEqGE A b) = b.
  Proof.
    intros. unfold solveEqGE.
    rewrite <- mmulv_assoc. rewrite mmul_minvGE_r; auto. rewrite mmulv_1_l. auto.
  Qed.

  (** Solve the equation A*x=b over list *)
  Definition solveEqListGE (n : nat) (lA : dlist tA) (lb : list tA) : list tA :=
    let A : smat n := l2m 0 lA in
    let b : vec n := l2v 0 lb in
    let x := solveEqGE A b in
    v2l x.

  (** {solveEqListGE lA lb} = solveEqGE {lA} {lb} *)
  Lemma solveEqListGE_spec : forall n (lA : dlist tA) (lb : list tA),
      let A : smat n := l2m 0 lA in
      let b : vec n := l2v 0 lb in
      l2v 0 (solveEqListGE n lA lb) = solveEqGE A b.
  Proof. intros. unfold solveEqListGE. rewrite l2v_v2l. auto. Qed.
  
End minvGE.
