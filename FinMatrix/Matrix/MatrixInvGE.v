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


(* ############################################################################ *)
(** * Test *)

(* ******************************************************************* *)
(** ** Test inverse matrix on Qc *)

Module MinvGE_Qc := MinvGE FieldElementTypeQc.

Section test_Qc.
  Import MinvGE_Qc.

  Open Scope Q_scope.
  Open Scope Qc_scope.
  Open Scope mat_scope.
  
  (** Example 1: a `3x3` matrix *)
  Section ex1.

    (* [1 3 1]     [-1 -1  2]
       [2 1 1] <-> [ 0 -1  1]
       [2 2 1]     [ 2  4 -5] *)
    Let d1 := Q2Qc_dlist [[1;3;1];[2;1;1];[2;2;1]]%Q.
    Let d2 := Q2Qc_dlist [[-1;-1;2];[0;-1;1];[2;4;-5]]%Q.
    (* Note, we need the `Q2Qc` function to typing term of `Qc` type *)
    
    (* Compute minvtblebList 3 d1. *)
    (* Compute minvList 3 d1. *)
    (* Compute minvList 3 d2. *)

    Goal minvList 3 d1 = d2.
    Proof. cbv. list_eq; f_equal; apply proof_irrelevance. Qed.
    
    (* Note, the `canon` part is unnecessary for users. 
       But we can remove the proof part easily *)
    (* Compute Qc2Q_dlist (minvList 3 d1). *)
  End ex1.

  (* Using Qc type, in summary:
     1. the input need `Q2Qc` function
     2. the output has unnecessary proofs *)

  (* We can define more convenient functions with Q type *)
  Open Scope Q_scope.

  (** Check matrix invertibility with rational number lists *)
  Definition minvtblebListQ (n : nat) (d : dlist Q) : bool :=
    minvtblebList n (Q2Qc_dlist d).
  
  (** Inverse matrix with rational number lists *)
  Definition minvListQ (n : nat) (dl : dlist Q) : dlist Q :=
    Qc2Q_dlist (minvList n (Q2Qc_dlist dl)).
  
  (** Example 2: a `3x3` matrix *)
  Section ex2.

    (* [1 3 1]     [-1 -1  2]
       [2 1 1] <-> [ 0 -1  1]
       [2 2 1]     [ 2  4 -5] *)
    Let d1 := [[1;3;1];[2;1;1];[2;2;1]].
    Let d2 := [[-1;-1;2];[0;-1;1];[2;4;-5]].
    
    (* Compute minvtblebListQ 3 d1. *)
    (* Compute minvListQ 3 d1. *)
    (* Compute minvListQ 3 d2. *)
    (* Note, we get a friendly experience for typing and printing *)

    (* Meanwhile, the equality of the result with Q type also satisfy canonical form,
       that means we can use Leibniz equal instad of setoid equal `Qeq` *)
    Goal minvListQ 3 d1 = d2.
    Proof. cbv. auto. Qed.
  End ex2.

  (* Example 3: another matrix *)
  Section ex3.
    (* A manually given random matrix *)
    Let d1 :=
          [[1;2;3;4;5;6;7;8];
           [2;4;5;6;7;8;9;1];
           [3;5;7;6;8;4;2;1];
           [4;5;7;6;9;8;3;2];
           [5;4;3;7;9;6;8;1];
           [6;5;3;4;7;8;9;2];
           [7;8;6;5;9;2;1;3];
           [8;9;6;3;4;5;2;1]].
    (* Time Compute minvListQ 6 d1. (* 0.04 s *) *)
    (* Time Compute minvListQ 7 d1. (* 0.14 s *) *)
    (* Time Compute minvListQ 8 d1. (* 0.62 s *) *)
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
         in COQ,     M1(0,2)=41846/50943 = 0.8214278704
         in MATLAB,  M1(0,2)=23/28       = 0.8214285714
     *)

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

  (* Example 4 : a `8x8` matrix with decimal numbers *)
  Section ex4.
  (* In MATLAB, 
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

    (* Time Compute minvtblebListQ 8 d1. (* 0.15s *) *)
    (* Time Compute minvListQ 5 d1. (* 0.34 *) *)
    (* Time Compute minvListQ 6 d1. (* 1.28 *) *)
    (* Time Compute minvListQ 7 d1. (* 4.8 *) *)
    (* Time Compute minvListQ 8 d1. (* 20.5 *) *)
  End ex4.
  
  (* In summary, for computing inverse matrices with listQ:
     1. simple input format, and relatively simple output format.
     2. more accuately result compared to MATLAB, but fractions are not intuitive.
     3. Leibniz equal is supported.
   *)
End test_Qc.
