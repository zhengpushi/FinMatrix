(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Block matrix
  author    : Zhengpu Shi
  date      : 2024.06

  remark    :
  1. a basic block matrix is composed with 4 small matrices: lu, lb, ru, rb.
     Here, {r: left, r:right, u:upper, b:bottom}
 *)


Require Export Matrix.

Generalizable Variable tA Aadd Azero Aopp Amul Aone Ainv.



(* ######################################################################### *)
(** * Block matrix *)
Section block_matrix.
  Context {tA : Type} (Azero : tA).
  Notation mat r c := (mat tA r c).
  Notation "0" := Azero : A_scope.
  Notation m2f := (m2f 0).

  (* ======================================================================= *)
  (** ** Conversion between block matrix and matrix *)

  (** Get left upper matrix of matrix A *)
  Definition bmlu {r1 r2 c1 c2} (A : mat (r1 + r2) (c1 + c2)) : mat r1 c1 :=
    fun i j => A (fAddRangeR i) (fAddRangeR j).

  Lemma bmlu_spec : forall r1 r2 c1 c2 (A : mat (r1 + r2) (c1 + c2)) (i j : nat),
      i < r1 -> j < c1 -> m2f (bmlu A) i j = m2f A i j.
  Proof.
    intros. unfold bmlu. erewrite !nth_m2f. f_equal; fin. Unshelve. all: fin.
  Qed.

  (** Get right upper matrix of matrix A *)
  Definition bmru {r1 r2 c1 c2} (A : mat (r1 + r2) (c1 + c2)) : mat r1 c2 :=
    fun i j => A (fAddRangeR i) (fAddRangeAddL j).

  Lemma bmru_spec : forall r1 r2 c1 c2 (A : mat (r1 + r2) (c1 + c2)) (i j : nat),
      i < r1 -> j < c2 -> m2f (bmru A) i j = m2f A i (c1 + j).
  Proof.
    intros. unfold bmru. erewrite !nth_m2f. f_equal; fin. Unshelve. all: fin.
  Qed.

  (** Get left bottom matrix of matrix A *)
  Definition bmlb {r1 r2 c1 c2} (A : mat (r1 + r2) (c1 + c2)) : mat r2 c1 :=
    fun i j => A (fAddRangeAddL i) (fAddRangeR j).

  Lemma bmlb_spec : forall r1 r2 c1 c2 (A : mat (r1 + r2) (c1 + c2)) (i j : nat),
      i < r2 -> j < c1 -> m2f (bmlb A) i j = m2f A (r1 + i) j.
  Proof.
    intros. unfold bmlb. erewrite !nth_m2f. f_equal; fin. Unshelve. all: fin.
  Qed.

  (** Get right bottom matrix of matrix A *)
  Definition bmrb {r1 r2 c1 c2} (A : mat (r1 + r2) (c1 + c2)) : mat r2 c2 :=
    fun i j => A (fAddRangeAddL i) (fAddRangeAddL j).

  Lemma bmrb_spec : forall r1 r2 c1 c2 (A : mat (r1 + r2) (c1 + c2)) (i j : nat),
      i < r2 -> j < c2 -> m2f (bmrb A) i j = m2f A (r1 + i) (c1 + j).
  Proof.
    intros. unfold bmrb. erewrite !nth_m2f. f_equal; fin. Unshelve. all: fin.
  Qed.

  (** Make a block matrix from four matrices *)
  Definition bmmake {r1 r2 c1 c2} (lu : mat r1 c1) (ru : mat r1 c2)
    (lb : mat r2 c1) (rb : mat r2 c2) : mat (r1 + r2) (c1 + c2).
  Proof.
    intros i j. destruct (i ??< r1) as [Hi|Hi], (j ??< c1) as [Hj|Hj].
    - refine (lu (fAddRangeR' i Hi) (fAddRangeR' j Hj)).
    - refine (ru (fAddRangeR' i Hi) (fAddRangeAddL' j _)).
      apply Nat.nlt_ge; auto.
    - refine (lb (fAddRangeAddL' i _) (fAddRangeR' j Hj)).
      apply Nat.nlt_ge; auto.
    - refine (rb (fAddRangeAddL' i _) (fAddRangeAddL' j _)).
      all: apply Nat.nlt_ge; auto.
  Defined.

  Lemma bmmake_spec_lu : forall r1 r2 c1 c2 (lu : mat r1 c1) (ru : mat r1 c2)
                           (lb : mat r2 c1) (rb : mat r2 c2) (i j : nat),
      i < r1 -> j < c1 -> m2f (bmmake lu ru lb rb) i j = m2f lu i j.
  Proof.
    intros. erewrite !nth_m2f. unfold bmmake. fin. f_equal; fin. Unshelve. all: fin.
  Qed.

  Lemma bmmake_spec_ru : forall r1 r2 c1 c2 (lu : mat r1 c1) (ru : mat r1 c2)
                           (lb : mat r2 c1) (rb : mat r2 c2) (i j : nat),
      i < r1 -> j < c2 -> m2f (bmmake lu ru lb rb) i (c1 + j) = m2f ru i j.
  Proof.
    intros. erewrite !nth_m2f. unfold bmmake. fin.
    exfalso; fin. f_equal; fin. Unshelve. all: fin.
  Qed.

  Lemma bmmake_spec_lb : forall r1 r2 c1 c2 (lu : mat r1 c1) (ru : mat r1 c2)
                           (lb : mat r2 c1) (rb : mat r2 c2) (i j : nat),
      i < r2 -> j < c1 -> m2f (bmmake lu ru lb rb) (r1 + i) j = m2f lb i j.
  Proof.
    intros. erewrite !nth_m2f. unfold bmmake. fin.
    exfalso; fin. f_equal; fin. Unshelve. all: fin.
  Qed.

  Lemma bmmake_spec_rb : forall r1 r2 c1 c2 (lu : mat r1 c1) (ru : mat r1 c2)
                           (lb : mat r2 c1) (rb : mat r2 c2) (i j : nat),
      i < r2 -> j < c2 -> m2f (bmmake lu ru lb rb) (r1 + i) (c1 + j) = m2f rb i j.
  Proof.
    intros. erewrite !nth_m2f. unfold bmmake. fin.
    exfalso; fin. exfalso; fin. exfalso; fin. f_equal; fin. Unshelve. all: fin.
  Qed.

  Lemma bmlu_bmmake :
    forall r1 r2 c1 c2 (lu : mat r1 c1) (ru : mat r1 c2) (lb : mat r2 c1) (rb : mat r2 c2),
      bmlu (bmmake lu ru lb rb) = lu.
  Proof.
    intros. apply meq_iff_mnth; intros.
    pose proof (fin2nat_lt i). pose proof (fin2nat_lt j). unfold bmlu, bmmake. fin.
  Qed.

  Lemma bmru_bmmake :
    forall r1 r2 c1 c2 (lu : mat r1 c1) (ru : mat r1 c2) (lb : mat r2 c1) (rb : mat r2 c2),
      bmru (bmmake lu ru lb rb) = ru.
  Proof.
    intros. apply meq_iff_mnth; intros.
    pose proof (fin2nat_lt i). pose proof (fin2nat_lt j). unfold bmru, bmmake. fin.
    exfalso; fin.
  Qed.

  Lemma bmlb_bmmake :
    forall r1 r2 c1 c2 (lu : mat r1 c1) (ru : mat r1 c2) (lb : mat r2 c1) (rb : mat r2 c2),
      bmlb (bmmake lu ru lb rb) = lb.
  Proof.
    intros. apply meq_iff_mnth; intros.
    pose proof (fin2nat_lt i). pose proof (fin2nat_lt j). unfold bmlb, bmmake. fin.
    exfalso; fin.
  Qed.

  Lemma bmrb_bmmake :
    forall r1 r2 c1 c2 (lu : mat r1 c1) (ru : mat r1 c2) (lb : mat r2 c1) (rb : mat r2 c2),
      bmrb (bmmake lu ru lb rb) = rb.
  Proof.
    intros. apply meq_iff_mnth; intros.
    pose proof (fin2nat_lt i). pose proof (fin2nat_lt j). unfold bmrb, bmmake. fin.
    all: exfalso; fin.
  Qed.

  Lemma bmmake_lu_ru_lb_rb : forall r1 r2 c1 c2 (A : mat (r1 + r2) (c1 + c2)),
      bmmake (bmlu A) (bmru A) (bmlb A) (bmrb A) = A.
  Proof.
    intros. apply meq_iff_mnth; intros. unfold bmmake, bmlu, bmru, bmlb, bmrb. fin.
  Qed.

  (* ======================================================================= *)
  (** ** Algebraic operations of block matrices *)
  
  Context `{HSRing : SRing tA Aadd 0}.
  (* Add Ring ring_inst : (make_ring_theory HARing). *)
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.

  Notation madd := (@madd _ Aadd _ _).
  Notation mmul := (@mmul _ Aadd 0 Amul _ _ _).
  Notation mscal := (@mscal _ Amul _ _).
  Infix "+" := madd : mat_scope.
  Infix "*" := mmul : mat_scope.
  Infix "s*" := mscal : mat_scope.

  (** block matrix transpose *)
  Definition bmtrans {r1 r2 c1 c2} (A : mat (r1 + r2) (c1 + c2))
    : mat (c1 + c2) (r1 + r2) :=
    bmmake
      ((bmlu A)\T)
      ((bmlb A)\T)
      ((bmru A)\T)
      ((bmrb A)\T).

  Lemma bmtrans_eq : forall r1 r2 c1 c2 (A : mat (r1 + r2) (c1 + c2)),
      bmtrans A = A\T.
  Proof.
    intros. apply meq_iff_mnth; intros. unfold mtrans, bmtrans, bmmake.
    unfold bmlu, bmru, bmlb, bmrb. fin; auto_vec; f_equal; fin.
  Qed.

  (** block matrix scalar multiplication *)
  Definition bmscal {r1 r2 c1 c2} (c : tA) (A : mat (r1 + r2) (c1 + c2))
    : mat (r1 + r2) (c1 + c2) :=
    bmmake
      (c s* (bmlu A))
      (c s* (bmru A))
      (c s* (bmlb A))
      (c s* (bmrb A)).

  Lemma bmscal_eq : forall r1 r2 c1 c2 (c : tA) (A : mat (r1 + r2) (c1 + c2)),
      bmscal c A = c s* A.
  Proof.
    intros. apply meq_iff_mnth; intros. unfold mscal, bmscal, bmmake.
    unfold bmlu, bmru, bmlb, bmrb.
    fin; auto_vec; try rewrite mnth_mscal; f_equal; f_equal; fin.
  Qed.

  (** block matrix addition *)
  Definition bmadd {r1 r2 c1 c2} (A B : mat (r1 + r2) (c1 + c2))
    : mat (r1 + r2) (c1 + c2) :=
    bmmake
      (bmlu A + bmlu B)
      (bmru A + bmru B)
      (bmlb A + bmlb B)
      (bmrb A + bmrb B).

  Lemma bmadd_eq : forall r1 r2 c1 c2 (A B : mat (r1 + r2) (c1 + c2)),
      bmadd A B = A + B.
  Proof.
    intros. apply meq_iff_mnth; intros. unfold madd, bmadd, bmmake.
    unfold bmlu, bmru, bmlb, bmrb.
    fin; auto_vec; try rewrite mnth_madd; f_equal; f_equal; fin.
  Qed.

  (** block matrix multiplication *)
  Definition bmmul {r1 r2 c1 c2 s1 s2} (A : mat (r1 + r2) (c1 + c2))
    (B : mat (c1 + c2) (s1 + s2)) : mat (r1 + r2) (s1 + s2) :=
    bmmake
      (bmlu A * bmlu B + bmru A * bmlb B)
      (bmlu A * bmru B + bmru A * bmrb B)
      (bmlb A * bmlu B + bmrb A * bmlb B)
      (bmlb A * bmru B + bmrb A * bmrb B).

  Lemma bmlu_mmul :
    forall r1 r2 c1 c2 s1 s2 (A : mat (r1 + r2) (c1 + c2)) (B : mat (c1 + c2) (s1 + s2)),
      bmlu (A * B) = bmlu A * bmlu B + bmru A * bmlb B.
  Proof.
    intros. apply meq_iff_mnth; intros. unfold bmlu, bmru, bmlb, bmrb.
    rewrite mnth_madd. rewrite !mnth_mmul. rewrite vdot_vheadN_vtailN. f_equal.
  Qed.

  Lemma bmru_mmul :
    forall r1 r2 c1 c2 s1 s2 (A : mat (r1 + r2) (c1 + c2)) (B : mat (c1 + c2) (s1 + s2)),
      bmru (A * B) = bmlu A * bmru B + bmru A * bmrb B.
  Proof.
    intros. apply meq_iff_mnth; intros. unfold bmlu, bmru, bmlb, bmrb.
    rewrite mnth_madd. rewrite !mnth_mmul. rewrite vdot_vheadN_vtailN. f_equal.
  Qed.

  Lemma bmlb_mmul :
    forall r1 r2 c1 c2 s1 s2 (A : mat (r1 + r2) (c1 + c2)) (B : mat (c1 + c2) (s1 + s2)),
      bmlb (A * B) = bmlb A * bmlu B + bmrb A * bmlb B.
  Proof.
    intros. apply meq_iff_mnth; intros. unfold bmlu, bmru, bmlb, bmrb.
    rewrite mnth_madd. rewrite !mnth_mmul. rewrite vdot_vheadN_vtailN. f_equal.
  Qed.

  Lemma bmrb_mmul :
    forall r1 r2 c1 c2 s1 s2 (A : mat (r1 + r2) (c1 + c2)) (B : mat (c1 + c2) (s1 + s2)),
      bmrb (A * B) = bmlb A * bmru B + bmrb A * bmrb B.
  Proof.
    intros. apply meq_iff_mnth; intros. unfold bmlu, bmru, bmlb, bmrb.
    rewrite mnth_madd. rewrite !mnth_mmul. rewrite vdot_vheadN_vtailN. f_equal.
  Qed.

  Lemma bmmul_eq :
    forall r1 r2 c1 c2 s1 s2 (A : mat (r1 + r2) (c1 + c2)) (B : mat (c1 + c2) (s1 + s2)),
      bmmul A B = mmul A B.
  Proof.
    intros. unfold bmmul. symmetry. rewrite <- bmmake_lu_ru_lb_rb at 1. f_equal.
    rewrite bmlu_mmul; auto.
    rewrite bmru_mmul; auto.
    rewrite bmlb_mmul; auto.
    rewrite bmrb_mmul; auto.
  Qed.

End block_matrix.

Section test.

  Notation mmul := (@mmul _ plus 0 mult _ _ _).
  Notation bmmul := (@bmmul _ 0 plus mult _ _ _ _ _ _).

  (* [ 1  2  3 |  7  8]
     [ 4  5  6 |  9 10]
     ---------- ------
     [11 12 13 | 20 21] 
     [14 15 16 | 22 23]
     [17 18 19 | 24 25] *)
  Let lu1 : mat nat 2 3 := l2m 0 [[1;2;3];[4;5;6]].
  Let ru1 : mat nat 2 2 := l2m 0 [[7;8];[9;10]].
  Let lb1 : mat nat 3 3 := l2m 0 [[11;12;13];[14;15;16];[17;18;19]].
  Let rb1 : mat nat 3 2 := l2m 0 [[20;21];[22;23];[24;25]].

  Let A1 : mat nat (2+3) (3+2) := bmmake lu1 ru1 lb1 rb1.
  Let Alu1 := bmlu A1.
  Let Aru1 := bmru A1.
  Let Alb1 := bmlb A1.
  Let Arb1 := bmrb A1.

  (* Compute m2l A1. *)
  (* Compute m2l Alu1. *)
  
  Goal lu1 = Alu1. meq. Qed.
  Goal ru1 = Aru1. meq. Qed.
  Goal lb1 = Alb1. meq. Qed.
  Goal rb1 = Arb1. meq. Qed.


  (* [ 1  2  3 | 10 11]
     [ 4  5  6 | 12 13]
     [ 7  8  9 | 14 15] 
     ---------- ------
     [16 17 18 | 22 23]
     [19 20 21 | 24 25] *)
  Let lu2 : mat nat 3 3 := l2m 0 [[1;2;3];[4;5;6];[7;8;9]].
  Let ru2 : mat nat 3 2 := l2m 0 [[10;11];[12;13];[14;15]].
  Let lb2 : mat nat 2 3 := l2m 0 [[16;17;18];[19;20;21]].
  Let rb2 : mat nat 2 2 := l2m 0 [[22;23];[24;25]].

  Let A2 : mat nat (3+2) (3+2) := bmmake lu2 ru2 lb2 rb2.
  Let Alu2 := bmlu A2.
  Let Aru2 := bmru A2.
  Let Alb2 := bmlb A2.
  Let Arb2 := bmrb A2.

  (* Compute m2l A2. *)
  (* Compute m2l Alu2. *)
  
  Goal lu2 = Alu2. meq. Qed.
  Goal ru2 = Aru2. meq. Qed.
  Goal lb2 = Alb2. meq. Qed.
  Goal rb2 = Arb2. meq. Qed.

  (* Compute m2l (mmul A1 A2). *)
  (* Compute m2l (bmmul A1 A2). *)

  (* proof the equality of specific matrices by calculation *)
  Goal mmul A1 A2 = bmmul A1 A2.
  Proof. meq. Qed.

  (* proof the equality by derivation *)
  Goal mmul A1 A2 = bmmul A1 A2.
  Proof. erewrite bmmul_eq; auto. auto with nat. Qed.

End test.


(* ######################################################################### *)
(** * Block matrix with special cases *)
Section block_matrix_special.
  Context {tA : Type} (Azero : tA).
  Notation mat r c := (mat tA r c).
  Notation "0" := Azero : A_scope.

  (** [a11 a12 | v1]
      [a21 a22 | v2]
       ------- | -- 
      [ u1  u2 |  x] *)
  Lemma mconscT_mconsrT_vconsT_eq_bmmake :
    forall r c (A : mat r c) (u : @vec tA c) (v : @vec tA r) (x : tA),
      mconscT (mconsrT A u) (vconsT v x) =
        mcastAdd2S (bmmake A (v2cv v) (v2rv u) (l2m 0 [[x]])).
  Proof.
    intros. apply meq_iff_mnth; intros.
  Abort.

End block_matrix_special.

