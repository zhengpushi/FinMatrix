(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Gauss elimination of matrix
  author    : ZhengPu Shi
  date      : 2023.12

  remark    :
  1. Two stages
     First stage, we use a simple case of `n × n` matrix
     Second stage, we should consider the case of `m × n` matrix

  2. learn "fold_left" and "fold_right"

     fold_left  f [b1;b2;b3] a = f (f (f a b1) b2) b3
     Folding start from newest added element.

     fold_right f a [b1;b2;b3] = f b1 (f b2 (f b3 a))
     Folding start from oldest added element.
 *)

Require Import NatExt.
Require Import Hierarchy.
Require Import Matrix.
Require Import MyExtrOCamlR.
Require QcExt RExt.

Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv.

(** fold_left f (map g l) a = fold_left (fun x y => f x (g y)) l a *)
Lemma fold_left_map : forall {A B} (l : list B) (f : A -> A -> A) (g : B -> A) a,
    fold_left f (map g l) a = fold_left (fun x y => f x (g y)) l a.
Proof.
  intros A B l. induction l; intros; simpl. auto.
  rewrite IHl. auto.
Qed.

(** fold_right f a (map g l) = fold_right (fun x y => f (g x) y) a l *)
Lemma fold_right_map : forall {A B} (l : list B) (f : A -> A -> A) (g : B -> A) a,
    fold_right f a (map g l) = fold_right (fun x y => f (g x) y) a l.
Proof.
  intros A B l. induction l; intros; simpl. auto.
  rewrite IHl. auto.
Qed.


(* ############################################################################ *)
(** * Gauss elimination. *)
Section GaussElim.
  Context `{HField : Field} `{HAeqDec : Dec _ (@eq A)}.
  Add Field field_inst : (make_field_theory HField).

  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Infix "/" := (fun a b => a * / b) : A_scope.
  Notation Aeqb := (@Acmpb _ (@eq A) _).
  
  Notation mat r c := (mat A r c).
  Notation smat n := (smat A n).
  Notation mat1 := (@mat1 _ Azero Aone).
  Notation madd := (@madd _ Aadd).
  Infix "+" := madd : mat_scope.
  Notation mmul := (@mmul _ Aadd Azero Amul).
  Infix "*" := mmul : mat_scope.
  Notation mrowSwap := (@mrowSwap A).
  Notation mrowScale := (@mrowScale _ Amul).
  Notation mrowAdd := (@mrowAdd _ Aadd Amul).
  Notation mrowSwapM := (@mrowSwapM _ 0 1 _).
  Notation mrowScaleM := (@mrowScaleM _ 0 1 _).
  Notation mrowAddM := (@mrowAddM _ Aadd 0 1 _).
  Notation mrow := (@mrow _ Azero).


  (* ======================================================================= *)
  (** ** 行变换 *)
  
  (* 为避免逆矩阵计算时的大量计算，使用抽象表示，可提高计算效率 *)
  Inductive RowOp {n} :=
  | ROnop
  | ROswap (i j : 'I_(S n))
  | ROscale (i : 'I_(S n)) (c : A)
  | ROadd (i j : 'I_(S n)) (c : A).

  (** 行变换列表转换为矩阵 *)
  Definition rowOps2mat {n} (l : list (@RowOp n)) : smat (S n) :=
    fold_right (fun op M =>
                  match op with
                  | ROnop => M
                  | ROswap i j => mrowSwap i j M
                  | ROscale i c => mrowScale i c M
                  | ROadd i j c => mrowAdd i j c M
                  end) mat1 l.

  (** rowOps2mat (l1 ++ l2) = rowOps2mat l1 * rowOps2mat l2 *)
  Theorem rowOps2mat_app : forall {n} (l1 l2 : list (@RowOp n)),
      rowOps2mat (l1 ++ l2) = rowOps2mat l1 * rowOps2mat l2.
  Proof.
    intros. induction l1; intros; simpl.
    - rewrite mmul_1_l; auto.
    - destruct a; auto.
      + rewrite IHl1. rewrite mrowSwap_mmul; auto.
      + rewrite IHl1. rewrite mrowScale_mmul; auto.
      + rewrite IHl1. rewrite mrowAdd_mmul; auto.
  Qed.


  (* ======================================================================= *)
  (** ** 行变换的逆过程 *)

  (** 行变换列表转换为反作用的矩阵。即，rowOps2mat的逆矩阵 *)
  Definition rowOps2matInv {n} (l : list (@RowOp n)) : smat (S n) :=
    fold_left (fun M op =>
                 match op with
                 | ROnop => M
                 | ROswap i j => mrowSwap i j M
                 | ROscale i c => mrowScale i (/c) M
                 | ROadd i j c => mrowAdd i j (-c) M
                 end) l mat1.

  (* 为证明 rowOps2matInv_app，引入辅助定义和引理，主要思想是：
     将 rowOps2mat 和 rowOps2matInv 转换为矩阵乘法 *)
  Section helper.
    
    (* Valid RowOp *)
    Definition roValid {n} (op : @RowOp n) : Prop :=
      match op with
      | ROnop => True
      | ROswap i j => True
      | ROscale i c => c <> 0
      | ROadd i j c => i <> j
      end.

    (* op => matrix of op *)
    Definition ro2mat {n} (op : @RowOp n) : smat (S n) :=
      match op with
      | ROnop => mat1
      | ROswap i j => mrowSwapM i j
      | ROscale i c => mrowScaleM i c
      | ROadd i j c => mrowAddM i j c
      end.

    (* op => matrix of inverse opeation *)
    Definition ro2matInv {n} (op : @RowOp n) : smat (S n) :=
      match op with
      | ROnop => mat1
      | ROswap i j => mrowSwapM i j
      | ROscale i c => mrowScaleM i (/c)
      | ROadd i j c => mrowAddM i j (-c)
      end.

    Lemma mmul_ro2mat_l : forall n (op : RowOp) (M : smat (S n)),
        ro2mat op * M =
          match op with
          | ROnop => M
          | ROswap i j => mrowSwap i j M
          | ROscale i c => mrowScale i c M
          | ROadd i j c => mrowAdd i j c M
          end.
    Proof.
      intros. unfold ro2mat. destruct op.
      - apply mmul_1_l.
      - rewrite mrowSwap_eq; auto.
      - rewrite mrowScale_eq; auto.
      - rewrite mrowAdd_eq; auto.
    Qed.

    Lemma mmul_ro2matInv_l : forall n (op : RowOp) (M : smat (S n)),
        ro2matInv op * M =
          match op with
          | ROnop => M
          | ROswap i j => mrowSwap i j M
          | ROscale i c => mrowScale i (/ c) M
          | ROadd i j c => mrowAdd i j (- c) M
          end.
    Proof.
      intros.  unfold ro2matInv. destruct op.
      - apply mmul_1_l.
      - rewrite mrowSwap_eq; auto.
      - rewrite mrowScale_eq; auto.
      - rewrite mrowAdd_eq; auto.
    Qed.
    
    Lemma mmul_ro2mat_ro2matInv : forall {n} (op : @RowOp n),
        roValid op -> ro2mat op * ro2matInv op = mat1.
    Proof.
      intros. hnf in H. destruct op; simpl.
      - rewrite mmul_1_l; auto.
      - rewrite mmul_mrowSwapM_mrowSwapM; auto.
      - rewrite mmul_mrowScaleM_mrowScaleM; auto.
      - rewrite mmul_mrowAddM_mrowAddM; auto.
    Qed.
    
    Lemma mmul_ro2matInv_ro2mat : forall {n} (op : @RowOp n),
        roValid op -> ro2matInv op * ro2mat op = mat1.
    Proof.
      intros. hnf in H. destruct op; simpl.
      - rewrite mmul_1_l; auto.
      - rewrite mmul_mrowSwapM_mrowSwapM; auto.
      - replace c with (/ / c) at 2.
        rewrite mmul_mrowScaleM_mrowScaleM; auto.
        apply field_inv_neq0_iff; auto.
        rewrite field_inv_inv; auto.
      - replace c with (- - c) at 2 by field.
        rewrite mmul_mrowAddM_mrowAddM; auto.
    Qed.

    (** rowOps2mat has an equivalent form with matrix multiplication. *)
    (*     Note that, we won't use this definition to improve performance *)
    Lemma rowOps2mat_eq : forall {n} (l : list (@RowOp n)),
        rowOps2mat l = fold_right mmul mat1 (map ro2mat l).
    Proof.
      intros. unfold rowOps2mat. rewrite fold_right_map. f_equal.
      extensionality M. extensionality op. rewrite mmul_ro2mat_l. auto.
    Qed.

    (** rowOps2matInv has an equivalent form with matrix multiplication. *)
    (*     Note that, we won't use this definition to improve performance *)
    Lemma rowOps2matInv_eq : forall {n} (l : list (@RowOp n)),
        rowOps2matInv l = fold_left (fun x y => y * x) (map ro2matInv l) mat1.
    Proof.
      intros. unfold rowOps2matInv. rewrite fold_left_map. f_equal.
      extensionality M. extensionality op. rewrite mmul_ro2matInv_l. auto.
    Qed.
  End helper.

  (** rowOps2matInv l * rowOps2mat l = mat1 *)
  Lemma mmul_rowOps2matInv_rowOps2mat_eq1 : forall {n} (l : list (@RowOp n)),
      Forall roValid l -> rowOps2matInv l * rowOps2mat l = mat1.
  Proof.
    intros.
    (* convert to mmul *)
    rewrite rowOps2mat_eq. rewrite rowOps2matInv_eq. rewrite <- fold_left_rev_right.
    (* If we assume l = a1;a2;a3, and denoted that
            map ro2matInv l       = a1';a2';a3'
            rev (map ro2matInv l) = a3';a2';a1'
            map ro2mat l          = a1;a2;a3,
       then the Goal is: (a3'*a2'*a1'*mat1) * (a1*a2*a3*mat1) = mat1 *)
    induction l; simpl. apply mmul_1_l.
    (* Convert 'ro2matInv a' to second items of matrix multiplication *)
    replace (fold_right mmul mat1 (rev (map ro2matInv l) ++ [ro2matInv a]))
      with ((fold_right mmul mat1 (rev (map ro2matInv l))) * (ro2matInv a)).
    2: {
      (* (a3'*a2'*a1'*mat1)*a' = (a3'*a2'*a1'*a')*mat1 *)
      remember (rev (map ro2matInv l)). remember (ro2matInv a).
      clear Heqv IHl Heql0.
      induction l0; simpl. rewrite mmul_1_l, mmul_1_r; auto.
      rewrite mmul_assoc. f_equal. rewrite IHl0. auto. }
    (* Now, eliminate the middle two items *)
    rewrite mmul_assoc. rewrite <- (mmul_assoc (ro2matInv a)).
    rewrite mmul_ro2matInv_ro2mat. rewrite mmul_1_l. apply IHl.
    inversion H; auto. inversion H; auto.
  Qed.

  (** rowOps2mat l * rowOps2matInv l = mat1 *)
  Lemma mmul_rowOps2mat_rowOps2matInv_eq1 : forall {n} (l : list (@RowOp n)),
      Forall roValid l -> rowOps2mat l * rowOps2matInv l = mat1.
  Proof.
    intros.
    (* convert to mmul *)
    rewrite rowOps2mat_eq. rewrite rowOps2matInv_eq. rewrite <- fold_left_rev_right.
    (* If we assume l = a1;a2;a3, and denoted that
            map ro2matInv l       = a1';a2';a3'
            rev (map ro2matInv l) = a3';a2';a1'
            map ro2mat l          = a1;a2;a3,
       then the Goal is: (a1*a2*a3*mat1) (a3'*a2'*a1'*mat1) = mat1 *)
    induction l; simpl. apply mmul_1_l.
    (* Convert 'ro2matInv a' to last items of matrix multiplication *)
    replace (fold_right mmul mat1 (rev (map ro2matInv l) ++ [ro2matInv a]))
      with ((fold_right mmul mat1 (rev (map ro2matInv l))) * (ro2matInv a)).
    2: {
      (* (a3'*a2'*a1'*mat1)*a' = (a3'*a2'*a1'*a')*mat1 *)
      remember (rev (map ro2matInv l)). remember (ro2matInv a).
      clear Heqv IHl Heql0.
      induction l0; simpl. rewrite mmul_1_l, mmul_1_r; auto.
      rewrite mmul_assoc. f_equal. rewrite IHl0. auto. }
    (* Now, eliminate the middle two items *)
    rewrite <- !mmul_assoc. rewrite (mmul_assoc (ro2mat a)). rewrite IHl.
    rewrite mmul_1_r. rewrite mmul_ro2mat_ro2matInv. auto.
    inversion H; auto. inversion H; auto.
  Qed.

  (** rowOps2mat l * M = N -> rowOps2matInv l * N = M *)
  Lemma rowOps2mat_imply_rowOps2matInv : forall {n} (l : list RowOp) (M N : smat (S n)),
      Forall roValid l -> (rowOps2mat l) * M = N -> (rowOps2matInv l) * N = M.
  Proof.
    intros. rewrite <- H0. rewrite <- mmul_assoc.
    rewrite mmul_rowOps2matInv_rowOps2mat_eq1; auto. rewrite mmul_1_l. auto.
  Qed.

  (** rowOps2matInv l * M = N -> rowOps2mat l * N = M *)
  Lemma rowOps2matInv_imply_rowOps2mat : forall {n} (l : list RowOp) (M N : smat (S n)),
      Forall roValid l -> (rowOps2matInv l) * M = N -> (rowOps2mat l) * N = M.
  Proof.
    intros. rewrite <- H0. rewrite <- mmul_assoc.
    rewrite mmul_rowOps2mat_rowOps2matInv_eq1; auto. rewrite mmul_1_l. auto.
  Qed.

  (** (l1 * l2 * ... * ln * 1) * a = l1 * l2 * ... * ln * (a * 1) *)
  Lemma fold_right_mmul_rebase : forall {n} (l : list (smat n)) (a : smat n),
      fold_right mmul mat1 l * a = fold_right mmul a l.
  Proof.
    intros n. induction l; intros; simpl. rewrite mmul_1_l; auto.
    rewrite mmul_assoc. rewrite IHl. auto.
  Qed.

  (** rowOps2matInv (l1 ++ l2) = rowOps2matInv l2 * rowOps2matInv l1 *)
  Theorem rowOps2matInv_app : forall {n} (l1 l2 : list (@RowOp n)),
      rowOps2matInv (l1 ++ l2) = rowOps2matInv l2 * rowOps2matInv l1.
  Proof.
    intros n. unfold rowOps2matInv.
    remember (fun (M : smat (S n)) (op : RowOp) =>
                match op with
                | ROnop => M
                | ROswap i j => mrowSwap i j M
                | ROscale i c => mrowScale i (/ c) M
                | ROadd i j c => mrowAdd i j (- c) M
                end) as f.
    (* by induction on l2 is easier *)
    intros l1 l2. revert l1. induction l2.
    - intros. simpl. rewrite app_nil_r. rewrite mmul_1_l; auto.
    - intros. simpl.
      replace (l1 ++ a :: l2)%list with ((l1 ++ [a]) ++ l2)%list;
        [|rewrite <- app_assoc; auto].
      rewrite IHl2. rewrite fold_left_app; simpl.
      (* Assume: l1 = [b1;b2], l2 = [c1;c2], then
         l1++l2 = [b1;b2;c1;c2]
         f mat1 a                        = Ta*1
         fold_left f l2 mat1             = Tc2*Tc1*1
         fold_left f l2 (f mat1 a)       = Tc2*Tc1*Ta*1
         fold_left f l1 mat1             = Tb2*Tb1*1
         f (fold_left f l1 mat1) a       = Ta*Tb2*Tb1*1
      The goal is:
         (Tc2*Tc1*1)*(Ta*Tb2*Tb1*1) = (Tc2*Tc1*Ta*1)*(Tb2*Tb1*1) *)
      replace (f (fold_left f l1 mat1) a)
        with (ro2matInv a * (fold_left f l1 mat1)).
      2:{ rewrite mmul_ro2matInv_l. rewrite Heqf; auto. }
      replace (fold_left f l2 (f mat1 a))
        with ((fold_left f l2 mat1) * ro2matInv a).
      2:{
        (* a difficulty proof *)
        clear IHl2. rename l2 into l. clear l1.
        assert (f = fun (M : smat (S n)) op => ro2matInv op * M).
        { rewrite Heqf. unfold ro2matInv.
          extensionality M. extensionality op. destruct op.
          rewrite mmul_1_l; auto.
          rewrite mrowSwap_eq; auto.
          rewrite mrowScale_eq; auto.
          rewrite mrowAdd_eq; auto. }
        (* op ==> 矩阵乘法 *)
        rewrite H.
        rewrite <- (fold_left_map l (fun x y => y * x) ro2matInv).
        rewrite <- (fold_left_map l (fun x y => y * x) ro2matInv).
        (* “交换的矩阵乘法” ==> 正常的矩阵转换 *)
        rewrite <- fold_left_rev_right.
        rewrite <- fold_left_rev_right.
        remember (rev (map ro2matInv l)) as L.
        rewrite mmul_1_r.
        remember (ro2matInv a) as b.
        (* (l1*l2*l3*1)*b = l1*l2*l3*(b*1) *)
        rewrite fold_right_mmul_rebase. auto. }
      rewrite mmul_assoc. auto.
  Qed.


  (* ======================================================================= *)
  (** ** 矩阵形状的谓词 *)

  (** 方阵 M 的前 x 列的左下角(不含对角线)是 0。当 x = n 时，整个矩阵左下角是 0 *)
  Definition mLeftLowerZeros {n} (M : smat n) (x : nat) : Prop :=
    forall (i j : 'I_n), j < x -> j < i -> M.[i].[j] = 0.

  Lemma mLeftLowerZeros_less : forall {n} (M : smat (S n)) (x : nat),
      mLeftLowerZeros M (S x) -> mLeftLowerZeros M x.
  Proof. intros. hnf in *; intros. rewrite H; auto. Qed.
  
  Lemma mLeftLowerZeros_S : forall {n} (M : smat (S n)) (x : nat),
      (forall (i : 'I_(S n)), x < i -> M i #x = 0) ->
      mLeftLowerZeros M x -> mLeftLowerZeros M (S x).
  Proof.
    intros. hnf in *; intros. destruct (x ??= j).
    - assert (j = #x). rewrite e. rewrite nat2finS_fin2nat; auto.
      rewrite H3. rewrite H; auto. lia.
    - rewrite H0; auto. lia.
  Qed.

  
  (** 方阵 M 是上三角矩阵（即，左下角都是0）  *)
  Definition mUpperTrig {n} (M : smat n) : Prop :=
    mLeftLowerZeros M n.
  
  Lemma mat1_mLeftLowerZeros : forall {n}, mLeftLowerZeros (@mat1 n) n.
  Proof.
    intros. hnf. intros. rewrite mnth_mat1_diff; auto.
    assert (fin2nat i <> j); try lia. fin.
  Qed.
  
  Lemma mat1_mUpperTrig : forall {n}, mUpperTrig (@mat1 n).
  Proof. intros. unfold mUpperTrig. apply mat1_mLeftLowerZeros. Qed.

  
  (** 方阵 M 的前 x 行/列的对角线都是 1。当 x=n 时，整个矩阵的对角线是 1 *)
  Definition mDiagonalOne {n} (M : smat n) (x : nat) : Prop :=
    forall (i : 'I_n), i < x -> M i i = 1.
  
  Lemma mat1_mDiagonalOne : forall {n}, mDiagonalOne (@mat1 n) n.
  Proof. intros. hnf; intros. rewrite mnth_mat1_same; auto. Qed.

  
  (** 方阵 M 的对角线都是 1 *)
  Definition mDiagonalOnes {n} (M : smat n) : Prop := mDiagonalOne M n.
  
  Lemma mat1_mDiagonalOnes : forall {n}, mDiagonalOnes (@mat1 n).
  Proof. intros. unfold mDiagonalOnes. apply mat1_mDiagonalOne. Qed.

  
  (** 方阵 M 是单位上三角矩阵（即，左下角全0 + 对角线全1）*)
  Definition mUnitUpperTrig {n} (M : smat n) := 
    mUpperTrig M /\ mDiagonalOnes M.

  (** 单位上三角矩阵，任意下面的行的倍数加到上面，仍然是单位上三角矩阵 *)
  Lemma mrowAdd_mUnitUpperTrig : forall {n} (M : smat (S n)) (i j : 'I_(S n)),
      mUnitUpperTrig M ->
      i < j ->
      mUnitUpperTrig (mrowAdd i j (- (M i j))%A M).
  Proof.
    intros. unfold mUnitUpperTrig in *. destruct H. split; hnf in *; intros.
    - unfold mrowAdd; fin. subst.
      rewrite !(H _ j0); auto. ring.
      pose proof (fin2nat_lt j). lia.
    - unfold mrowAdd; fin. fin2nat.
      rewrite H1; auto; fin. rewrite (H _ i); auto. ring.
  Qed.
  
  
  (** 方阵 M 的后 x 列的右上角（不含对角线）全是 0。
      当 x = n 时，整个矩阵右上角是 0 *)
  Definition mRightUpperZeros {n} (M : smat n) (x : nat) : Prop :=
    forall (i j : 'I_n), n - x <= j -> i < j -> M i j = 0.
  
  Lemma mat1_mRightUpperZeros : forall {n}, mRightUpperZeros (@mat1 n) n.
  Proof.
    intros. hnf. intros. rewrite mnth_mat1_diff; auto.
    assert (fin2nat i <> j); try lia. fin.
  Qed.
  

  (* ======================================================================= *)
  (** ** 某列的第一个非零元的行号 *)

  (** 第 j 列的后 x 个元素中的第 1 个非零元的行号。
      eg: 当 x 是`维数` 时，则从第 0 行开始往下查找。 *)
  Fixpoint getPivot {n} (M : smat (S n)) (x : nat) (j : 'I_(S n))
    : option ('I_(S n)) :=
    match x with
    | O => None
    | S x' =>
        (* x的递归顺序：   x,    x-1, ... ,    1, (0)
           S n-x的顺序：Sn-x, Sn-x+1, ... , Sn-1, (Sn) *)
        if Aeqdec (M #(S n - x) j) 0
        then getPivot M x' j
        else Some #(S n - x)
    end.

  Lemma getPivot_imply_nonzero :
    forall (x : nat) {n} (M : smat (S n)) (i j : 'I_(S n)),
      getPivot M x j = Some i -> M i j <> 0.
  Proof.
    induction x; intros.
    - simpl in H. easy.
    - simpl in H. destruct (Aeqdec (M #(n - x) j) 0).
      + apply IHx in H; auto.
      + inv H. auto.
  Qed.
  
  (* 非零元行号 r < S n *)
  Lemma getPivot_max : forall (x : nat) {n} (M : smat (S n)) (j r : 'I_(S n)),
      getPivot M x j = Some r -> r < S n.
  Proof.
    induction x; intros.
    - simpl in H. easy.
    - simpl in H. destruct Aeqdec as [E|E].
      + apply IHx in H. auto.
      + inversion H. rewrite fin2nat_nat2finS; lia.
  Qed.
  
  (* 非零元行号 r >= S n - x *)
  Lemma getPivot_min: forall (x : nat) {n} (M : smat (S n)) (j r : 'I_(S n)),
      getPivot M x j = Some r -> r >= S n - x.
  Proof.
    induction x; intros.
    - simpl in H. easy.
    - simpl in H. destruct Aeqdec as [E|E].
      + apply IHx in H. lia.
      + inversion H. rewrite fin2nat_nat2finS; lia.
  Qed.
  
  (* End GaussElim. *)
  (* Section test. *)
  (*   Let M : smat nat 3 := l2m 0 [[1;0;0];[0;1;0];[0;0;1]]. *)
  (*   Notation getPivot := (@getPivot nat 0). *)
  (*   Compute getPivot M 3 #0. *)
  (*   Compute getPivot M 3 #1. *)
  (*   Compute getPivot M 3 #2. *)
  (*   Compute getPivot M 2 #0. *)
  (*   Compute getPivot M 2 #1. *)
  (*   Compute getPivot M 2 #2. *)
  (*   Compute getPivot M 1 #0. *)
  (*   Compute getPivot M 1 #1. *)
  (*   Compute getPivot M 1 #2. *)
  (*   Compute getPivot M 0 #0. *)
  (*   Compute getPivot M 0 #1. *)
  (*   Compute getPivot M 0 #2. *)
  (* End test. *)


  (* ******************************************************************* *)
  (** ** 向下消元 *)
  
  (* 将矩阵M的第j列的后 x 行元素变为 0。当 j=#0时，x=n *)
  Fixpoint elimDown {n} (M : smat (S n)) (x : nat) (j : 'I_(S n))
    : list RowOp * smat (S n) :=
    match x with
    | O => ([], M)
    | S x' =>
        (* 递归时 x 从大到小，而 fx 是从小到大 *)
        let fx : 'I_(S n) := #(S n - x) in
        let a : A := M.[fx].[j] in
        (* 如果 M[S n-x,j] <> 0，则 j 行的 -M[S n-x,j] 倍加到 S n-x 行。要求 M[j,j]=1 *)
        if Aeqdec a 0
        then elimDown M x' j
        else
          let op1 := ROadd fx j (-a)%A in
          let M1 := mrowAdd fx j (-a)%A M in
          let (l2, M2) := elimDown M1 x' j in
          ((l2 ++ [op1])%list, M2)
    end.
  
  (** 对 M 向下消元得到 (l, M')，则 l 都是有效的 *)
  Lemma elimDown_rowOpValid :
    forall (x : nat) {n} (M M' : smat (S n)) (j : 'I_(S n)) (l : list RowOp),
      x < S n - j -> elimDown M x j = (l, M') -> Forall roValid l.
  Proof.
    induction x; intros; simpl in *.
    - inversion H0. constructor.
    - (* 当前元素是否为0，若是则直接递归，若不是则消元后递归 *)
      destruct (Aeqdec (M #(n - x) j) 0) as [E|E].
      + apply IHx in H0; auto. lia.
      + destruct elimDown as [l2 M2] eqn: T2.
        apply IHx in T2; try lia. inversion H0.
        apply Forall_app. split; auto. repeat constructor. hnf. intro.
        destruct j.
        assert (n - x = i).
        { erewrite nat2finS_eq in H1. apply fin_eq_iff in H1. auto. }
        fin. subst. destruct (n - x) eqn:H2. fin. fin.
        Unshelve. fin.
  Qed.

  (** 对 M 向下消元得到 (l, M')，则 [l] * M = M' *)
  Lemma elimDown_eq :
    forall (x : nat) {n} (M M' : smat (S n)) (j : 'I_(S n)) (l : list RowOp),
      elimDown M x j = (l, M') -> rowOps2mat l * M = M'.
  Proof.
    induction x; intros; simpl in *.
    - inversion H. simpl. apply mmul_1_l.
    - (* 当前元素是否为0，若是则直接递归，若不是则消元后递归 *)
      destruct (Aeqdec (M #(n - x) j) 0) as [E|E].
      + apply IHx in H; auto.
      + destruct elimDown as [l2 M2] eqn: T2.
        apply IHx in T2. inversion H. rewrite <- H2, <- T2.
        rewrite rowOps2mat_app. simpl.
        rewrite !mmul_assoc. f_equal.
        rewrite <- mrowAdd_mmul. rewrite mmul_1_l. auto.
  Qed.

  (* 若M[y,y]=1，则对第y列的 后 x 行向下消元后，前S n - x行的所有元素保持不变 *)
  Lemma elimDown_keep_former_row :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp) (y : 'I_(S n)),
      elimDown M x y = (l, M') ->
      M y y = 1 ->
      x < S n - y ->
      (forall i j : 'I_(S n), i < S n - x -> M' i j = M i j).
  Proof.
    induction x; intros.
    - simpl in H. inv H. auto.
    - simpl in H.
      destruct Aeqdec as [E|E].
      + apply IHx with (i:=i)(j:=j) in H; auto; try lia.
      + destruct elimDown as [l2 M2] eqn: T2.
        inversion H. rewrite <- H5. apply IHx with (i:=i)(j:=j) in T2; try lia.
        * rewrite T2. unfold mrowAdd; fin.
        * unfold mrowAdd; fin.
  Qed.
  
  (* 若M[y,y]=1，则对第y列的 后 x 行向下消元后，第 y 列的后x行的所有元素变成 0 *)
  Lemma elimDown_latter_row_0:
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp) (y : 'I_(S n)),
      elimDown M x y = (l, M') ->
      M y y = 1 ->
      x < S n - y ->
      (forall i : 'I_(S n), S n - x <= i -> M' i y = 0).
  Proof.
    induction x; intros.
    - pose proof (fin2nat_lt i). lia.
    - simpl in H.
      destruct (Aeqdec (M #(n - x) y) 0) as [E|E].
      + destruct (i ??= n - x) as [E1|E1].
        * apply elimDown_keep_former_row with (i:=i)(j:=y) in H; auto; try lia.
          subst. rewrite H. rewrite <- E1 in E. rewrite nat2finS_fin2nat in E; auto.
        * apply IHx with (i:=i) in H; auto; try lia.
      + destruct elimDown as [l2 M2] eqn: T2.
        inversion H. rewrite <- H5.
        replace (S n - S x) with (n - x) in H2 by lia.
        destruct (i ??= n - x) as [E1|E1].
        * apply elimDown_keep_former_row with (i:=i)(j:=y) in T2; auto; try lia.
          ** rewrite T2. unfold mrowAdd; fin. rewrite H0. rewrite <- E0. fin.
          ** unfold mrowAdd; fin.
        * apply IHx with (i:=i) in T2; auto; try lia. unfold mrowAdd; fin.
  Qed.

  (* 若 M 的前 y 列左下方都是0，则对后 x 行向下消元后，M' 的前 y 列左下方都是0 *)
  Lemma elimDown_mLowerLeftZeros_aux:
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp) (y : 'I_(S n)),
      elimDown M x y = (l, M') ->
      mLeftLowerZeros M (y) ->
      x < S n - y ->
      M y y = 1 ->
      mLeftLowerZeros M' (y).
  Proof.
    induction x; intros.
    - simpl in H. inv H. auto.
    - simpl in H.
      destruct (Aeqdec (M #(n - x) y) 0) as [E|E].
      + apply IHx in H; auto; try lia.
      + destruct elimDown as [l2 M2] eqn: T2.
        inversion H. rewrite <- H5.
        hnf; intros.
        destruct (x ??< S n - y) as [E1|E1].
        * apply IHx in T2; auto; try lia; clear IHx.
          ** hnf; intros. unfold mrowAdd; fin.
             rewrite !(H0 _ j0); auto. ring.
          ** unfold mrowAdd; fin.
        * apply elimDown_keep_former_row with (i:=i)(j:=j) in T2; auto; try lia.
  Qed.

  (** 若 M 前 x 列左下是0，则对 M 的后 S n - S x 列消元后的 M' 的前 S x 列左下是 0 *)
  Lemma elimDown_mLeftLowerZeros :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      elimDown M (S n - S x) #x = (l, M') ->
      x < S n ->
      M #x #x = 1 ->
      mLeftLowerZeros M x ->
      mLeftLowerZeros M' (S x).
  Proof.
    intros. hnf; intros.
    (* 两种情况：在 x 列，在 x 列左侧 *)
    destruct (j ??= x) as [E|E].
    - apply elimDown_latter_row_0 with (i:=i) in H; auto; subst; fin.
    - apply elimDown_mLowerLeftZeros_aux in H; auto; fin.
      rewrite H; auto.
      pose proof (fin2nat_lt j). lia.
  Qed.

  (* End GaussElim. *)
  (* Section test. *)
  (*   Import QcExt. *)
  (*   Notation elimDown := (@elimDown _ Qcplus 0 Qcopp Qcmult _). *)
  
  (*   (* 化阶梯形测试 *) *)
  (*   Let M : smat Qc 3 := l2m 0 (Q2Qc_dlist [[1;2;3];[4;5;6];[7;8;9]]%Q). *)
  (*   Compute m2l (snd (elimDown M 2 #0)). *)
  (* End test. *)


  (* ******************************************************************* *)
  (** ** 化为行阶梯形 *)

  (*            (x=3)        (x=4)
   * * * *    * * * *     1 * * *
   * * * *    * 1 * *     0 1 * *
   * * * * => * 0 1 *     0 0 1 *
   * * * *    * 0 0 1     0 0 0 1
     -----------------------------------
     递归时i    3 2 1 (0)   4 3 2 1 (0)
     递归时n-i  1 2 3       0 1 2 3
   *)
  (* 将矩阵M的后 x 行化为单位上三角形。
     参数 x 最大为维数，递归时 x 递减，而 (维数-x) 递增。*)
  Fixpoint rowEchelon {n} (M : smat (S n)) (x : nat)
    : option (list RowOp * smat (S n)) :=
    match x with
    | O => Some ([], M)
    | S x' =>
        let j : 'I_(S n) := #(S n - x) in
        (* 找出主元 *)
        match getPivot M x j with
        | None => None (* 没有非零元，则该矩阵不可逆 *)
        | Some i =>
            (* 使主元行在当前行 *)
            let (op1, M1) :=
              (if i ??= j       (* 若当前行就是主元行，则不需要交换 *)
               then (ROnop, M)
               else (ROswap j i, mrowSwap j i M)) in
            (* 使主元是 1 *)
            let (op2, M2) :=
              (let c : A := M1.[j].[j] in
               (ROscale j (/c), mrowScale j (/c) M1)) in
            (* 使主元以下都是 0 *)
            let (l3, M3) := elimDown M2 x' j in
            (* 递归 *)
            match rowEchelon M3 x' with
            | None => None
            | Some (l4, M4) => Some ((l4 ++ l3 ++ [op2; op1])%list, M4)
            end
        end
    end.

  (** 对 M 行变换得到 (l, M')，则 [l] * M = M' *)
  Lemma rowEchelon_eq : forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      rowEchelon M x = Some (l, M') -> rowOps2mat l * M = M'.
  Proof.
    induction x; intros.
    - simpl in H. inversion H. simpl. apply mmul_1_l.
    - unfold rowEchelon in H; fold (@rowEchelon (n)) in H. (* Tips: simpl展开太多 *)
      destruct getPivot as [i|] eqn: Hi; try easy.
      replace (S n - S x) with (n - x) in * by lia.
      (* 根据 i ??= #(n - x) 决定是否需要换行 *)
      destruct (i ??= #(n - x)) as [E|E].
      + (* i 就是当前行，不需要换行 *)
        destruct elimDown as [l3 M3] eqn:T3.
        destruct rowEchelon as [[l4 M4]|] eqn:T4; try easy.
        apply IHx in T4. inversion H. rewrite <- H2, <- T4.
        apply elimDown_eq in T3. rewrite <- T3.
        rewrite !rowOps2mat_app. simpl. rewrite !mmul_assoc. f_equal. f_equal.
        rewrite <- mrowScale_mmul. rewrite mmul_1_l. auto.
      + (* i 不是当前行，需要换行 *)
        destruct elimDown as [l3 M3] eqn:T3.
        destruct (rowEchelon M3 x) as [[l4 M4]|] eqn:T4; try easy.
        apply IHx in T4. inversion H. rewrite <- H2, <- T4.
        apply elimDown_eq in T3. rewrite <- T3.
        rewrite !rowOps2mat_app. simpl. rewrite !mmul_assoc. f_equal. f_equal.
        rewrite <- mrowScale_mmul. rewrite <- mrowSwap_mmul. rewrite mmul_1_l. auto.
  Qed.

  (** M 的前 S n - x 列左下角是0，且将 M 的后 x 行变换上三角得到 (l, M')，
      则 M' 的所有列的左下角是 0 *)
  Lemma rowEchelon_mLeftLowerZeros :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      rowEchelon M x = Some (l, M') ->
      x <= S n ->
      mLeftLowerZeros M (S n - x) ->
      mLeftLowerZeros M' (S n).
  Proof.
    induction x; intros.
    - simpl in *. inv H. auto.
    - unfold rowEchelon in H; fold (@rowEchelon n) in H.
      replace (S n - S x) with (n - x) in * by lia.
      destruct getPivot as [i|] eqn : Hi; try easy.
      (* 根据 i ??= #(n - x) 决定是否需要换行 *)
      destruct (i ??= #(n - x)) as [E|E].
      + destruct elimDown as [l3 M3] eqn:T3.
        destruct rowEchelon as [[l4 M4]|] eqn:T4; try easy.
        inv H. apply IHx in T4; auto; try lia; clear IHx.
        replace x with (S n - (S (n - x))) in T3 at 4 by lia.
        apply elimDown_mLeftLowerZeros in T3; try lia.
        * replace (S (n - x)) with (S n - x) in T3 by lia; auto.
        * unfold mrowScale; fin.
          (* 确保元素非零时才能消去除法逆元 *)
          rewrite field_mulInvL; auto.
          apply getPivot_imply_nonzero in Hi. rewrite <- E in *. fin.
        * hnf; intros. unfold mrowScale; fin. rewrite (H1 _ j); fin.
      + destruct elimDown as [l3 M3] eqn:T3.
        destruct rowEchelon as [[l4 M4]|] eqn:T4; try easy.
        inv H. apply IHx in T4; auto; try lia; clear IHx.
        replace x with (S n - (S (n - x))) in T3 at 6 by lia.
        apply elimDown_mLeftLowerZeros in T3; try lia.
        * replace (S (n - x)) with (S n - x) in T3 by lia; auto.
        * unfold mrowScale; fin.
          (* 确保元素非零时才能消去除法逆元 *)
          rewrite field_mulInvL; auto.
          unfold mrowSwap; fin. apply getPivot_imply_nonzero in Hi. auto.
        * hnf; intros. unfold mrowScale, mrowSwap; fin.
          ** rewrite (H1 _ j); fin. apply getPivot_min in Hi. lia.
          ** rewrite (H1 _ j); fin.
  Qed.

  (** 化行阶梯矩阵得到了上三角矩阵 *)
  Lemma rowEchelon_mUpperTrig : forall {n} (M M' : smat (S n)) (l : list RowOp),
      rowEchelon M (S n) = Some (l, M') -> mUpperTrig M'.
  Proof.
    intros. apply rowEchelon_mLeftLowerZeros in H; auto.
    hnf; intros. lia.
  Qed.
  
  (** M 的前 S n - x 个对角线元素是1，且将 M 的后 x 行变换上三角得到 (l, M')，
      则 M' 的所有对角线都是1 *)
  Lemma rowEchelon_mDiagonalOne :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      rowEchelon M x = Some (l, M') ->
      mDiagonalOne M (S n - x) ->
      x <= S n ->
      mDiagonalOne M' (S n).
  Proof.
    induction x; intros.
    - simpl in *. inv H. auto.
    - (* simpl in H. *) (* too much! *)
      unfold rowEchelon in H; fold (@rowEchelon n) in H.
      destruct getPivot as [i|] eqn: Hi; try easy.
      replace (S n - S x) with (n - x) in * by lia.
      (* 根据 i ??= #(n - x) 决定是否需要换行 *)
      destruct (i ??= #(n - x)) as [E|E].
      + destruct elimDown as [l3 M3] eqn:T3.
        destruct rowEchelon as [[l4 M4]|] eqn:T4; try easy.
        apply IHx in T4; clear IHx; try lia.
        * inversion H; clear H. rewrite <- H4. auto.
        * hnf; intros.
          apply elimDown_keep_former_row with (i:=i0)(j:=i0) in T3; fin.
          ** rewrite T3. unfold mrowScale; fin.
             *** rewrite <- E0. fin. rewrite field_mulInvL; auto.
                 rewrite <- E0 in *. fin.
                 apply getPivot_imply_nonzero in Hi; auto.
                 fin2nat. auto.
             *** rewrite H0; auto. lia.
          ** unfold mrowScale; fin. rewrite field_mulInvL; auto.
             apply getPivot_imply_nonzero in Hi. rewrite <- E in *. fin.
      + destruct elimDown as [l3 M3] eqn:T3.
        destruct rowEchelon as [[l4 M4]|] eqn:T4; try easy.
        apply IHx in T4; clear IHx; try lia.
        * inversion H; clear H. rewrite <- H4. auto.
        * hnf; intros.
          apply elimDown_keep_former_row with (i:=i0)(j:=i0) in T3; fin.
          ** rewrite T3. unfold mrowScale, mrowSwap; fin.
             *** rewrite <- E0. fin. rewrite field_mulInvL; auto.
                 apply getPivot_imply_nonzero in Hi.
                 rewrite <- E0 in *. fin.
             *** subst.
                 pose proof (getPivot_max _ _ _ _ Hi).
                 pose proof (getPivot_min _ _ _ _ Hi). lia.
             *** assert (i0 < n - x). lia.
                 rewrite H0; auto.
          ** unfold mrowScale, mrowSwap; fin.
             rewrite field_mulInvL; auto.
             apply getPivot_imply_nonzero in Hi. auto.
  Qed.
  
  (** 化行阶梯矩阵得到的矩阵的对角线都是 1 *)
  Lemma rowEchelon_mDiagonalOnes : forall {n} (M M' : smat (S n)) (l : list RowOp),
      rowEchelon M (S n) = Some (l, M') -> mDiagonalOnes M'.
  Proof.
    intros. unfold mDiagonalOnes. apply rowEchelon_mDiagonalOne in H; auto.
    hnf; lia.
  Qed.

  (** 对 M 行变换得到 (l, M')，则 l 都是有效的 *)
  Lemma rowEchelon_rowOpValid :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      x <= S n -> rowEchelon M x = Some (l, M') -> Forall roValid l.
  Proof.
    induction x; intros.
    - simpl in H0. inversion H0. constructor.
    - unfold rowEchelon in H0; fold (@rowEchelon (n)) in H0.
      destruct getPivot as [i|] eqn: Hi; try easy.
      replace (S n - S x) with (n - x) in * by lia.
      (* 根据 i ??= #(n - x) 决定是否需要换行 *)
      destruct (i ??= #(n - x)) as [E|E].
      + (* i 就是当前行，不需要换行 *)
        destruct elimDown as [l3 M3] eqn:T3.
        destruct rowEchelon as [[l4 M4]|] eqn:T4; try easy. inversion H0.
        apply IHx in T4 as T4'.
        apply elimDown_rowOpValid in T3.
        apply Forall_app. split; auto.
        apply Forall_app. split; auto.
        repeat constructor. unfold roValid.
        apply field_inv_neq0_iff.
        apply getPivot_imply_nonzero in Hi. fin2nat. auto. fin. fin.
      + (* i 不是当前行，需要换行 *)
        destruct elimDown as [l3 M3] eqn:T3.
        destruct (rowEchelon M3 x) as [[l4 M4]|] eqn:T4; try easy.
        apply IHx in T4 as T4'. inversion H0.
        apply elimDown_rowOpValid in T3.
        apply Forall_app. split; auto.
        apply Forall_app. split; auto.
        repeat constructor. unfold roValid.
        apply field_inv_neq0_iff. unfold mrowSwap. fin.
        apply getPivot_imply_nonzero in Hi. auto. fin. fin.
  Qed.

  (** 对 M 行变换得到 (l, M')，则 [l]' * M' = M *)
  Lemma rowEchelon_eq_inv :  forall {n} (M M' : smat (S n)) (l : list RowOp),
      rowEchelon M (S n) = Some (l, M')  -> rowOps2matInv l * M' = M.
  Proof.
    intros. apply rowEchelon_eq in H as H'. rewrite <- H'.
    rewrite <- mmul_assoc. rewrite mmul_rowOps2matInv_rowOps2mat_eq1.
    rewrite mmul_1_l; auto.
    apply rowEchelon_rowOpValid in H. auto. lia.
  Qed.
  
  (** 化行阶梯矩阵得到的矩阵是单位上三角矩阵 *)
  Lemma rowEchelon_mUnitUpperTrig : forall {n} (M M' : smat (S n)) (l : list RowOp),
      rowEchelon M (S n) = Some (l, M') -> mUnitUpperTrig M'.
  Proof.
    intros. hnf. split.
    apply rowEchelon_mUpperTrig in H; auto.
    apply rowEchelon_mDiagonalOnes in H; auto.
  Qed.

  (** 化行阶梯形满足乘法不变式，并且结果矩阵是规范的上三角矩阵 *)
  Theorem rowEchelon_spec :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      rowEchelon M (S n) = Some (l, M') ->
      (rowOps2mat l * M = M') /\ mUnitUpperTrig M'.
  Proof.
    intros. split.
    apply rowEchelon_eq in H; auto.
    apply rowEchelon_mUnitUpperTrig in H; auto.
  Qed.


  (* End GaussElim. *)
  (* Section test. *)

  (*   Import QcExt. *)
  (*   Notation getPivot := (getPivot (Azero:=0)). *)
  (*   Notation rowEchelon := (@rowEchelon _ Qcplus 0 Qcopp Qcmult Qcinv _). *)
  (*   Notation elimDown := (@elimDown _ Qcplus 0 Qcopp Qcmult _). *)
  (*   Notation rowOps2mat := (@rowOps2mat _ Qcplus 0 Qcmult 1 _). *)
  (*   Notation mmul := (@mmul _ Qcplus 0 Qcmult). *)
  (*   Infix "*" := mmul : mat_scope. *)

  (*   (* 行阶梯形 *) *)
  (* (*      [  0 -2  1]     [0    1/3  0]   [1 0 -2/3] *) *)
  (* (*      [  3  0 -2]  => [-1/2   0  0] * [0 1 -1/2] *) *)
  (* (*      [ -2  3  0]     [9      4  6]   [0 0    1] *) *)
  (*   Let M : smat Qc 3 := l2m 0 (Q2Qc_dlist [[0;-2;1];[3;0;-2];[-2;3;0]]%Q). *)
  (*   Let M1 : smat Qc 3 := l2m 0 (Q2Qc_dlist [[1;0;-2/3];[0;1;-1/2];[0;0;1]]%Q). *)
  (*   Let E1 : smat Qc 3 := l2m 0 (Q2Qc_dlist [[0;1/3;0];[-1/2;0;0];[9;4;6]]%Q). *)
  
  (*   Goal match rowEchelon M 3 with *)
  (*        | Some (l1',M1') => m2l (rowOps2mat l1') = m2l E1 *)
  (*                           /\ m2l M1' = m2l M1 *)
  (*        | _ => False *)
  (*        end. *)
  (*   Proof. *)
  (*     Time cbv; split; list_eq; f_equal; apply proof_irrelevance. *)
  (*   Qed. *)

  (*   (* 验证 E1 将 M 变换到了 M1 *) *)
  (*   Goal (E1 * M)%M = M1. *)
  (*   Proof. apply m2l_inj. cbv. list_eq; f_equal. Qed. *)

  (* End test. *)

  (* ******************************************************************* *)
  (** ** 向上消元 *)
  
  (* 将矩阵M的第 j 列的前 x 行元素变为 0。当 j=#(S n)时，x=S n *)
  Fixpoint elimUp {n} (M : smat (S n)) (x : nat) (j : 'I_(S n))
    : list RowOp * smat (S n) :=
    match x with
    | O => ([], M)
    | S x' =>
        let fx : 'I_(S n) := #x' in
        let a : A := (M.[fx].[j]) in
        (* 如果 M[x',j] <> 0，则 j 行的 -M[x',j] 倍加到 x' 行。要求 M[j,j]=1 *)
        if Aeqdec a 0
        then elimUp M x' j
        else
          let (op1, M1) := (ROadd fx j (-a)%A, mrowAdd fx j (-a)%A M) in
          let (l2, M2) := elimUp M1 x' j in
          ((l2 ++ [op1])%list, M2)
    end.

  (** 对 M 向上消元得到 (l, M')，则 [l] * M = M' *)
  Lemma elimUp_eq :
    forall (x : nat) {n} (M M' : smat (S n)) (j : 'I_(S n)) (l : list RowOp),
      elimUp M x j = (l, M') -> rowOps2mat l * M = M'.
  Proof.
    induction x; intros; simpl in *.
    - inversion H. simpl. apply mmul_1_l.
    - (* 当前元素是否为0，若是则直接递归，若不是则消元后递归 *)
      destruct (Aeqdec (M #x j) 0) as [E|E].
      + apply IHx in H; auto.
      + destruct elimUp as [l2 M2] eqn:T2.
        apply IHx in T2. inv H.
        rewrite rowOps2mat_app. simpl.
        rewrite !mmul_assoc. f_equal.
        rewrite <- mrowAdd_mmul. rewrite mmul_1_l. auto.
  Qed.
  
  (** 对 M 向上消元得到 (l, M')，则 l 都是有效的 *)
  Lemma elimUp_rowOpValid :
    forall (x : nat) {n} (M M' : smat (S n)) (j : 'I_(S n)) (l : list RowOp),
      x <= j ->     (* 前 x 行，行号不超过 j *)
      elimUp M x j = (l, M') -> Forall roValid l.
  Proof.
    induction x; intros; simpl in *.
    - inversion H0. constructor.
    - (* 当前元素是否为0，若是则直接递归，若不是则消元后递归 *)
      destruct (Aeqdec (M #x j) 0) as [E|E].
      + apply IHx in H0; auto. fin.
      + destruct elimUp as [l2 M2] eqn:T2.
        apply IHx in T2; fin. inv H0.
        apply Forall_app. split; auto. repeat constructor. hnf. intros.
        rewrite <- H0 in H.
        rewrite fin2nat_nat2finS in H; fin.
        pose proof (fin2nat_lt j). fin.
  Qed.

  (** 对 M 向上消元保持单位上三角矩阵 *)
  Lemma elimUp_mUnitUpperTrig :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp) (j : 'I_(S n)),
      elimUp M x j = (l, M') ->
      x <= j ->     (* 前 x 行，行号不超过 j *)
      mUnitUpperTrig M -> mUnitUpperTrig M'.
  Proof.
    induction x; intros.
    - simpl in H. inv H. auto.
    - simpl in H.
      destruct (Aeqdec (M #x j) 0) as [E|E].
      + apply IHx in H; auto; try lia.
      + destruct elimUp as [l2 M2] eqn: T2. inv H.
        apply IHx in T2; auto; try lia.
        apply mrowAdd_mUnitUpperTrig; auto. fin.
        pose proof (fin2nat_lt j). lia.
  Qed.

  (* 上消元时，x 行及以下的行保持不变 *)
  Lemma elimUp_keep_lower_rows :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp) (y : 'I_(S n)),
      elimUp M x y = (l, M') ->
      x <= y ->     (* 前 x 行，行号不超过 y *)
      (forall i j : 'I_(S n), x <= i -> M' i j = M i j).
  Proof.
    induction x; intros.
    - simpl in H. inv H. auto.
    - simpl in H.
      destruct (Aeqdec (M #x y) 0) as [E|E].
      + apply IHx with (i:=i)(j:=j) in H; auto; try lia.
      + destruct elimUp as [l2 M2] eqn: T2. inv H.
        apply IHx with (i:=i)(j:=j) in T2; auto; try lia.
        rewrite T2. unfold mrowAdd; fin.
        pose proof (fin2nat_lt y). lia.
  Qed.
  
  (* 上消元后该列上方元素为 0 *)
  Lemma elimUp_upper_rows_0 :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp) (y : 'I_(S n)),
      elimUp M x y = (l, M') ->
      mUnitUpperTrig M ->
      x <= y ->     (* 前 x 行，行号不超过 y *)
      (forall i : 'I_(S n), i < x -> M' i y = 0).
  Proof.
    induction x; intros; try lia.
    simpl in H. hnf in H0. destruct H0 as [H00 H01].
    destruct (Aeqdec (M #x y) 0) as [E|E].
    - (* i 在当前列 x，或者 i 小于 x *)
      destruct (x ??= i) as [E1|E1].
      + apply elimUp_keep_lower_rows with (i:=i)(j:=y) in H; try lia.
        rewrite H. subst. fin.
      + apply IHx with (i:=i) in H; auto; try lia. split; auto.
    - destruct elimUp as [l2 M2] eqn: T2. inv H.
      (* i 在当前列 x，或者 i 小于 x *)
      destruct (x ??= i) as [E1|E1].
      + rewrite E1 in *.
        apply elimUp_keep_lower_rows with (i:=i)(j:=y) in T2; try lia. rewrite T2.
        unfold mrowAdd; fin. rewrite H01; auto; try lia; fin.
      + apply IHx with (i:=i) in T2; auto; try lia.
        apply mrowAdd_mUnitUpperTrig; auto. split; auto.
        fin. pose proof (fin2nat_lt y). lia.
  Qed.

  (** 若 M 的后 L 列的右上角都是 0，则上消元后，M' 的后 L 列的右上角都是 0 *)
  Lemma elimUp_mUpperRightZeros_aux :
    forall (x L : nat) {n} (M M' : smat (S n)) (l : list RowOp) (y : 'I_(S n)),
      elimUp M x y = (l, M') ->
      x <= y ->
      L < S n - y ->
      mUnitUpperTrig M ->
      mRightUpperZeros M L ->
      mRightUpperZeros M' L.
  Proof.
    induction x; intros; simpl in H. inv H; auto.
    simpl in H.
    destruct (Aeqdec (M #x y) 0) as [E|E].
    - hnf; intros.
      apply IHx with (L:=L) in H; auto; try lia.
    - destruct elimUp as [l2 M2] eqn: T2. inv H.
      hnf; intros.
      apply IHx with (L:=L) in T2; auto; try lia.
      + apply mrowAdd_mUnitUpperTrig; auto. fin.
      + hnf; intros. unfold mrowAdd; fin.
        rewrite !(H3 _ j0); try lia. ring.
  Qed.
  
  (** 若 M 的后 (S n - S y) 列的右上角都是 0，则上消元后，S n - y 列的右上角都是 0 *)
  Lemma elimUp_mUpperRightZeros:
    forall {n} (M M' : smat (S n)) (l : list RowOp) (y : nat),
      elimUp M y #y = (l, M') ->
      y < S n ->
      mUnitUpperTrig M ->
      mRightUpperZeros M (S n - S y) ->
      mRightUpperZeros M' (S n - y).
  Proof.
    intros. hnf; intros.
    replace (S n - (S n - y)) with y in H3 by lia.
    destruct (j ??= y) as [E|E].
    - subst. apply elimUp_upper_rows_0 with (i:=i) in H; auto; fin.
    - apply elimUp_mUpperRightZeros_aux with (L:=S n - S y) in H; auto; fin.
      rewrite H; auto. lia.
  Qed.
  
  (* End GaussElim. *)
  (* Section test. *)

  (*   Import QcExt. *)
  (*   Notation elimUp := (@elimUp _ Qcplus 0 Qcopp Qcmult _). *)
  
  (*   Let M : smat Qc 3 := l2m 0 (Q2Qc_dlist [[1;2;3];[4;5;6];[7;8;1]]%Q). *)
  (*   Compute m2l (snd (elimUp M 2 #2)). *)
  (* End test. *)
  

  (* ******************************************************************* *)
  (** ** 最简行阶梯形矩阵 *)

  (* 将矩阵 M 的前 x 行(列)化为行最简阶梯形。当 x 为 S n 时表示整个矩阵 *)
  Fixpoint minRowEchelon {n} (M : smat (S n)) (x : nat) : list RowOp * smat (S n) :=
    match x with
    | O => ([], M)
    | S x' =>
        let fx : 'I_(S n) := #x' in
        let (l1, M1) := elimUp M x' fx in
        let (l2, M2) := minRowEchelon M1 x' in
        ((l2 ++ l1)%list, M2)
    end.

  (** 对 M 最简行变换得到 (l, M')，则 [l] * M = M' *)
  Lemma minRowEchelon_eq : forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      minRowEchelon M x = (l, M') -> rowOps2mat l * M = M'.
  Proof.
    induction x; intros; simpl in *.
    - inversion H. simpl. apply mmul_1_l.
    - destruct elimUp as [l1 M1] eqn : T1.
      destruct minRowEchelon as [l2 M2] eqn : T2.
      apply IHx in T2. inv H.
      apply elimUp_eq in T1. rewrite <- T1.
      rewrite rowOps2mat_app. apply mmul_assoc.
  Qed.

  (* minRowEchelon 保持上三角 *)
  Lemma minRowEchelon_mUnitUpperTrig :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      minRowEchelon M x = (l, M') ->
      x <= S n ->
      mUnitUpperTrig M ->
      mUnitUpperTrig M'.
  Proof.
    induction x; intros; simpl in H. inv H; auto.
    destruct elimUp as [l1 M1] eqn : T1.
    destruct minRowEchelon as [l2 M2] eqn : T2. inv H.
    apply IHx in T2; auto; try lia.
    apply elimUp_mUnitUpperTrig in T1; auto. fin.
  Qed.
  
  (** 若 M 的 后 S n - x 列的右上角都是0，则对 M 最简行变换得到的 M' 的右上角都是0 *)
  Lemma minRowEchelon_mRightUpperZeros :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      minRowEchelon M x = (l, M') ->
      x <= S n ->
      mUnitUpperTrig M ->
      mRightUpperZeros M (S n - x) ->
      mRightUpperZeros M' (S n).
  Proof.
    induction x; intros; simpl in H. inv H; auto.
    destruct elimUp as [l1 M1] eqn : T1.
    destruct minRowEchelon as [l2 M2] eqn : T2. inv H.
    apply IHx in T2; auto; try lia.
    - apply elimUp_mUnitUpperTrig in T1; auto. fin.
    - apply elimUp_mUpperRightZeros in T1; auto.
  Qed.

  (** 对 M 向下消元得到 (l, M')，则 l 都是有效的 *)
  Lemma minRowEchelon_rowOpValid :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      minRowEchelon M x = (l, M') -> x <= S n -> Forall roValid l.
  Proof.
    induction x; intros; simpl in H. inv H; auto.
    destruct elimUp as [l1 M1] eqn : T1.
    destruct minRowEchelon as [l2 M2] eqn : T2. inv H.
    apply IHx in T2; auto; try lia.
    apply elimUp_rowOpValid in T1 as T1'; fin.
    apply Forall_app. split; auto.
  Qed.
  
  (** 对 M 最简行变换得到 (l, M')，则 [l]' * M' = M *)
  Lemma minRowEchelon_eq_inv : forall {n} (M M' : smat (S n)) (l : list RowOp),
      minRowEchelon M (S n) = (l, M') -> rowOps2matInv l * M' = M.
  Proof.
    intros. apply minRowEchelon_eq in H as H'. rewrite <- H'.
    rewrite <- mmul_assoc. rewrite mmul_rowOps2matInv_rowOps2mat_eq1.
    rewrite mmul_1_l; auto.
    apply minRowEchelon_rowOpValid in H; fin.
  Qed.
  
  (** 对 M 最简行变换得到 (l, M')，则 M' 是单位阵 *)
  Lemma minRowEchelon_mat1 : forall {n} (M M' : smat (S n)) (l : list RowOp),
      minRowEchelon M (S n) = (l, M') ->
      mUnitUpperTrig M -> M' = mat1.
  Proof.
    intros. apply meq_iff_mnth; intros. 
    (* 分别处理：左下角、对角线、右上角 *)
    destruct (j ??< i).
    - (* 左下角 *)
      rewrite mat1_mLeftLowerZeros; auto; fin.
      apply minRowEchelon_mUnitUpperTrig in H; auto.
      hnf in H. destruct H. rewrite H; auto; fin.
    - destruct (j ??= i) as [E|E].
      + (* 对角线 *)
        apply minRowEchelon_mUnitUpperTrig in H; auto. fin2nat.
        rewrite mat1_mDiagonalOne; fin.
        hnf in H. destruct H. rewrite H1; auto; fin.
      + (* 右上角 *)
        assert (i < j) by lia.
        rewrite mat1_mRightUpperZeros; auto; fin.
        apply minRowEchelon_mRightUpperZeros in H; auto; fin.
        * rewrite H; auto; try lia.
        * hnf; intros. pose proof (fin2nat_lt j0). lia.
  Qed.

End GaussElim.


Section test.
  Import QcExt.
  Open Scope mat_scope.

  Notation smat n := (smat Qc n).
  Notation mat1 := (@mat1 _ 0 1).
  Notation mmul := (@mmul _ Qcplus 0 Qcmult).
  Infix "*" := mmul : mat_scope.
  Notation rowEchelon := (@rowEchelon _ Qcplus 0 Qcopp Qcmult Qcinv).
  Notation minRowEchelon := (@minRowEchelon _ Qcplus 0 Qcopp Qcmult).
  Notation elimUp := (@elimUp _ Qcplus 0 Qcopp Qcmult).
  Notation rowOps2mat := (@rowOps2mat _ Qcplus 0 Qcmult 1).
  Notation rowOps2matInv := (@rowOps2matInv _ Qcplus 0 Qcopp Qcmult 1 Qcinv).
  
  (*
                                  [ 0 -2  1]
                                  [ 3  0 -2]                 M0
                                  [-2  3  0]

  行阶梯形
                  [0    1/3  0]   [ 0 -2  1]   [1 0 -2/3]
                  [-1/2   0  0] * [ 3  0 -2] = [0 1 -1/2]    T1 * M0 = M1
                  [9      4  6]   [-2  3  0]   [0 0    1]

  简化行阶梯形
    [1  0  2/3]   [0    1/3  0]   [ 0 -2  1]   [1 0 0]
    [0  1  1/2] * [-1/2   0  0] * [ 3  0 -2] = [0 1 0]       T2 * T1 * M0 = M2
    [0  0    1]   [9      4  6]   [-2  3  0]   [0 0 1]

  逆矩阵
                        [6 3 4]   [ 0 -2  1]   [1 0 0]
                        [4 2 3] * [ 3  0 -2] = [0 1 0]       N0 * M0 = I
                        [9 4 6]   [-2  3  0]   [0 0 1]
   *)

  (* 通过元素的比较来证明两个有限维的矩阵相等 *)
  Ltac meq :=
    apply m2l_inj; cbv; list_eq; f_equal; apply proof_irrelevance.
  
  (* 给定输入 M0 *)
  Let M0 : smat 3 := l2m 0 (Q2Qc_dlist [[0;-2;1];[3;0;-2];[-2;3;0]]%Q).
  (* 算出 M0 的逆矩阵一定是 N0 *)
  Let N0 : smat 3 := l2m 0 (Q2Qc_dlist [[6;3;4];[4;2;3];[9;4;6]]%Q).

  (* 验证 M0 和 N0 互逆 *)
  Goal M0 * N0 = mat1.
  Proof. meq. Qed.

  Goal N0 * M0 = mat1.
  Proof. meq. Qed.
  
  (* 行阶梯形 *)
  Let l1 := match rowEchelon M0 3 with Some (l1,M1) => l1 | _ => [] end.
  Let T1 : smat 3 := rowOps2mat l1.
  Let M1 : smat 3 := match rowEchelon M0 3 with Some (l1,M1) => M1 | _ => mat1 end.
  
  (* 简化行阶梯形 *)
  Let l2 := fst (minRowEchelon M1 3).
  Let T2 : smat 3 := rowOps2mat l2.
  Let M2 : smat 3 := snd (minRowEchelon M1 3).

  (* 证明变换后的矩阵 M2 是单位阵 *)
  Goal M2 = mat1.
  Proof. meq. Qed.

  (* 验证变换阵 T2*T1 是逆矩阵 N0 *)
  Goal T2 * T1 = N0.
  Proof. meq. Qed.
  
  (* 可直接计算这些矩阵值 *)
  (* Compute m2l (T2 * T1). *)

  (* 我们还能得到以下结论：
     1. 根据 T1 * M0 = M1 得到 M0 = T1\-1 * M1
     2. 根据 T2 * M1 = E  得到 M1 = T2\-1
     3. 根据 T2 * T1 * M0 = E 得到 M0 = T1\-1 * T2\-1
     注意，由于 T1 和 T2 是由初等行变换构造的，其逆矩阵很容易求得。
   *)
  Goal rowOps2matInv l1 * M1 = M0.
  Proof. meq. Qed.
  
  Goal rowOps2matInv l2 = M1.
  Proof. meq. Qed.
  
  Goal rowOps2matInv l1 * rowOps2matInv l2 = M0.
  Proof. meq. Qed.

  (* 并猜测 rowOps2matInv_app 性质 *)
  Goal rowOps2matInv (l2 ++ l1) = M0.
  Proof. meq. Qed.
  
End test.
