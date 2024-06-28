(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Determinant of matrix
  author    : Zhengpu Shi
  date      : 2023.06

  motivation :
  1. 数域K上n个方程的n元线性方程组有唯一解 <==> n阶行列式(n级矩阵的行列式)非零。
  2. 行列式在几何、分析等数学分支中也有重要应用。

  remark    :
  1. 行列式的定义：n!个单项式的代数和，每个项是矩阵中不同行不同列元素的乘积，并冠以逆序数。
  (1) 2级矩阵
     A = [[a11;a12]; [a21;a22]]
     det(A) = a11*a22 + -(a12*a21)
            = a11*det[[a22]] + (-a12)*det[[a21]]  按第1行展开
            = (-a21)*det[[a12]] + a22*det[[a11]]  按第2行展开
            = a11*det[[a22]] + (-a21)*det[[a12]]  按第1列展开
            = (-a12)*det[[a21]] + a22*det[[a11]]  按第2列展开
  (2) 3级矩阵
     A = [[a11;a12;a13]; [a21;a22;a23]; [a31;a32;a33]]，
     det(A) = a11*a22*a33 + -a11*a23*a32 + ...
            = a11*det[[a22;a23];[a32;a33]])
              + (-a12)*det[[a21;a23];[a31;a33]]
              + a13*det[[a21;a22];[a31;a32]]    按第1行展开
            = 其他含开方式类似

  这里展示了两种方法：原始的凑下标的方式，递归的按某行某列展开的方法。
  数学上已经证明这两种方法的等价性。在Coq中也可以验证一次。
              
  上述分析发现，我们需要如下的算法：
  (1). 逆序数：给定一个自然数列表，
  (2). 行列式原始算法：如何取出不同行不同列下标的所有组合。
  (3). 子矩阵：去掉一行一列后剩下的矩阵。这是构造按某行某列展开算法的基础。

  2. 行列式的性质
  (1) n阶行列式是 n! 项的代数和，其中每一项是位于不同行、不同列的n个元素的乘积。
      当 n 增大时，n! 迅速增大。例如：5!=120, 10!=3628800 (362万个项)。
      所以我们一般不会做完全展开。
  (2) 行列互换（即矩阵做转置），行列式的值不变。这表明行列式的行与列的地位是对称的。
      因此有关行的性质，对于列也同样成立。今后只研究有关行的性质。

  3. 行列式的行指标、列指标的各种可能性
  (1) 2 级为例
         12    21
      12 11*22 12*21
      21 21*12 22*11
      有2!种行指标排列，构成了每一行: 11*22-12*21, -21*12+22*11
      有2!种列指标排列，构成了每一列: 11*22-21*12, -12*21+22*11
  (2) 3级矩阵
          123      132      213      231      312      321
      123 11*22*33 11*23*32 12*21*33 12*23*31 13*21*32 13*22*31
      132
      213
      231
      312
      321
      有3!种行指标排列，构成了每一行。
      有3!种列指标排列，构成了每一列。
   (3) n级矩阵
      有n!种行指标排列，每个排列构成了一行，第一行是行指标自然序。
      有n!种列指标排列，每个排列构成了一列，第一列是列指标自然序。
      该矩阵应该满足：每一行相加都相等，每一列相加也相等。
 *)

Require Export ListExt NatExt Permutation Matrix.

Generalizable Variable tA Aadd Azero Aopp Amul Aone Ainv.


(* ############################################################################ *)
(** * n-order of determinant *)

(* ======================================================================= *)
(** ** Full expansion of determinant *)
Section mdet.
  Context `{HARing : ARing}.
  Add Ring ring_inst : (make_ring_theory HARing).

  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + -b).
  Infix "-" := Asub : A_scope.
  Infix "*" := Amul : A_scope.

  Notation vadd := (@vadd _ Aadd).
  Infix "+" := vadd : vec_scope.
  Notation vscal := (@vscal _ Amul).
  Infix "s*" := vscal : vec_scope.

  Notation smat n := (smat tA n).
  Notation mmul := (@mmul _ Aadd 0 Amul).
  Infix "*" := mmul : mat_scope.
  Notation mat1 := (@mat1 _ 0 1).
  Notation seqsum := (@seqsum _ Aadd 0).
  Notation seqprod := (@seqprod _ Amul 1).
  Notation ronum := (@ronum nat Nat.ltb).

  (** n阶行列式的完全展开式 (行下标固定，列下标来自于全排列）*)

  (* Tips: 对 colIds 使用 list 而不是 vec，因为 perm 的个数难以用依赖类型表达 *)
  
  (* 旧的实现：元素索引为 fin 类型，故需要 i < n 的证明，故需要处理 n = 0 *)
  Definition mdet_old {n} : smat n -> tA :=
    match n with
    | O => fun _ => 1        (* the determinant of a empty matrix is 1 *)
    | S n' =>
        fun (M : smat (S n')) =>
          (* 列号 0,1,..,(n-1) 的全排列 *)
          let colIds := perm (seq 0 n) in
          (* 每个式 *)
          let item (l:list nat) : tA :=
            (let x := seqprod n (fun i => M.[#i].[#(nth i l O)]) in
             if odd (ronum l) then - x else x) in
          (* 求和 *)
          fold_left Aadd (map item colIds) 0
    end.

  (** 新的实现：元素索引为 nat 类型，避免了提供 i < n 的证明，无需处理 n = 0 *)
  Definition mdet {n} (M : smat n) : tA :=
    (* 列号 0,1,..,(n-1) 的全排列 *)
    let colIds : dlist nat := perm (seq 0 n) in
    (* 每个项 *)
    let item (l : list nat) : tA :=
      (let x := seqprod n (fun i => (m2f 0 M) i (nth i l O)) in
       if odd (ronum l) then - x else x) in
    (* 求和 *)
    fold_left Aadd (map item colIds) 0.

  Notation "| M |" := (mdet M) : mat_scope.

  (** n阶行列式的完全展开式 (列下标固定，行下标来自于全排列）*)
  Definition mdet' {n} (M : smat n) : tA :=
    (* 行号 0,1,..,(n-1) 的全排列 *)
    let rowIds : dlist nat := perm (seq 0 n) in
    (* 每个项 *)
    let item (l : list nat) : tA :=
      (let x := seqprod n (fun j => (m2f 0 M) (nth j l O) j) in
       if odd (ronum l) then - x else x) in
    (* 求和 *)
    fold_left Aadd (map item rowIds) 0.

  (* 上述两种算法等价 *)
  Lemma mdet'_eq_mdet : forall {n} (M : smat n), mdet' M = mdet M.
  Proof.
  (* 该命题的证明见丘维声老师《高等代数》P35，我暂时未完成验证 *)
  Admitted.

  (** Property 1: |M\T| = |M| *)
  Lemma mdet_mtrans : forall {n} (M : smat n), |M\T| = |M|.
  Proof.
    intros. rewrite <- mdet'_eq_mdet at 1.
    unfold mdet, mdet'. f_equal.
    apply map_ext_in; intros.
    destruct (odd (ronum a)).
    - f_equal. apply seqsum_eq; intros.
      erewrite !nth_m2f, mnth_mtrans; auto.
    - apply seqprod_eq; intros. erewrite !nth_m2f, mnth_mtrans; auto.
      Unshelve. all: auto.
      apply perm_index_lt; auto.
      apply perm_index_lt; auto.
  Qed.

  (* |M*N| = |M| * |N| *)
  Lemma mdet_mmul : forall {n} (M N : smat n), |M * N| = (|M| * |N|)%A.
  Proof.
  Admitted.

  (* |mat1| = 1 *)
  Lemma mdet_mat1 : forall {n}, |@mat1 n| = 1.
  Proof.
    induction n; simpl.
    - unfold mdet. simpl. ring.
    - unfold mdet in *. simpl.
  Admitted.

  (** g (f a1 + ... + f an + b) = gf a1 + ... + gf an + g b *)
  Lemma fold_left_map :
    forall {tA tB} (l : list tA) (fadd : tB -> tB -> tB) (b : tB) (f : tA -> tB) (g : tB -> tB)
      (homo: forall b1 b2, g (fadd b1 b2) = fadd (g b1) (g b2)),
      g (fold_left fadd (map f l) b) =
        fold_left fadd (map (fun x => g (f x)) l) (g b).
  Proof.
    clear. intros tA tB l.
    induction l; intros; simpl; auto.
    rewrite IHl; auto. f_equal. auto.
  Qed.

  (** h (f a1 + ... + f an + b1) (g a1 + ... + g an + b2) = 
      hfg a1 + ... + hfg an + h b1 b2 *)
  Lemma fold_left_map_map :
    forall {tA tB} (l : list tA) (fadd : tB -> tB -> tB) (b1 b2 : tB) (f g : tA -> tB)
      (h : tB -> tB -> tB)
      (homo: forall b1 b2 b3 b4, h (fadd b1 b3) (fadd b2 b4) = fadd (h b1 b2) (h b3 b4)),
      h (fold_left fadd (map f l) b1) (fold_left fadd (map g l) b2) =
        fold_left fadd (map (fun x => h (f x) (g x)) l) (h b1 b2).
  Proof.
    clear. intros tA tB l.
    induction l; intros; simpl; auto.
    rewrite IHl; auto. f_equal. auto.
  Qed.
  
  (** Property 2 : | M with x*row(M,i) | = x * |M| *)
  Lemma mdet_row_scale : forall {n} (M1 M2 : smat n) (i : 'I_n) (x : tA),
      (forall j, j <> i -> M1.[j] = M2.[j]) ->
      (M1.[i] = x s* M2.[i])%V -> |M1| = (x * |M2|)%A.
  Proof.
    intros. unfold mdet.
    rewrite fold_left_map.
    2:{ intros; ring. }
    f_equal; try ring. apply map_ext_in; intros.
    assert (seqprod n (fun i0 : nat => m2f 0 M1 i0 (nth i0 a O)) =
              (x * seqprod n (fun i0 : nat => m2f 0 M2 i0 (nth i0 a O)))%A).
    - rewrite seqprod_scal_l with (j:=i); [|fin].
      apply seqprod_eq; intros.
      assert (i0 < n) as Hi by lia.
      assert (nth i0 a O < n) as Hj. apply perm_index_lt; auto.
      bdestruct (i0 =? i).
      + rewrite !nth_m2f with (Hi:=Hi)(Hj:=Hj).
        replace (nat2fin i0 Hi) with i. rewrite H0; auto. subst; fin.
      + rewrite !nth_m2f with (Hi:=Hi)(Hj:=Hj). rewrite H; auto.
        intro; destruct H3; subst; fin.
    - destruct (odd (ronum a)) eqn:E; auto.
      rewrite H2. ring.
  Qed.

  (** Property 3: 若某一行是两组数的和，则行列式等于两个行列式的和，
      它们的这一行分别是这两组数 *)
  Lemma mdet_row_add : forall {n} (M1 M2 M : smat n) (i : 'I_n),
      (forall j, j <> i -> M1.[j] = M.[j] /\ M2.[j] = M.[j]) ->
      (M1.[i] + M2.[i])%V = M.[i] -> |M| = (|M1| + |M2|)%A.
  Proof.
    intros. unfold mdet.
    rewrite fold_left_map_map.
    2:{ intros; ring. }
    f_equal; try ring. apply map_ext_in; intros.
    assert (seqprod n (fun i0 : nat => m2f 0 M i0 (nth i0 a O)) =
              (seqprod n (fun i0 : nat => m2f 0 M1 i0 (nth i0 a O)) +
                 seqprod n (fun i0 : nat => m2f 0 M2 i0 (nth i0 a O)))%A).
    - pose proof (fin2nat_lt i) as Hi.
      replace n with (i + S (n - S i))%nat at 1 2 3 by lia.
      rewrite !seqprod_plusIdx_three.
      replace (m2f 0 M i (nth i a O))
        with ((m2f 0 M1 i (nth i a O)) + (m2f 0 M2 i (nth i a O)))%A.
      2:{
        assert (nth i a O < n) as Hj. apply perm_index_lt; auto.
        rewrite !nth_m2f with (Hi:=Hi) (Hj:=Hj). fin.
        rewrite <- H0. rewrite vnth_vadd. auto. }
      ring_simplify. f_equal.
      + (* LEFT PART *)
        move2h (m2f 0 M1 i (nth i a O)). f_equal. f_equal.
        * apply seqprod_eq; intros.
          assert (i0 < n) as Hi0. pose proof (fin2nat_lt i). lia.
          assert (nth i0 a O < n) as Hj0. apply perm_index_lt; auto.
          rewrite !nth_m2f with (Hi:=Hi0) (Hj:=Hj0).
          assert (nat2fin i0 Hi0 <> i).
          { intro. subst. fin. }
          destruct (H _ H3). rewrite H4. auto.
        * apply seqprod_eq; intros.
          assert (S (i + i0) < n) as Hi0. pose proof (fin2nat_lt i). lia.
          assert (nth (S (i + i0)) a O < n) as Hj0. apply perm_index_lt; auto.
          rewrite !nth_m2f with (Hi:=Hi0) (Hj:=Hj0).
          assert (nat2fin (S (i + i0)) Hi0 <> i).
          { intro. destruct i. simpl in *. apply fin_eq_iff in H3. lia. }
          destruct (H _ H3). rewrite H4. auto.
      + (* RIGHT PART, same as LEFT PART *)
        move2h (m2f 0 M2 i (nth i a O)). f_equal. f_equal.
        * apply seqprod_eq; intros.
          assert (i0 < n) as Hi0. pose proof (fin2nat_lt i). lia.
          assert (nth i0 a O < n) as Hj0. apply perm_index_lt; auto.
          rewrite !nth_m2f with (Hi:=Hi0) (Hj:=Hj0).
          assert (nat2fin i0 Hi0 <> i).
          { intro. subst. fin. }
          destruct (H _ H3). rewrite H5. auto.
        * apply seqprod_eq; intros.
          assert (S (i + i0) < n) as Hi0. pose proof (fin2nat_lt i). lia.
          assert (nth (S (i + i0)) a O < n) as Hj0. apply perm_index_lt; auto.
          rewrite !nth_m2f with (Hi:=Hi0) (Hj:=Hj0).
          assert (nat2fin (S (i + i0)) Hi0 <> i).
          { intro. destruct i. simpl in *. apply fin_eq_iff in H3. lia. }
          destruct (H _ H3). rewrite H5. auto.
    - destruct (odd (ronum a)) eqn:E; auto.
      rewrite H2. ring.
  Qed.
  
  (* Property 4: 两行互换，行列式反号 (单侧的 i < k) *)
  Lemma mdet_row_swap_lt : forall {n} (M1 M2 : smat n) (i k : 'I_n),
      i < k ->
      (forall j, j <> i -> j <> k -> M1.[j] = M2.[j]) ->
      M1.[i] = M2.[k] -> M1.[k] = M2.[i] ->
      (|M1| = - |M2|)%A.
  Proof.
    intros. unfold mdet.
    rewrite fold_left_map. 2: intros; ring.
    (* NOTE: sum is equal, but the elements are not point-wise equal *)

    (* BELOW PROOF IS A WRONG WORK *)
    f_equal; try ring. apply map_ext_in; intros.
    assert (seqprod n (fun i0 : nat => m2f 0 M1 i0 (nth i0 a O)) =
              - seqprod n (fun i0 : nat => m2f 0 M2 i0 (nth i0 a O))).
    - pose proof (fin2nat_lt i) as Hi.
      pose proof (fin2nat_lt k) as Hk.
      replace n with (i + S ((k - S i) + S (n - S k)))%nat at 1 2; fin.
      repeat (rewrite ?seqprod_plusIdx; rewrite ?seqprodS_head).
      replace (i + O)%nat with (fin2nat i); fin.
      replace (i + S (k - S i + O))%nat with (fin2nat k); fin.
      move2h (m2f 0 M1 k (nth k a O)).
      move2h (m2f 0 M1 i (nth i a O)).
      move2h (m2f 0 M2 k (nth k a O)).
      move2h (m2f 0 M2 i (nth i a O)).
      ring_simplify.
      assert (nth i a O < n) as Hi'. apply perm_index_lt; auto.
      assert (nth k a O < n) as Hk'. apply perm_index_lt; auto.
      rewrite !nth_m2f with (Hi:=Hi)(Hj:=Hi').
      rewrite !nth_m2f with (Hi:=Hk)(Hj:=Hk').
      fin. rewrite H1,H2.
      remember (seqprod i (fun i0 : nat => m2f 0 M1 i0 (nth i0 a O))) as x1.
      remember (seqprod i (fun i0 : nat => m2f 0 M2 i0 (nth i0 a O))) as y1.
      remember (seqprod (k - S i)
                  (fun i0 : nat => m2f 0 M1 (i + S i0) (nth (i + S i0) a O))) as x2.
      remember (seqprod (k - S i)
                  (fun i0 : nat => m2f 0 M2 (i + S i0) (nth (i + S i0) a O))) as y2.
      remember (seqprod (n - S k)
                  (fun i0 : nat => m2f 0 M1 (i + S (k - S i + S i0))
                                 (nth (i + S (k - S i + S i0)) a O)))%A as x3.
      remember (seqprod (n - S k)
                  (fun i0 : nat => m2f 0 M2 (i + S (k - S i + S i0))
                                 (nth (i + S (k - S i + S i0)) a O)))%A as y3.
      assert (x1 = y1).
      { rewrite Heqx1, Heqy1. apply seqprod_eq; intros.
        assert (i0 < n) by lia. assert (nth i0 a O < n). apply perm_index_lt; auto.
        erewrite !nth_m2f with (Hi:=H5)(Hj:=H6).
        destruct i,k. fin. rewrite H0; auto.
        { intro. apply fin_eq_iff in H7. lia. }
        { intro. apply fin_eq_iff in H7. lia. } }
      assert (x2 = y2).
      { rewrite Heqx2, Heqy2. apply seqprod_eq; intros.
        assert (i + S i0 < n) by lia.
        assert (nth (i + S i0) a O < n). apply perm_index_lt; auto.
        erewrite !nth_m2f with (Hi:=H6)(Hj:=H7).
        destruct i,k. fin. rewrite H0; auto.
        { intro. apply fin_eq_iff in H8. fin. }
        { intro. apply fin_eq_iff in H8. fin. } }
      assert (x3 = y3).
      { rewrite Heqx3, Heqy3. apply seqprod_eq; intros.
        assert (i + S (k - S i + S i0) < n) by lia.
        assert (nth (i + S (k - S i + S i0)) a O < n). apply perm_index_lt; auto.
        erewrite !nth_m2f with (Hi:=H7)(Hj:=H8).
        destruct i,k. fin. rewrite H0; auto.
        { intro. apply fin_eq_iff in H9. fin. }
        { intro. apply fin_eq_iff in H9. fin. } }
      clear Heqx1 Heqy1 Heqx2 Heqy2 Heqx3 Heqy3. subst.
      admit.
    - rewrite H4. destruct (odd (ronum a)); auto.
  Admitted.
  
  (* Property 4: 两行互换，行列式反号 (低阶描述的版本) *)
  Lemma mdet_row_swap : forall {n} (M1 M2 : smat n) (i k : 'I_n),
      i <> k ->
      (forall j, j <> i -> j <> k -> M1.[j] = M2.[j]) ->
      M1.[i] = M2.[k] -> M1.[k] = M2.[i] ->
      (|M1| = - |M2|)%A.
  Proof.
    intros. destruct (i ??< k).
    - apply mdet_row_swap_lt with (i:=i)(k:=k); auto.
    - apply mdet_row_swap_lt with (i:=k)(k:=i); auto.
      assert (fin2nat i <> fin2nat k). fin2nat; auto. lia.
  Qed.
  
  (* Property 4: 两行互换，行列式反号 (用 mrowSwap 描述的版本) *)
  Lemma mdet_row_mrowSwap : forall {n} (M : smat n) (i k : 'I_n),
      i <> k -> (|mrowSwap i k M| = - |M|)%A.
  Proof.
    intros. unfold mrowSwap.
    apply mdet_row_swap with (i:=i) (k:=k); auto; intros; fin.
  Qed.

  Section Field.
    Context `{HField : Field tA Aadd Azero Aopp Amul Aone}.
    Context {AeqDec : Dec (@eq tA)}.
    
    (**
       WE ASSUME the field is not F2, i.e. {0,1},
       because we mainly use a numerical field.

       SO, WE ASSUME THIS AXIOM HERE. *)
    Axiom two_neq0 : (1 + 1)%A <> 0.
    
    (* Property 5: 两行相同，行列式的值为 0 *)
    Lemma mdet_row_same_eq0 : forall {n} (M : smat n) (i j : 'I_n),
        i <> j -> M.[i] = M.[j] -> |M| = 0.
    Proof.
      intros.
      assert (|M| = -|M|). apply (mdet_row_swap M M i j); auto.
      apply group_sub_eq0_iff_eq in H1.
      rewrite group_opp_opp in H1.
      replace (|M|) with (1 * |M|)%A in H1 by ring.
      rewrite <- distrRight in H1.
      rewrite field_mul_eq0_iff in H1. destruct H1; auto.
      (* 1 + 1 <> 0 *)
      apply two_neq0 in H1. easy.
    Qed.

    (* When i-th row is replaced with j-th row (i <> j), |M| = 0 *)
    Corollary mdet_row_vset_eq0 : forall {n} (M : smat n) (i j : 'I_n),
        i <> j -> |vset M i (M j)| = 0.
    Proof.
      intros. apply (mdet_row_same_eq0 _ i j); auto.
      rewrite vnth_vset_eq, vnth_vset_neq; auto.
    Qed.
    
    (* Property 6: 两行成比例，行列式的值为 0 *)
    Lemma mdet_row_scal : forall {n} (M : smat n) (i j : 'I_n) (x : tA),
        i <> j -> M.[i] = (x s* M.[j])%A -> |M| = 0.
    Proof.
      intros. rewrite (mdet_row_scale M (vset M i M.[j]) i x).
      - pose proof (mdet_row_vset_eq0 M i j H). rewrite H1. ring.
      - intros k Hk. bdestruct (i =? k); fin.
        rewrite vnth_vset_neq; auto.
      - rewrite vnth_vset_eq; auto.
    Qed.

    (* When i-th row is replaced with (x * j-th row) (i <> j), |M| = 0 *)
    Corollary mdet_row_vset_scal_eq0 : forall {n} (M : smat n) (i j : 'I_n) x,
        i <> j -> |vset M i (x s* M j)| = 0.
    Proof.
      intros.
      pose proof (mdet_row_scal (vset M i (x s* M j)) i j x H).
      rewrite vnth_vset_eq, vnth_vset_neq in H0; auto.
    Qed.
    
    (* Property 7: 一行的倍数加到另一行，行列式的值不变 *)
    Lemma mdet_row_addRow : forall {n} (M1 M2 : smat n) (i j : 'I_n) (x : tA),
        i <> j ->
        (forall k, k <> i -> M1.[k] = M2.[k]) ->
        M1.[i] = (M2.[i] + x s*M2.[j])%V -> |M1| = |M2|.
    Proof.
      intros.
      pose proof (mdet_row_add M2 (vset M2 i (x s* M2.[j])) M1 i).
      rewrite H2; auto.
      - rewrite (mdet_row_vset_scal_eq0); auto. ring.
      - intros k Hk. rewrite H0; auto. split; auto.
        rewrite vnth_vset_neq; auto.
      - rewrite vnth_vset_eq. auto.
    Qed.
    
  End Field.

  (* If we have a field structure *)
  Section Field.
    Context `{HField : Field tA Aadd 0 Aopp Amul 1}.
    Add Field field_inst : (make_field_theory HField).
    
    (** M * N = mat1 -> |M| <> 0 *)
    Lemma mmul_eq1_imply_mdet_neq0_l : forall {n} (M N : smat n),
        M * N = mat1 -> |M| <> 0.
    Proof.
      intros. assert(|M * N|=|@mat1 n|). rewrite H; auto.
      rewrite mdet_mmul in H0. intro. rewrite H1 in H0. rewrite mdet_mat1 in H0.
      ring_simplify in H0. apply field_1_neq_0; auto.
    Qed.

    (** M * N = mat1 -> |N| <> 0 *)
    Lemma mmul_eq1_imply_mdet_neq0_r : forall {n} (M N : smat n),
        M * N = mat1 -> |N| <> 0.
    Proof.
      intros. assert(|M * N|=|@mat1 n|). rewrite H; auto.
      rewrite mdet_mmul in H0. intro. rewrite H1 in H0. rewrite mdet_mat1 in H0.
      ring_simplify in H0. apply field_1_neq_0; auto.
    Qed.
  End Field.
  
End mdet.


(* ======================================================================= *)
(** ** Determinant on concrete dimensions *)
Section mdet_concrete.
  Context `{HARing : ARing}.
  Add Ring ring_inst : (make_ring_theory HARing).

  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + -b).
  Infix "-" := Asub : A_scope.
  Infix "*" := Amul : A_scope.

  Notation mdet := (@mdet _ Aadd 0 Aopp Amul 1).

  (** Determinant of a matrix of dimension-1 *)
  Definition mdet1 (M : smat tA 1) := M.11.

  (** mdet1 M = |M| *)
  Lemma mdet1_eq_mdet : forall M, mdet1 M = mdet M.
  Proof. intros. cbv. ring. Qed.
  
  (** |M| <> 0 <-> mdet_exp <> 0 *)
  Lemma mdet1_neq0_iff : forall (M : smat tA 1),
      mdet M <> 0 <-> M.11 <> 0.
  Proof. intros. rewrite <- mdet1_eq_mdet; easy. Qed.

  (** Determinant of a matrix of dimension-2 *)
  Definition mdet2 (M : smat tA 2) := (M.11*M.22 - M.12*M.21)%A.

  (** mdet2 M = |M| *)
  Lemma mdet2_eq_mdet : forall M, mdet2 M = mdet M.
  Proof. intros. unfold mdet2. cbn; rewrite <- !(nth_m2f_nat2finS 0); auto; ring. Qed.

  (** |M| <> 0 <-> mdet_exp <> 0 *)
  Lemma mdet2_neq0_iff : forall (M : smat tA 2),
      mdet M <> 0 <-> (M.11*M.22 - M.12*M.21)%A <> 0.
  Proof. intros. rewrite <- mdet2_eq_mdet; easy. Qed.

  (** Determinant of a matrix of dimension-3 *)
  Definition mdet3 (M : smat tA 3) :=
    (M.11 * M.22 * M.33 - M.11 * M.23 * M.32 - 
       M.12 * M.21 * M.33 + M.12 * M.23 * M.31 + 
       M.13 * M.21 * M.32 - M.13 * M.22 * M.31)%A.

  (** mdet3 M = mdet M *)
  Lemma mdet3_eq_mdet : forall M, mdet3 M = mdet M.
  Proof. intros. unfold mdet3. cbn; rewrite <- !(nth_m2f_nat2finS 0); auto; ring. Qed.
  
  (** |M| <> 0 <-> mdet_exp <> 0 *)
  Lemma mdet3_neq0_iff : forall (M : smat tA 3),
      mdet M <> 0 <->
        (M.11 * M.22 * M.33 - M.11 * M.23 * M.32 - 
           M.12 * M.21 * M.33 + M.12 * M.23 * M.31 + 
           M.13 * M.21 * M.32 - M.13 * M.22 * M.31)%A <> 0.
  Proof. intros. rewrite <- mdet3_eq_mdet; easy. Qed.

  (** Determinant of a matrix of dimension-4 *)
  Definition mdet4 (M : smat tA 4) :=
    (M.11*M.22*M.33*M.44 - M.11*M.22*M.34*M.43 -
       M.11*M.23*M.32*M.44 + M.11*M.23*M.34*M.42 +
       M.11*M.24*M.32*M.43 - M.11*M.24*M.33*M.42 -
       M.12*M.21*M.33*M.44 + M.12*M.21*M.34*M.43 +
       M.12*M.23*M.31*M.44 - M.12*M.23*M.34*M.41 -
       M.12*M.24*M.31*M.43 + M.12*M.24*M.33*M.41 +
       M.13*M.21*M.32*M.44 - M.13*M.21*M.34*M.42 -
       M.13*M.22*M.31*M.44 + M.13*M.22*M.34*M.41 +
       M.13*M.24*M.31*M.42 - M.13*M.24*M.32*M.41 -
       M.14*M.21*M.32*M.43 + M.14*M.21*M.33*M.42 +
       M.14*M.22*M.31*M.43 - M.14*M.22*M.33*M.41 -
       M.14*M.23*M.31*M.42 + M.14*M.23*M.32*M.41)%A.

  (** mdet4 M = mdet M *)
  Lemma mdet4_eq_mdet : forall M, mdet4 M = mdet M.
  Proof. intros. unfold mdet4. cbn; rewrite <- !(nth_m2f_nat2finS 0); auto; ring. Qed.
  
  (** |M| <> 0 <-> mdet_exp <> 0 *)
  Lemma mdet4_neq0_iff : forall (M : smat tA 4),
      mdet M <> 0 <->
        (M.11*M.22*M.33*M.44 - M.11*M.22*M.34*M.43 -
           M.11*M.23*M.32*M.44 + M.11*M.23*M.34*M.42 +
           M.11*M.24*M.32*M.43 - M.11*M.24*M.33*M.42 -
           M.12*M.21*M.33*M.44 + M.12*M.21*M.34*M.43 +
           M.12*M.23*M.31*M.44 - M.12*M.23*M.34*M.41 -
           M.12*M.24*M.31*M.43 + M.12*M.24*M.33*M.41 +
           M.13*M.21*M.32*M.44 - M.13*M.21*M.34*M.42 -
           M.13*M.22*M.31*M.44 + M.13*M.22*M.34*M.41 +
           M.13*M.24*M.31*M.42 - M.13*M.24*M.32*M.41 -
           M.14*M.21*M.32*M.43 + M.14*M.21*M.33*M.42 +
           M.14*M.22*M.31*M.43 - M.14*M.22*M.33*M.41 -
           M.14*M.23*M.31*M.42 + M.14*M.23*M.32*M.41)%A <> 0.
  Proof. intros. rewrite <- mdet4_eq_mdet. easy. Qed.
End mdet_concrete.


(* ############################################################################ *)
(** * Cofactor expansion of the determinant *)
Section mdetEx.
  Context `{HARing : ARing}.
  Add Ring ring_inst : (make_ring_theory HARing).

  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.

  Notation vsum := (@vsum _ Aadd 0).
  Notation vdot := (@vdot _ Aadd 0 Amul).
  Notation vzero := (vzero 0).
  
  Notation mat r c := (mat tA r c).
  Notation smat n := (smat tA n).
  Notation madd := (@madd _ Aadd).
  Infix "+" := madd : mat_scope.
  Notation mdet := (@mdet _ Aadd 0 Aopp Amul 1).
  Notation "| M |" := (mdet M) : mat_scope.

  (* ======================================================================= *)
  (** ** sub-matrix  子矩阵 *)

  (* sub-matrix by nat-indexing-function, which is used for proof *)
  Definition msubmatNat (M : nat -> nat -> tA) (i j : nat) : nat -> nat -> tA :=
    fun i0 j0 =>
      M (if i0 ??< i then i0 else S i0) (if j0 ??< j then j0 else S j0).

  (** sub-matrix of M by remove i-th row and j-th column *)
  
  (* OLD IMPLEMENTATION, deprecated *)
  Definition msubmat' {n} (M : smat (S n)) (i j : 'I_(S n)) : smat n :=
    fun i0 j0 =>
      let i1 := if i0 ??< i then fSuccRange i0 else fSuccRangeS i0 in
      let j1 := if j0 ??< j then fSuccRange j0 else fSuccRangeS j0 in
      M.[i1].[j1].

  Definition msubmat {n} (M : smat (S n)) (i j : 'I_(S n)) : smat n :=
    fun i0 j0 =>
      let i1 := if i0 ??< i then #i0 else #(S i0) in
      let j1 := if j0 ??< j then #j0 else #(S j0) in
      M.[i1].[j1].

  (** msubmat (msetr M a j) i j = msubmat M i j *)
  Lemma msubmat_msetr : forall {n} (M : smat (S n)) (a : vec (S n)) (i j : 'I_(S n)),
      msubmat (msetr M a i) i j = msubmat M i j.
  Proof. intros. apply meq_iff_mnth; intros. unfold msubmat. unfold msetr. fin. Qed.

  (** msubmat (msetc M a j) i j = msubmat M i j *)
  Lemma msubmat_msetc : forall {n} (M : smat (S n)) (a : vec (S n)) (i j : 'I_(S n)),
      msubmat (msetc M a j) i j = msubmat M i j.
  Proof. intros. apply meq_iff_mnth; intros. unfold msubmat. unfold msetc. fin. Qed.
  
  Lemma msubmat_eq_msubmatNat : forall {n} (M : smat (S n)) (i j : 'I_(S n)),
      msubmat M i j = @f2m _ n n (msubmatNat (m2f 0 M) i j).
  Proof.
    intros. unfold msubmat, msubmatNat. apply meq_iff_mnth; intros.
    rewrite mnth_f2m.
    destruct i0,j0,i,j; simpl.
    assert ((if i0 ??< i then i0 else S i0) < S n) as Hi.
    { destruct (_??<_). lia. lia. }
    assert ((if i1 ??< i2 then i1 else S i1) < S n) as Hj.
    { destruct (i1 ??< i2). lia. lia. }
    rewrite nth_m2f with (Hi:=Hi)(Hj:=Hj). f_equal.
    - assert (i0 < S n) by lia. rewrite nat2finS_eq with (E:=H).
      assert (S i0 < S n) by lia. rewrite nat2finS_eq with (E:=H0). fin.
    - assert (i1 < S n) by lia. rewrite nat2finS_eq with (E:=H).
      assert (S i1 < S n) by lia. rewrite nat2finS_eq with (E:=H0). fin.
  Qed.

  (* ======================================================================= *)
  (** ** minor of matrix  余子式，余因式，余因子展开式 *)

  (** (i,j) minor of M *)
  Definition mminor {n} (M : smat (S n)) (i j : 'I_(S n)) : tA := |msubmat M i j|.

  (** minor(M\T,i,j) = minor(M,j,i) *)
  Lemma mminor_mtrans : forall {n} (M : smat (S n)) (i j : 'I_(S n)),
      mminor (M\T) i j = mminor M j i.
  Proof. intros. unfold mminor. rewrite <- mdet_mtrans. auto. Qed.

  (** mminor (msetr M a i) i j = mminor M i j *)
  Lemma mminor_msetr : forall {n} (M : smat (S n)) (a : vec (S n)) (i j : 'I_(S n)),
      mminor (msetr M a i) i j = mminor M i j.
  Proof. intros. unfold mminor. rewrite msubmat_msetr. auto. Qed.
  
  (** mminor (msetc M a j) i j = mminor M i j *)
  Lemma mminor_msetc : forall {n} (M : smat (S n)) (a : vec (S n)) (i j : 'I_(S n)),
      mminor (msetc M a j) i j = mminor M i j.
  Proof. intros. unfold mminor. rewrite msubmat_msetc. auto. Qed.


  Definition mminorNat {n:nat} (M : nat -> nat -> tA) (i j : nat) : tA :=
    mdet (@f2m _ n n (msubmatNat M i j)).
  
  Lemma mminor_eq_mminorNat : forall {n} (M : smat (S n)) (i j : 'I_(S n)),
      mminor M i j = @mminorNat n (m2f 0 M) i j.
  Proof.
    intros. unfold mminor, mminorNat. rewrite msubmat_eq_msubmatNat. auto.
  Qed.
  
  
  (* ======================================================================= *)
  (** ** cofactor of matrix  代数余子式 *)

  (** (i,j) cofactor of M *)
  Definition mcofactor {n} (M : smat (S n)) (i j : 'I_(S n)) : tA :=
    let x := mminor M i j in
    if Nat.even (i + j) then x else - x.

  (** A(M\T,i,j) = A(M,j,i) *)
  Lemma mcofactor_mtrans : forall {n} (M : smat (S n)) (i j : 'I_(S n)),
      mcofactor (M\T) i j = mcofactor M j i.
  Proof.
    intros. unfold mcofactor. rewrite mminor_mtrans. rewrite Nat.add_comm. auto.
  Qed.

  (** mcofactor (msetr M a i) i j = mcofactor M i j *)
  Lemma mcofactor_msetr : forall {n} (M : smat (S n)) (a : vec (S n)) (i j : 'I_(S n)),
      mcofactor (msetr M a i) i j = mcofactor M i j.
  Proof. intros. unfold mcofactor. rewrite mminor_msetr. auto. Qed.

  (** mcofactor (msetc M a j) i j = mcofactor M i j *)
  Lemma mcofactor_msetc : forall {n} (M : smat (S n)) (a : vec (S n)) (i j : 'I_(S n)),
      mcofactor (msetc M a j) i j = mcofactor M i j.
  Proof. intros. unfold mcofactor. rewrite mminor_msetc. auto. Qed.

  
  (* ======================================================================= *)
  (** ** cofactor matrix (matrix of cofactors) 代数余子阵 *)

  (** cofactor matrix of M *)
  (* Definition mcomat {n} (M : smat (S n)) : smat (S n) := fun i j => mcofactor M i j. *)


  (* ======================================================================= *)
  (** **  Cofactor expansion of the determinant (Laplace expansion) *)

  (** Cofactor expansion of `M` along the i-th row *)
  Definition mdetExRow {n} : smat n -> 'I_n -> tA :=
    match n with
    | O => fun _ _ => 1
    | S n' => fun M i => vsum (fun j => M.[i].[j] * mcofactor M i j)
    end.

  (** Cofactor expansion of `M` along the j-th column *)
  Definition mdetExCol {n} : smat n -> 'I_n -> tA :=
    match n with
    | O => fun _ _ => 1
    | S n' => fun M j => vsum (fun i => M.[i].[j] * mcofactor M i j)
    end.

  (** row_expansion (M\T, i) = col_expansion (M, i) *)
  Lemma mdetExRow_mtrans : forall {n} (M : smat n) (i : 'I_n),
      mdetExRow (M \T) i = mdetExCol M i.
  Proof.
    intros. unfold mdetExRow, mdetExCol. destruct n; auto.
    apply vsum_eq; intros. rewrite mcofactor_mtrans, mnth_mtrans. auto.
  Qed.

  (** col_expansion (M\T, i) = row_expansion (M, i) *)
  Lemma mdetExCol_mtrans : forall {n} (M : smat n) (i : 'I_n),
      mdetExCol (M \T) i = mdetExRow M i.
  Proof. intros. rewrite <- mdetExRow_mtrans. auto. Qed.

  (** Cofactor expansion by row is equivalent to full expansion *)
  Lemma mdetExRow_eq_mdet : forall {n} (M : smat n) (i : 'I_n), mdetExRow M i = mdet M.
  Proof.
    intros. destruct n. cbv; ring.
    unfold mdetExRow, mdet in *.
  Admitted.

  (** Cofactor expansion by column is equivalent to full expansion *)
  Lemma mdetExCol_eq_mdet : forall {n} (M : smat n) (j : 'I_n), mdetExCol M j = mdet M.
  Proof.
    intros.
    pose proof(mdetExRow_eq_mdet (M\T) j).
    rewrite mdet_mtrans in H. rewrite <- H.
    rewrite mdetExRow_mtrans. auto.
  Qed.

  (** Cofactor expansion by row is equivalent to cofactor expansion by column *)
  Lemma mdetExRow_eq_mdetExCol : forall {n} (M : smat n) (i : 'I_n),
      mdetExRow M i = mdetExCol M i.
  Proof. intros. rewrite mdetExRow_eq_mdet, mdetExCol_eq_mdet. auto. Qed.

  (**     [r11 r12 r13 | v1]       [r11 r12 r13]
      det [r21 r22 r23 | v2] = det [r21 r22 r23]
          [r31 r32 r33 | v3]       [r31 r32 r33]
          [  0   0   0 |  1] *)
  Lemma mdet_mconsrT_vconsT_vzero_1_eq : forall {n} (A : mat n (S n)),
  |mconsrT A (vconsT vzero Aone)| = |mremovecT A|.
  Proof.
  Admitted.
  

  Section Field.
    Context `{HField: Field tA Aadd Azero Aopp Amul Aone}.
    Context {AeqDec: Dec (@eq tA)}.
    
    (** < i-th row, cofactor of k-th row > = 0 (if i <> k) *)
    Lemma vdot_mcofactor_row_diff_eq0 : forall {n} (M : smat (S n)) (i k : 'I_(S n)),
        i <> k -> vdot (M.[i]) (fun j => mcofactor M k j) = 0.
    Proof.
      intros.
      (* B矩阵按第 k 行展开就是当前的目标 *)
      pose (msetr M (M.[i]) k) as B.
      pose proof (mdetExRow_eq_mdet B k).
      assert (mdetExRow B k = vdot M.[i] (fun j => mcofactor M k j)).
      - unfold mdetExRow. unfold vdot.
        apply vsum_eq; intros.
        rewrite vnth_vmap2. unfold B.
        rewrite mnth_msetr_same; auto. f_equal.
        unfold mcofactor.
        destruct (Nat.even (k + i0)) eqn:H1.
        + unfold mminor. f_equal. apply meq_iff_mnth; intros.
          unfold msubmat. unfold msetr. fin.
        + f_equal. unfold mminor. f_equal. apply meq_iff_mnth; intros.
          unfold msubmat. unfold msetr. fin.
      - rewrite <- H1. unfold B.
        rewrite mdetExRow_eq_mdet.
        apply (mdet_row_same_eq0 _ i k); auto.
        apply veq_iff_vnth; intros.
        rewrite mnth_msetr_diff; auto.
        rewrite mnth_msetr_same; auto.
    Qed.
    
    (** < j-th column, cofactor of l-column row > = 0 (if j <> l) *)
    Lemma vdot_mcofactor_col_diff_eq0 : forall {n} (M : smat (S n)) (j l : 'I_(S n)),
        j <> l -> vdot (M&[j]) (fun i => mcofactor M i l) = 0.
    Proof.
      intros. pose proof (vdot_mcofactor_row_diff_eq0 (M\T) j l H).
      rewrite <- H0 at 2. f_equal. apply veq_iff_vnth; intros.
      rewrite mcofactor_mtrans. auto.
    Qed.
  End Field.

  (** < i-th row, cofactor of i-th row > = |M| *)
  Lemma vdot_mcofactor_row_same_eq_det : forall {n} (M : smat (S n)) (i : 'I_(S n)),
      vdot (M.[i]) (fun j => mcofactor M i j) = |M|.
  Proof. intros. rewrite <- mdetExRow_eq_mdet with (i:=i). auto. Qed.

  (** < j-th column, cofactor of j-th column > = |M| *)
  Lemma vdot_mcofactor_col_same_eq_det : forall {n} (M : smat (S n)) (j : 'I_(S n)),
      vdot (M&[j]) (fun i => mcofactor M i j) = |M|.
  Proof. intros. rewrite <- mdetExCol_eq_mdet with (j:=j). auto. Qed.

  (** Cofactor expansion of `M` along the 0-th row *)
  (* Note that, it is not simply use `mdetExRow`, but a recursively definition *)
  Fixpoint mdetEx {n} : smat n -> tA :=
    match n with
    | O => fun M => 1
    | S n' =>
        fun M => 
          vsum (fun j =>
                  let a := if Nat.even j
                           then (M.[#0].[j])
                           else (-(M.[#0].[j]))%A in
                  let d := mdetEx (msubmat M #0 j) in
                  a * d)
    end.

  (** mdetEx is equal to mdetExRow along 0-th row  *)
  Lemma mdetEx_eq_mdetExRow_0 : forall {n} (M : smat (S n)),
      mdetEx M = mdetExRow M #0.
  Proof.
    induction n; intros.
    - cbv. rewrite <- (nth_m2f 0). ring.
    - unfold mdetEx, mdetExRow; fold (@mdetEx n).
      apply vsum_eq; intros.
      specialize (IHn (msubmat M #0 i)) as H.
      unfold mdetEx, mdetExRow in H; fold (@mdetEx n) in H. rewrite H; clear H.
      destruct (Nat.even i) eqn:H1.
      + f_equal.
        unfold mcofactor; simpl. rewrite H1. unfold mminor at 3.
        rewrite <- (mdetExRow_eq_mdet _ #0).
        unfold mdetExRow. apply vsum_eq; intros. auto.
      + unfold mcofactor; simpl. rewrite H1. ring_simplify. f_equal.
        unfold mminor at 3.
        rewrite <- (mdetExRow_eq_mdet _ #0).
        unfold mdetExRow. apply vsum_eq; intros. auto.
  Qed.
  
  (** mdetEx is equal to mdet *)
  Lemma mdetEx_eq_mdet : forall {n} (M : smat n), mdetEx M = mdet M.
  Proof.
    intros. destruct n.
    - cbv. ring.
    - rewrite mdetEx_eq_mdetExRow_0. rewrite mdetExRow_eq_mdet. auto.
  Qed.


  (* 证明 mdetEx M = mdet M 的等式。由于 cbv 会展开太多，可手动控制 mdet 的展开 *)
  Ltac mdetEx_eq_mdet :=
    match goal with
    | |- mdetEx ?M = mdet ?M =>
        let HeqM := fresh "HeqM" in
        (* 计算左侧的 mdetEx *)
        remember (mdet M) eqn: HeqM; cbv; rewrite <- !(nth_m2f 0);
        (* 快速展开 mdet *)
        rewrite HeqM; unfold mdet; simpl;
        (* 完成证明 *)
        try ring
    end.
  
  Example mdetEx_eq_mdet_1 : forall (M : smat 1), mdetEx M = mdet M.
  Proof. intros. mdetEx_eq_mdet. Qed.

  Example mdetEx_eq_mdet_2 : forall (M : smat 2), mdetEx M = mdet M.
  Proof. intros. mdetEx_eq_mdet. Qed.

  Example mdetEx_eq_mdet_3 : forall (M : smat 3), mdetEx M = mdet M.
  Proof. intros. mdetEx_eq_mdet. Qed.
        
  Example mdetEx_eq_mdet_4 : forall (M : smat 4), mdetEx M = mdet M.
  Proof.
    intros.
    (* 如果直接展开，则需要 1.5 s；而手动展开只需要 0.5s *)
    (* Time cbv; rewrite <- !(nth_m2f 0); ring. *)
    (* Time *)
      mdetEx_eq_mdet.
  Qed.


  (* ======================================================================= *)
  (** ** cofactor of matrix (Expansion version)  代数余子式(行列式为展开形式的版本) *)

  (** (i,j) cofactor of matrix M (按第一行展开来计算行列式的版本) *)
  Definition mcofactorEx {n} (M : smat (S n)) (i j : 'I_(S n)) : tA :=
    let x := mdetEx (msubmat M i j) in
    if Nat.even (i + j) then x else - x.

  (** mcofactorEx is equal to mcofactor *)
  Lemma mcofactorEx_eq_mcofactor : forall {n} (M : smat (S n)) (i j : 'I_(S n)),
      mcofactorEx M i j = mcofactor M i j.
  Proof.
    intros. unfold mcofactorEx, mcofactor. unfold mminor.
    rewrite <- mdetEx_eq_mdet. auto.
  Qed.

End mdetEx.


(* ############################################################################ *)
(** * Adjoint Matrix *)
Section madj.
  Context `{HField : Field} {HAeqDec : Dec (@eq tA)}.
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

  Notation vec n := (@vec tA n).
  Notation vsum := (@vsum _ Aadd 0).

  Notation smat n := (smat tA n).
  Notation mat1 := (@mat1 _ 0 1).
  Notation mscal := (@mscal _ Amul).
  Infix "s*" := mscal : mat_scope.
  Notation mmul := (@mmul _ Aadd 0 Amul).
  Infix "*" := mmul : mat_scope.
  Notation mmulv := (@mmulv _ Aadd 0 Amul).
  Infix "*v" := mmulv : mat_scope.
  Notation mdet := (@mdet _ Aadd 0 Aopp Amul 1).
  Notation "| M |" := (mdet M) : mat_scope.
  Notation mcofactor := (@mcofactor _ Aadd 0 Aopp Amul 1).

  Notation mdetEx := (@mdetEx _ Aadd 0 Aopp Amul 1).
  Notation mcofactorEx := (@mcofactorEx _ Aadd 0 Aopp Amul 1).
  
  (* ======================================================================= *)
  (** ** Adjoint matrix (Adjugate matrix, adj(A), A* ) *)
  
  (** Adjoint matrix *)
  Definition madj {n} : smat n -> smat n := 
    match n with
    | O => fun M => M 
    | S n' => fun M i j => mcofactor M j i
    end.
  Notation "M \A" := (madj M) : mat_scope.

  (* (** (M\A).[i].[j] = (-1)^(i+j) * det(submat M i j) *) *)
  (* Lemma mnth_madj : forall {n} (M : smat (S n)) i j, *)
  (*     (M\A).[i].[j] = (madjSign i j * mdetEx (mminor M j i))%A. *)
  (* Proof. intros. auto. Qed. *)
  
  (* (** (madj M) $ i $ j = (mcofactor M) $ j $ i. *) *)
  (* Lemma mnth_madj_eq_mnth_mcofactor_swap : forall {n} (M : smat n) i j, *)
  (*     (M\A).[i].[j] = (mcofactor M).[j].[i]. *)
  (* Proof. *)
  (*   intros. destruct n. *)
  (*   - exfalso. apply fin0_False; auto. *)
  (*   - simpl. f_equal. apply madjSign_comm. *)
  (* Qed. *)

  (* (** (M\A)\T = mcofactor M *) *)
  (* Lemma mtrans_madj : forall {n} (M : smat n), (M\A)\T = mcofactor M. *)
  (* Proof. *)
  (*   intros. apply meq_iff_mnth; intros. rewrite mnth_mtrans. *)
  (*   apply mnth_madj_eq_mnth_mcofactor_swap. *)
  (* Qed. *)

  (* (** (mcofactor M)\T = madj M *) *)
  (* Lemma mtrans_mcofactor : forall {n} (M : smat n), (mcofactor M)\T = M\A. *)
  (* Proof. intros. rewrite <- mtrans_madj, mtrans_mtrans. auto. Qed. *)

  (** M * (M\A) = |M| * I *)
  Lemma mmul_madj_r : forall {n} (M : smat n), M * M\A = |M| s* mat1.
  Proof.
    intros. apply meq_iff_mnth; intros.
    unfold madj. destruct n. fin.
    rewrite mnth_mmul. unfold mcol.
    destruct (i ??= j) as [E|E].
    - fin2nat. subst.
      rewrite vdot_mcofactor_row_same_eq_det.
      rewrite mnth_mscal. rewrite mnth_mat1_same; auto. ring.
    - fin2nat.
      rewrite (vdot_mcofactor_row_diff_eq0 M i j); auto.
      rewrite mnth_mscal. rewrite mnth_mat1_diff; auto. ring.
  Qed.

  (** (M\A) * M = |M| * I *)
  Lemma mmul_madj_l : forall {n} (M : smat n), M\A * M = |M| s* mat1.
  Proof.
    intros. apply meq_iff_mnth; intros.
    unfold madj. destruct n. fin.
    rewrite mnth_mmul. rewrite vdot_comm.
    destruct (i ??= j) as [E|E].
    - fin2nat. subst.
      rewrite vdot_mcofactor_col_same_eq_det.
      rewrite mnth_mscal. rewrite mnth_mat1_same; auto. ring.
    - fin2nat.
      rewrite (vdot_mcofactor_col_diff_eq0 M j i); auto.
      rewrite mnth_mscal. rewrite mnth_mat1_diff; auto. ring.
  Qed.
  
  (** (/|M| .* M\A) * M = mat1 *)
  Lemma mmul_det_scal_adj_l : forall {n} (M : smat n),
  |M| <> 0 -> (/|M| s* M\A) * M = mat1.
  Proof.
    intros. rewrite mmul_mscal_l. rewrite mmul_madj_l. rewrite mscal_assoc.
    rewrite field_mulInvL; auto. apply mscal_1_l.
  Qed.

  (** M * (/|M| .* M\A) = mat1 *)
  Lemma mmul_det_scal_adj_r : forall {n} (M : smat n),
  |M| <> 0 -> M * (/|M| s* M\A) = mat1.
  Proof.
    intros. rewrite mmul_mscal_r. rewrite mmul_madj_r. rewrite mscal_assoc.
    rewrite field_mulInvL; auto. apply mscal_1_l.
  Qed.  

  (** |M| <> 0 -> (exists N : smat n, N * M = mat1) *)
  Lemma mdet_neq0_imply_mmul_eq1_l : forall {n} (M : smat n),
  |M| <> 0 -> (exists N : smat n, N * M = mat1).
  Proof. intros. exists (/|M| s* M\A). apply mmul_det_scal_adj_l. auto. Qed.

  (** |M| <> 0 -> (exists N : smat n, M * N = mat1) *)
  Lemma mdet_neq0_imply_mmul_eq1_r : forall {n} (M : smat n),
  |M| <> 0 -> (exists N : smat n, M * N = mat1).
  Proof. intros. exists (/|M| s* M\A). apply mmul_det_scal_adj_r. auto. Qed.

  (** |M| <> 0 -> (exists N : smat n, N * M = mat1 /\ M * N = mat1) *)
  Lemma mdet_neq0_imply_mmul_eq1 : forall {n} (M : smat n),
  |M| <> 0 -> (exists N : smat n, N * M = mat1 /\ M * N = mat1).
  Proof.
    intros. exists (/|M| s* M\A). split.
    apply mmul_det_scal_adj_l. auto.
    apply mmul_det_scal_adj_r. auto.
  Qed.


  (* ======================================================================= *)
  (** ** Cramer rule *)

  (** Cramer rule, which can solve the equation with the form of A*x=b.
      Note, the result is valid only when |B| is not zero *)
  Definition cramerRule {n} (A : smat n) (b : vec n) : vec n :=
    fun i => |msetc A b i| / |A|.

  (** A *v (cramerRule A b) = b, (The dimension is `S n`) *)
  Lemma cramerRule_eq_S : forall {n} (A : smat (S n)) (b : vec (S n)),
  |A| <> 0 -> A *v (cramerRule A b) = b.
  Proof.
    intros. unfold cramerRule.
    remember (msetc A b) as C. apply veq_iff_vnth; intros.
    rewrite vnth_mmulv. unfold vdot. unfold vmap2.
    rewrite vsum_eq with (b:=fun j => (/|A| * (A.[i].[j] * |C j|))%A).
    2:{ intros. field. auto. }
    rewrite <- vsum_scal_l.
    rewrite vsum_eq
      with (b:=fun j => (vsum (fun k => A.[i].[j] * (b.[k] * mcofactor A k j)))%A).
    2:{ intros j. rewrite <- vsum_scal_l. f_equal.
        rewrite <- (mdetExCol_eq_mdet _ j). unfold mdetExCol.
        apply vsum_eq; intros k. rewrite HeqC.
        rewrite mnth_msetc_same; auto. f_equal.
        rewrite mcofactor_msetc. auto. }
    rewrite vsum_eq
      with (b:=fun j=> vsum (fun k=> (A.[i].[j] * b.[k] * mcofactor A k j)%A)).
    2:{ intros j. apply vsum_eq; intros k. ring. }
    rewrite vsum_vsum.
    rewrite vsum_eq
      with (b:=fun k=> (b.[k] * vsum (fun j=> A.[i].[j] * mcofactor A k j))%A).
    2:{ intros j. rewrite vsum_scal_l. apply vsum_eq; intros k. ring. }
    (* `vsum` has only one value when k = i *)
    rewrite vsum_unique with (i:=i) (x:=(|A| * b.[i])%A).
    - field; auto.
    - pose proof (vdot_mcofactor_row_same_eq_det A i).
      unfold vdot in H0. unfold vmap2 in H0. rewrite H0. ring.
    - intros.
      pose proof (vdot_mcofactor_row_diff_eq0 A i j H0).
      unfold vdot in H1. unfold vmap2 in H1. rewrite H1. ring.
  Qed.

  (** A *v (cramerRule A b) = b *)
  Lemma cramerRule_spec : forall {n} (A : smat n) (b : vec n),
  |A| <> 0 -> A *v (cramerRule A b) = b.
  Proof.
    intros. destruct n.
    - cbv. apply v0eq.
    - apply cramerRule_eq_S. auto.
  Qed.

  (** Cramer rule over list *)
  Definition cramerRuleList (n : nat) (lA : dlist tA) (lb : list tA) : list tA :=
    let A : smat n := l2m 0 lA in
    let b : vec n := l2v 0 lb in
    let x := cramerRule A b in
    v2l x.

  (** length (cramerRuleList n lA lb) = n *)
  Lemma cramerRuleList_length : forall (n : nat) (lA : dlist tA) (lb : list tA),
      length (cramerRuleList n lA lb) = n.
  Proof. intros. unfold cramerRuleList. rewrite v2l_length. auto. Qed.

  (** {cramerRuleList lA lb} = cramerRule {lA} {lb} *)
  Lemma cramerRuleList_spec : forall n (lA : dlist tA) (lb : list tA),
      let A : smat n := l2m 0 lA in
      let b : vec n := l2v 0 lb in
      l2v 0 (cramerRuleList n lA lb) = cramerRule A b.
  Proof. intros. unfold cramerRuleList. rewrite l2v_v2l. auto. Qed.
  
End madj.
