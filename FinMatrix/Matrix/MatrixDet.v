(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Determinant of matrix
  author    : ZhengPu Shi
  date      : 2023.06

  motivation :
  1. 数域K上n个方程的n元线性方程组有唯一解 <==> n阶行列式(n级矩阵的行列式)非零。
  2. 行列式在几何、分析等数学分支中也有重要应用。

  remark    :
  1. compute permutation of a list, such as 
     perm [a;b;c] => [[a;b;c]; [a;c;b]; [b;a;c]; [b;c;a]; [c;a;b]; [c;b;a]]
     perm [1;2;3] => [[1;2;3]; [1;3;2]; [2;1;3]; [2;3;1]; [3;1;2]; [3;2;1]]
  2. 行列式问题

     行列式的定义：它是一个单项式的求和，每个单项式是矩阵中不同行不同列元素的乘积，并
     冠以逆序数。

     二级矩阵
        A = [[a11;a12]; [a21;a22]]
        det(A) = a11*a22 + -(a12*a21)
               = a11*det[[a22]] + (-a12)*det[[a21]]  按第1行展开
               = (-a21)*det[[a12]] + a22*det[[a11]]  按第2行展开
               = a11*det[[a22]] + (-a21)*det[[a12]]  按第1列展开
               = (-a12)*det[[a21]] + a22*det[[a11]]  按第2列展开
     三级矩阵
        A = [[a11;a12;a13]; [a21;a22;a23]; [a31;a32;a33]]，
        det(A) = a11*a22*a33 + -a11*a23*a32 + ...
               = a11*det[[a22;a23];[a32;a33]])
                 + (-a12)*det[[a21;a23];[a31;a33]]
                 + a13*det[[a21;a22];[a31;a32]]    按第1行展开
               = 其他含开方式类似

     这里展示了两种方法：原始的凑下标的方式，递归的按某行某列展开的方法。
     数学上已经证明这两种方法的等价性。在Coq中也可以验证一次。
                 
     上述分析发现，我们需要如下的算法：
     1. 逆序数：给定一个自然数列表，
     2. 行列式原始算法：如何取出不同行不同列下标的所有组合。
     3. 子矩阵：去掉一行一列后剩下的矩阵。这是构造按某行某列展开算法的基础。

  3. 行列式的性质
  (1) n阶行列式是 n! 项的代数和，其中每一项是位于不同行、不同列的n个元素的乘积。
      当 n 增大时，n! 迅速增大。例如：5!=120, 10!=3628800 (362万个项)。
      所以我们一般不会做完全展开。
  (2) 行列互换（即矩阵做转置），行列式的值不变。这表明行列式的行与列的地位是对称的。
      因此有关行的性质，对于列也同样成立。今后只研究有关行的性质。
 *)

Require Import Extraction.
Require Export ListExt NatExt Matrix.
Require ZArith Reals.


Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv.


(* ############################################################################ *)
(** * Permutation of a list *)

(* ======================================================================= *)
(** ** Different methods for permutation *)

(** *** Method 1 *)
Module method1.
  
  Section def.
    Context {A} {Azero : A}.
    
    (** Get k-th element and remaining elements from a list *)
    Fixpoint pick (l : list A) (k : nat) : A * list A :=
      match k with
      | 0 => (hd Azero l, tl l)
      | S k' =>
          match l with
          | [] => (Azero, [])
          | x :: l' =>
              let (a,l0) := pick l' k' in
              (a, [x] ++ l0)
          end
      end.
    
    (** Get permutation of a list from its top n elements *)
    Fixpoint permAux (n : nat) (l : list A) : list (list A) :=
      match n with
      | 0 => [[]]
      | S n' =>
          concat
            (map
               (fun k =>
                  let '(x, lx) := k in
                  map (cons x) (permAux n' lx))
               (map (fun i => pick l i) (seq 0 n)))
      end.

    (** Get permutation of a list *)
    Definition perm (l : list A) : list (list A) := permAux (length l) l.
  End def.
  
  (* Compute perm [1;2;3]. *)

End method1.



(* Section old_code. *)
(*   Context {A : Type} {Azero : A} {Altb : A -> A -> bool}. *)


(** *** Method 2 *)
Module method2.
  
  Section def.
    Context {A} {Azero : A}.
    
    (** Convert a list to list of (one element * remaining elements) *)
    Fixpoint pick {A} (l : list A) (remaining : list A) : list (A * list A) :=
      match l with
      | [] => []
      | hl :: tl =>
          (hl, remaining ++ tl) :: (pick tl (remaining ++ [hl]))
      end.

    (** Get permutation of a list from its top n elements *)
    Fixpoint permAux {A} (n : nat) (l : list A) : list (list A) :=
      match n with
      | 0 => [[]]
      | S n' =>
          concat
            (map
               (fun k =>
                  let '(x, lx) := k in
                  map (cons x) (permAux n' lx))
               (pick l []))
      end.
    
    (** Get permutation of a list *)
    Definition perm (l : list A) : list (list A) := permAux (length l) l.
  End def.

  (* Compute perm2 [1;2;3]. *)
  
End method2.



(** *** Method 3 *)
Module Export method3.

  Section def.
    Context {A : Type}.

    (* 将 a 插入 l 的每个位置 *)
    Fixpoint permOne (a : A) (l : list A) : list (list A) :=
      match l with
      | [] => [[a]]
      | hl :: tl => (a :: l) :: (map (cons hl) (permOne a tl))
      end.
    
    Fixpoint perm (l : list A) : list (list A) :=
      match l with
      | [] => [[]]
      | hl :: tl => concat (map (permOne hl) (perm tl))
      end.
  End def.

  (* Compute perm [1;2;3]. *)

  Section props.
    Context {A : Type}.

    (** |permOne (a::l)| = |l| + 1 *)
    Lemma permOne_length : forall a (l : list A), length (permOne a l) = S (length l).
    Proof. induction l; simpl; auto. rewrite map_length. auto. Qed.

    Lemma permOne_not_nil : forall a (l : list A), permOne a l <> [].
    Proof. induction l; simpl; try easy. Qed.

    Lemma perm_not_nil : forall (l : list A), perm l <> [].
    Proof.
      induction l; simpl; try easy.
      destruct (perm l) eqn:E; simpl; try easy.
      destruct (permOne a l0) eqn:E1; try easy.
      apply permOne_not_nil in E1; auto.
    Qed.
    
    (* hd (perm l) = l *)
    Lemma hd_perm : forall (l : list A), hd [] (perm l) = l.
    Proof.
      induction l; auto.
      simpl.
    Admitted.

    Lemma perm_length_in : forall (l x : list A),
        In x (perm l) -> length x = S (length l).
    Admitted.
    (** |perm (a::l)| = |(a::l)| * |perm l| *)
    Lemma perm_cons_length : forall a (l : list A),
        length (perm (a :: l)) = (S (length l)) * (length (perm l)).
    Proof.
      intros. revert a. induction l; intros.
      - simpl. auto.
      - unfold perm; fold (perm (a :: l)).
        (* remember (a :: l) as d. *)
        assert (forall {A} (d : dlist A) n,
                   (forall l, In l d -> length l = n) ->
                   length (concat d) = n * length d).
        admit.
        rewrite H with (n:=S (length (a :: l))).
        rewrite map_length. auto.
        intros.
    Admitted.
    
    (** |perm l| = |l|! *)
    Lemma length_perm : forall (l : list A), length (perm l) = fact (length l).
    Proof.
      induction l. auto.
      rewrite perm_cons_length.
      simpl. rewrite IHl. auto.
    Qed.

    (* In a (perm l) -> forall x, In x a -> In x l *)
    Lemma perm_in : forall (l : list A) (a : list A),
        In a (perm l) -> (forall x, In x a -> In x l).
    Proof.
    Admitted.
  
  End props.

  (* 索引下标构成的排列 *)
  Section perm_index.
    Open Scope nat_scope.
    Notation perm := (@perm nat).
    
    (** In a (perm (seq 0 n)) -> i < n -> nth i a < n *)
    Lemma perm_index_lt : forall n i a, In a (perm (seq 0 n)) -> i < n -> nth i a 0 < n.
    Proof.
      intros. apply perm_in with (x:=nth i a 0) in H.
      - apply in_seq in H. lia.
      - apply nth_In.
        apply perm_length_in in H. rewrite seq_length in H. lia.
    Qed.

  End perm_index.

End method3.


(* ======================================================================= *)
(** ** reverse-order-number (RON) of a list, 逆序数 *)
Section ronum.
  Context {A} {Altb : A -> A -> bool}.
  Infix "<?" := Altb.

  (* The RON of one element respect to a list *)
  Definition ronum1 (a : A) (l : list A) : nat :=
    fold_left (fun (n : nat) (b : A) => n + (if b <? a then 1 else 0)) l 0.

  (* The RON of a list *)
  Fixpoint ronum (l : list A) : nat :=
    match l with
    | [] => 0
    | x :: l' => ronum1 x l' + ronum l'
    end.
End ronum.

Section test.
  Let ronum1 := @ronum1 nat Nat.leb.
  Let ronum := @ronum nat Nat.leb.
  (* Compute ronum1 3 [1;2;4]. (* = 2 *) *)
  (* Compute ronum [2;1;4;3]. (* = 2 *) *)
  (* Compute ronum [2;3;4;1]. (* = 3 *) *)
End test.

(* ======================================================================= *)
(** ** Parity of a permutation, 排列的奇偶性 *)
Section parity.
  Context {A} {Altb : A -> A -> bool}.

  (** The RON of a permutation is odd *)
  Definition oddPerm (l : list A) : bool := odd (ronum (Altb:=Altb) l).

End parity.


(* ======================================================================= *)
(** ** Exchange of a permutation 排列的对换 *)
Section permExchg.
  Context {A} {Altb : A -> A -> bool} (Azero : A).

  Notation ronum := (ronum (Altb:=Altb)).
  Notation oddPerm := (oddPerm (Altb:=Altb)).

  (* 对换第 i0,i1 的元素 *)
  Definition permExchg (l : list A) (i0 i1 : nat) : list A :=
    lswap Azero l i0 i1.

  (** 对换相邻位置改变排列的奇偶性 *)
  Theorem permExchg_parity : forall (l : list A) (n i0 i1 : nat),
      length l = n -> i0 < n -> i1 < n -> i0 <> i1 ->
      oddPerm (permExchg l i0 i1) <> oddPerm l.
  Proof.
    intros. unfold oddPerm. unfold permExchg.
    revert l i0 i1 H H0 H1 H2. induction n; intros. lia.
    destruct l; simpl in *. lia.
    (* 教科书上的证明很巧妙，难以形式化的描述出来。
       书上把 l 分解为
       [...] i [...] j [...]
       这种形式，然后分情形讨论
     *)
  Admitted.
  
End permExchg.


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
  Notation vcmul := (@vcmul _ Amul).
  Infix "\.*" := vcmul : vec_scope.

  Notation smat n := (smat A n).
  Notation mmul := (@mmul _ Aadd 0 Amul).
  Infix "*" := mmul : mat_scope.
  Notation mat1 := (@mat1 _ 0 1).
  (* Notation seqsum := (@seqsum _ Aadd 0). *)

  (** n阶行列式的完全展开式 (行下标固定，列下标来自于全排列）*)

  (* Tips: 对 colIds 使用 list 而不是 vec，因为 perm 的个数难以用依赖类型表达 *)
  
  (* 旧的实现：元素索引为 fin 类型，故需要 i < n 的证明，故需要处理 n = 0 *)
  Definition mdet_old {n} : smat n -> A :=
    match n with
    | O => fun _ => 1        (* the determinant of a empty matrix is 1 *)
    | S n' =>
        fun (M : smat (S n')) =>
          (* 列号 0,1,..,(n-1) 的全排列 *)
          let colIds := perm (seq 0 n)%nat in
          (* 每个式 *)
          let item (l:list nat) : A :=
            (let x := @seqsum _ Amul 1 n (fun i => M.[#i].[#(nth i l 0)%nat]) in
             if odd (ronum l (Altb:=Nat.ltb)) then - x else x) in
          (* 求和 *)
          fold_left Aadd (map item colIds) 0
    end.

  (** 新的实现：元素索引为 nat 类型，避免了提供 i < n 的证明，无需处理 n = 0 *)
  Definition mdet {n} (M : smat n) : A :=
    (* 列号 0,1,..,(n-1) 的全排列 *)
    let colIds : dlist nat := perm (seq 0 n)%nat in
    (* 每个项 *)
    let item (l : list nat) : A :=
      (let x := @seqsum _ Amul 1 n (fun i => (m2f 0 M) i (nth i l 0%nat)) in
       if odd (ronum l (Altb:=Nat.ltb)) then - x else x) in
    (* 求和 *)
    fold_left Aadd (map item colIds) 0.

  Notation "| M |" := (mdet M) : mat_scope.

  (** n阶行列式的完全展开式 (列下标固定，行下标来自于全排列）*)
  Definition mdet' {n} (M : smat n) : A :=
    (* 行号 0,1,..,(n-1) 的全排列 *)
    let rowIds : dlist nat := perm (seq 0 n)%nat in
    (* 每个项 *)
    let item (l : list nat) : A :=
      (let x := @seqsum _ Amul 1 n (fun j => (m2f 0 M) (nth j l 0%nat) j) in
       if odd (ronum l (Altb:=Nat.ltb)) then - x else x) in
    (* 求和 *)
    fold_left Aadd (map item rowIds) 0.

  (* 该命题见丘老师《高等代数》P35，我暂时未实现其证明 *)
  Axiom mdet'_eq_mdet : forall {n} (M : smat n), mdet' M = mdet M.

  (* |M\T| = |M| *)
  Lemma mdet_mtrans : forall {n} (M : smat n), |M\T| = |M|.
  Proof.
    intros. rewrite <- mdet'_eq_mdet at 1.
    unfold mdet, mdet'. f_equal.
    apply map_ext_in; intros.
    destruct (odd (ronum a)).
    - f_equal. apply seqsum_eq; intros.
      erewrite !nth_m2f, mnth_mtrans; auto.
    - apply seqsum_eq; intros. erewrite !nth_m2f, mnth_mtrans; auto.
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
  Admitted.
  
  (* 行列式一行的公因子可以提出去 *)
  Lemma mdet_row_coef : forall {n} (M1 M2 : smat n) (i : fin n) (x : A),
      (forall j, j <> i -> M1.[j] = M2.[j]) ->
      (M1.[i] = x \.* M2.[i])%V ->
      |M1| = (x * |M2|)%A.
  Admitted.

  (* 某一行是两组数的和，则行列式等于两个行列式的和，它们的这一行分别是这两组数 *)
  Lemma mdet_row_add : forall {n} (M1 M2 M : smat n) (i : fin n),
      (forall j, j <> i -> M1.[j] = M.[j] /\ M2.[j] = M.[j]) ->
      (M1.[i] + M2.[i])%V = M.[i] -> |M| = (|M1| + |M2|)%A.
  Admitted.
  
  (* 两行互换，行列式反号 *)
  Lemma mdet_row_swap : forall {n} (M1 M2 : smat n) (i j : fin n),
      i <> j ->
      (forall k, k <> i -> k <> j -> M1.[k] = M2.[k]) ->
      M1.[i] = M2.[j] -> M1.[j] = M2.[i] ->
      (|M1| = - |M2|)%A.
  Admitted.
  
  (* 两行相同，行列式的值为 0 *)
  Lemma mdet_row_same : forall {n} (M : smat n) (i j : fin n),
      i <> j -> M.[i] = M.[j] -> |M| = 0.
  Admitted.
  
  (* 两行成比例，行列式的值为 0 *)
  Lemma mdet_row_cmul : forall {n} (M : smat n) (i j : fin n) (x : A),
      i <> j -> M.[i] = (x \.* M.[j])%A -> |M| = 0.
  Admitted.
  
  (* 一行的倍数加到另一行，行列式的值不变 *)
  Lemma mdet_row_addRow : forall {n} (M1 M2 : smat n) (i j : fin n) (x : A),
      i <> j ->
      (forall k, k <> i -> M1.[k] = M2.[k]) ->
      M1.[i] = (M2.[i] + x \.*M2.[j])%V -> |M1| = |M2|.
  Admitted.

  (* If we have a field structure *)
  Section Field.
    Context `{HField : Field A Aadd 0 Aopp Amul 1}.
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
  Definition mdet1 (M : smat A 1) := M.11.

  (** mdet1 M = |M| *)
  Lemma mdet1_eq_mdet : forall M, mdet1 M = mdet M.
  Proof. intros. cbv. ring. Qed.
  
  (** |M| <> 0 <-> mdet_exp <> 0 *)
  Lemma mdet1_neq0_iff : forall (M : smat A 1),
      mdet M <> 0 <-> M.11 <> 0.
  Proof. intros. rewrite <- mdet1_eq_mdet; easy. Qed.

  (** Determinant of a matrix of dimension-2 *)
  Definition mdet2 (M : smat A 2) := (M.11*M.22 - M.12*M.21)%A.

  (** mdet2 M = |M| *)
  Lemma mdet2_eq_mdet : forall M, mdet2 M = mdet M.
  Proof. intros. unfold mdet2. cbn; rewrite <- !(nth_m2f_nat2finS 0); auto; ring. Qed.

  (** |M| <> 0 <-> mdet_exp <> 0 *)
  Lemma mdet2_neq0_iff : forall (M : smat A 2),
      mdet M <> 0 <-> (M.11*M.22 - M.12*M.21)%A <> 0.
  Proof. intros. rewrite <- mdet2_eq_mdet; easy. Qed.

  (** Determinant of a matrix of dimension-3 *)
  Definition mdet3 (M : smat A 3) :=
    (M.11 * M.22 * M.33 - M.11 * M.23 * M.32 - 
       M.12 * M.21 * M.33 + M.12 * M.23 * M.31 + 
       M.13 * M.21 * M.32 - M.13 * M.22 * M.31)%A.

  (** mdet3 M = mdet M *)
  Lemma mdet3_eq_mdet : forall M, mdet3 M = mdet M.
  Proof. intros. unfold mdet3. cbn; rewrite <- !(nth_m2f_nat2finS 0); auto; ring. Qed.
  
  (** |M| <> 0 <-> mdet_exp <> 0 *)
  Lemma mdet3_neq0_iff : forall (M : smat A 3),
      mdet M <> 0 <->
        (M.11 * M.22 * M.33 - M.11 * M.23 * M.32 - 
           M.12 * M.21 * M.33 + M.12 * M.23 * M.31 + 
           M.13 * M.21 * M.32 - M.13 * M.22 * M.31)%A <> 0.
  Proof. intros. rewrite <- mdet3_eq_mdet; easy. Qed.

  (** Determinant of a matrix of dimension-4 *)
  Definition mdet4 (M : smat A 4) :=
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
  Lemma mdet4_neq0_iff : forall (M : smat A 4),
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


(* ======================================================================= *)
(** ** Test of determinant *)

(** *** Test of determinant on `Z` type *)
Section testZ.
  Import ZArith.
  Open Scope Z_scope.
  Let mdet {n} (M : @smat Z n) : Z := @mdet _ Z.add 0 Z.opp Z.mul 1 n M.

  (* 《高等代数》邱维声 第三版 习题2.2 *)
  Let ex_1_5 : mat Z 5 5 :=
        l2m 0 [[0;0;0;1;0];[0;0;2;0;0];[0;3;8;0;0];[4;9;0;7;0];[6;0;0;0;5]].
  Goal mdet ex_1_5 = 120. cbv. auto. Qed.

  Let ex_2_1 : mat Z 3 3 := l2m 0 [[1;4;2];[3;5;1];[2;1;6]].
  Goal mdet ex_2_1 = -49. cbv. auto. Qed.
End testZ.

(** *** Test of determinant on `R` type *)
Section testR.
  Import Reals.
  Open Scope R_scope.
  Notation "0" := R0.
  Notation "1" := R1.
  Let mdet {n} (M : @smat R n) : R := @mdet _ Rplus 0 Ropp Rmult 1 n M.

  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : R.

  (* Eval cbv in mdet (mkmat_1_1 a11). *)
  (* = 0 + a11 * 1 *)
  (* Eval cbv in mdet (mkmat_2_2 a11 a12 a21 a22). *)
  (* = 0 + a11 * (a22 * 1) + - (a12 * (a21 * 1)) *)
  (* Eval cbv in mdet (mkmat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33). *)
  (* = 0 + a11 * (a22 * (a33 * 1)) 
         + - (a12 * (a21 * (a33 * 1))) 
         + a12 * (a23 * (a31 * 1)) 
         + - (a11 * (a23 * (a32 * 1))) 
         + a13 * (a21 * (a32 * 1)) 
         + - (a13 * (a22 * (a31 * 1))) *)

  (* 《高等代数》邱维声 第三版 习题2.2 *)
  Let ex_2_3 : mat R 3 3 := l2m 0 [[a11;a12;a13];[0;a22;a23];[0;0;a33]].
  Goal mdet ex_2_3 = a11 * a22 * a33. cbv. lra. Qed.

  (* 2.2.2节，例题3 *)
  Example eg_2_2_2_3 : forall a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 c1 c2 d1 d2 e1 e2 : R,
      mdet (@l2m _ 0 5 5
              [[a1;a2;a3;a4;a5];
               [b1;b2;b3;b4;b5];
               [ 0; 0; 0;c1;c2];
               [ 0; 0; 0;d1;d2];
               [ 0; 0; 0;e1;e2]]) = 0.
  Proof. intros. cbv. lra. Qed.

  (* 2.2.2节，例题4 *)
  Example eg_2_2_2_4 : forall x:R,
      mdet (@l2m _ 0 4 4
              [[7*x;x;1;2*x];
               [1;x;5;-1];
               [4;3;x;1];
               [2;-1;1;x]]) = 7*x^4 - 5*x^3 - 99*x^2 + 38*x + 11.
  Proof. intros. cbv. lra. Qed.
  
End testR.


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
  
  Notation smat n := (smat A n).
  Notation mat0 := (@mat0 _ 0).
  Notation madd := (@madd _ Aadd).
  Infix "+" := madd : mat_scope.
  Notation mdet := (@mdet _ Aadd 0 Aopp Amul 1).
  Notation "| M |" := (mdet M) : mat_scope.

  (* ======================================================================= *)
  (** ** sub-matrix  子矩阵 *)

  (** sub-matrix of M by remove i-th row and j-th column *)
  Definition msubmat {n} (M : smat (S n)) (i j : fin (S n)) : smat n :=
    fun i0 j0 =>
      let i1 := if (fin2nat i0 ??< fin2nat i)%nat
                then fin2SuccRange i0
                else fin2SuccRangeSucc i0 in
      let j1 := if (fin2nat j0 ??< fin2nat j)%nat
                then fin2SuccRange j0
                else fin2SuccRangeSucc j0 in
      M.[i1].[j1].

  (** msubmat (msetr M a j) i j = msubmat M i j *)
  Lemma msubmat_msetr : forall {n} (M : smat (S n)) (a : vec (S n)) (i j : fin (S n)),
      msubmat (msetr M a i) i j = msubmat M i j.
  Proof. intros. apply meq_iff_mnth; intros. unfold msubmat. unfold msetr. fin. Qed.

  (** msubmat (msetc M a j) i j = msubmat M i j *)
  Lemma msubmat_msetc : forall {n} (M : smat (S n)) (a : vec (S n)) (i j : fin (S n)),
      msubmat (msetc M a j) i j = msubmat M i j.
  Proof. intros. apply meq_iff_mnth; intros. unfold msubmat. unfold msetc. fin. Qed.

  (* 以下定义有助于完成行列式性质的证明 *)
  
  (* 另一种实现，使用 nat 类型的元素索引 *)
  Definition msubmatNat (M : nat -> nat -> A) (i j : nat) : nat -> nat -> A :=
    fun i0 j0 =>
      M
        (if (i0 ??< i)%nat then i0 else S i0)
        (if (j0 ??< j)%nat then j0 else S j0).

  Lemma msubmat_eq_msubmatNat : forall {n} (M : smat (S n)) (i j : fin (S n)),
      msubmat M i j = @f2m _ n n (msubmatNat (m2f 0 M) (fin2nat i) (fin2nat j)).
  Proof.
    intros. unfold msubmat, msubmatNat. apply meq_iff_mnth; intros.
    rewrite mnth_f2m.
    destruct i0,j0,i,j; simpl.
    assert ((if (i0 ??< i)%nat then i0 else S i0) < S n) as Hi.
    { destruct (_??<_)%nat. lia. lia. }
    assert ((if (i1 ??< i2)%nat then i1 else S i1) < S n) as Hj.
    { destruct (i1??<i2)%nat. lia. lia. }
    rewrite nth_m2f with (Hi:=Hi)(Hj:=Hj). f_equal.
    - unfold fin2SuccRange, fin2SuccRangeSucc.
      assert (fin2nat (Fin i0 E) < S n) as Ei. { simpl. lia. }
      rewrite nat2finS_eq with (E:=Ei).
      simpl.
      destruct (i0 ??< i)%nat. fin. fin.
    - unfold fin2SuccRange, fin2SuccRangeSucc.
      assert (fin2nat (Fin i1 E0) < S n). simpl. auto.
      rewrite nat2finS_eq with (E:=H).
      destruct (i1 ??< i2)%nat. apply fin_eq_iff; auto.
      apply fin_eq_iff; auto.
  Qed.
      
  (* ======================================================================= *)
  (** ** minor of matrix  余子式，余因式，余因子展开式 *)

  (** (i,j) minor of M *)
  Definition mminor {n} (M : smat (S n)) (i j : fin (S n)) : A := |msubmat M i j|.
      
  (** minor(M\T,i,j) = minor(M,j,i) *)
  Lemma mminor_mtrans : forall {n} (M : smat (S n)) (i j : fin (S n)),
      mminor (M\T) i j = mminor M j i.
  Proof. intros. unfold mminor. rewrite <- mdet_mtrans. auto. Qed.

  (** mminor (msetr M a i) i j = mminor M i j *)
  Lemma mminor_msetr : forall {n} (M : smat (S n)) (a : vec (S n)) (i j : fin (S n)),
      mminor (msetr M a i) i j = mminor M i j.
  Proof. intros. unfold mminor. rewrite msubmat_msetr. auto. Qed.
  
  (** mminor (msetc M a j) i j = mminor M i j *)
  Lemma mminor_msetc : forall {n} (M : smat (S n)) (a : vec (S n)) (i j : fin (S n)),
      mminor (msetc M a j) i j = mminor M i j.
  Proof. intros. unfold mminor. rewrite msubmat_msetc. auto. Qed.


  Definition mminorNat {n:nat} (M : nat -> nat -> A) (i j : nat) : A :=
    mdet (@f2m _ n n (msubmatNat M i j)).
  
  Lemma mminor_eq_mminorNat : forall {n} (M : smat (S n)) (i j : fin (S n)),
      mminor M i j = @mminorNat n (m2f 0 M) (fin2nat i) (fin2nat j).
  Proof.
    intros. unfold mminor, mminorNat. rewrite msubmat_eq_msubmatNat. auto.
  Qed.
  
  
  (* ======================================================================= *)
  (** ** cofactor of matrix  代数余子式 *)

  (** (i,j) cofactor of M *)
  Definition mcofactor {n} (M : smat (S n)) (i j : fin (S n)) : A :=
    let x := mminor M i j in
    if Nat.even (fin2nat i + fin2nat j) then x else - x.

  (** A(M\T,i,j) = A(M,j,i) *)
  Lemma mcofactor_mtrans : forall {n} (M : smat (S n)) (i j : fin (S n)),
      mcofactor (M\T) i j = mcofactor M j i.
  Proof.
    intros. unfold mcofactor. rewrite mminor_mtrans. rewrite Nat.add_comm. auto.
  Qed.

  (** mcofactor (msetr M a i) i j = mcofactor M i j *)
  Lemma mcofactor_msetr : forall {n} (M : smat (S n)) (a : vec (S n)) (i j : fin (S n)),
      mcofactor (msetr M a i) i j = mcofactor M i j.
  Proof. intros. unfold mcofactor. rewrite mminor_msetr. auto. Qed.

  (** mcofactor (msetc M a j) i j = mcofactor M i j *)
  Lemma mcofactor_msetc : forall {n} (M : smat (S n)) (a : vec (S n)) (i j : fin (S n)),
      mcofactor (msetc M a j) i j = mcofactor M i j.
  Proof. intros. unfold mcofactor. rewrite mminor_msetc. auto. Qed.

  
  (* ======================================================================= *)
  (** ** cofactor matrix (matrix of cofactors) 代数余子阵 *)

  (** cofactor matrix of M *)
  Definition mcomat {n} (M : smat (S n)) : smat (S n) := fun i j => mcofactor M i j.


  (* ======================================================================= *)
  (** **  Cofactor expansion of the determinant (Laplace expansion) *)

  (** Cofactor expansion of `M` along the i-th row *)
  Definition mdetExRow {n} : smat n -> fin n -> A :=
    match n with
    | O => fun _ _ => 1
    | S n' => fun M i => vsum (fun j => M.[i].[j] * mcofactor M i j)
    end.

  (** Cofactor expansion of `M` along the j-th column *)
  Definition mdetExCol {n} : smat n -> fin n -> A :=
    match n with
    | O => fun _ _ => 1
    | S n' => fun M j => vsum (fun i => M.[i].[j] * mcofactor M i j)
    end.

  (** row_expansion (M\T, i) = col_expansion (M, i) *)
  Lemma mdetExRow_mtrans : forall {n} (M : smat n) (i : fin n),
      mdetExRow (M \T) i = mdetExCol M i.
  Proof.
    intros. unfold mdetExRow, mdetExCol. destruct n; auto.
    apply vsum_eq; intros. rewrite mcofactor_mtrans, mnth_mtrans. auto.
  Qed.

  (** col_expansion (M\T, i) = row_expansion (M, i) *)
  Lemma mdetExCol_mtrans : forall {n} (M : smat n) (i : fin n),
      mdetExCol (M \T) i = mdetExRow M i.
  Proof. intros. rewrite <- mdetExRow_mtrans. auto. Qed.

  (** Cofactor expansion by row is equivalent to full expansion *)
  Theorem mdetExRow_eq_mdet : forall {n} (M : smat n) (i : fin n), mdetExRow M i = mdet M.
  Proof.
    intros. destruct n. cbv; ring.
    unfold mdetExRow, mdet in *.
  Admitted.

  (** Cofactor expansion by column is equivalent to full expansion *)
  Theorem mdetExCol_eq_mdet : forall {n} (M : smat n) (j : fin n), mdetExCol M j = mdet M.
  Proof.
    intros.
    pose proof(mdetExRow_eq_mdet (M\T) j).
    rewrite mdet_mtrans in H. rewrite <- H.
    rewrite mdetExRow_mtrans. auto.
  Qed.

  (** Cofactor expansion by row is equivalent to cofactor expansion by column *)
  Theorem mdetExRow_eq_mdetExCol : forall {n} (M : smat n) (i : fin n),
      mdetExRow M i = mdetExCol M i.
  Proof. intros. rewrite mdetExRow_eq_mdet, mdetExCol_eq_mdet. auto. Qed.

  (** < i-th row, cofactor of k-th row > = 0 (if i <> k) *)
  Theorem vdot_mcofactor_row_diff_eq0 : forall {n} (M : smat (S n)) (i k : fin (S n)),
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
      destruct (Nat.even (fin2nat k + fin2nat i0)) eqn:H1.
      + unfold mminor. f_equal. apply meq_iff_mnth; intros.
        unfold msubmat. unfold msetr. fin.
      + f_equal. unfold mminor. f_equal. apply meq_iff_mnth; intros.
        unfold msubmat. unfold msetr. fin.
    - rewrite <- H1. unfold B.
      rewrite mdetExRow_eq_mdet.
      apply (mdet_row_same _ i k); auto.
      apply veq_iff_vnth; intros.
      rewrite mnth_msetr_diff; auto.
      rewrite mnth_msetr_same; auto.
  Qed.
      
  (** < j-th column, cofactor of l-column row > = 0 (if j <> l) *)
  Theorem vdot_mcofactor_col_diff_eq0 : forall {n} (M : smat (S n)) (j l : fin (S n)),
      j <> l -> vdot (M&[j]) (fun i => mcofactor M i l) = 0.
  Proof.
    intros. pose proof (vdot_mcofactor_row_diff_eq0 (M\T) j l H).
    rewrite <- H0 at 2. f_equal. apply veq_iff_vnth; intros.
    rewrite mcofactor_mtrans. auto.
  Qed.

  (** < i-th row, cofactor of i-th row > = |M| *)
  Lemma vdot_mcofactor_row_same_eq_det : forall {n} (M : smat (S n)) (i : fin (S n)),
      vdot (M.[i]) (fun j => mcofactor M i j) = |M|.
  Proof. intros. rewrite <- mdetExRow_eq_mdet with (i:=i). auto. Qed.

  (** < j-th column, cofactor of j-th column > = |M| *)
  Lemma vdot_mcofactor_col_same_eq_det : forall {n} (M : smat (S n)) (j : fin (S n)),
      vdot (M&[j]) (fun i => mcofactor M i j) = |M|.
  Proof. intros. rewrite <- mdetExCol_eq_mdet with (j:=j). auto. Qed.

  
  Section example1.
    (* 
       a b 0 0 ... 0 0 0 
       0 a b 0 ... 0 0 0
       0 0 a b ... 0 0 0
       ...
       0 0 0 0 ... a b 0
       0 0 0 0 ... 0 a b    = a^n + (-1)^(n+1)b^2
     *)
    
    Variable n : nat.
    (* Let n := 7. *)
    Variable a b : A.
    Let M1 : smat (S n) := mdiagMk 0 (vrepeat a).
    Let M2 : smat (S n) := mclsr (mdiagMk 0 (vrepeat b)) #1.
    Let M := M1 + M2.
    (* Compute m2l M. *)

    
    (* a ^ n *)
    Fixpoint ApowNat (a : A) (n : nat) : A :=
      match n with
      | O => Aone
      | S n' => a * ApowNat a n'
      end.

    Example mdet_example1 :
    |M| = (ApowNat a (S n) + (if odd (S (S n)) then -b*b else b*b))%A.
    Proof.
      rewrite <- (mdetExCol_eq_mdet) with (j:=#0).
      unfold M,M1,M2.
      simpl.
      Abort.

  End example1.

  Section example2.
    (* Vandermonde determinant *)
  End example2.


  (** Cofactor expansion of `M` along the 0-th row *)
  (* Note that, it is not simply use `mdetExRow`, but a recursively definition *)
  Fixpoint mdetEx {n} : smat n -> A :=
    match n with
    | O => fun M => 1
    | S n' =>
        fun M => 
          vsum (fun j =>
                  let a := if Nat.even (fin2nat j)
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
      destruct (Nat.even (fin2nat i)) eqn:H1.
      + f_equal.
        unfold mcofactor; simpl. rewrite H1. unfold mminor at 3.
        rewrite <- (mdetExRow_eq_mdet _ #0).
        unfold mdetExRow. apply vsum_eq; intros. auto.
      + unfold mcofactor; simpl. rewrite H1. ring_simplify. f_equal.
        unfold mminor at 3.
        rewrite <- (mdetExRow_eq_mdet _ #0).
        unfold mdetExRow. apply vsum_eq; intros. auto.
  Qed.
  
  Theorem mdetEx_eq_mdet : forall {n} (M : smat n), mdetEx M = mdet M.
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
  Definition mcofactorEx {n} (M : smat (S n)) (i j : fin (S n)) : A :=
    let x := mdetEx (msubmat M i j) in
    if Nat.even (fin2nat i + fin2nat j) then x else - x.

  (** mcofactorEx is equal to mcofactor *)
  Lemma mcofactorEx_eq_mcofactor : forall {n} (M : smat (S n)) (i j : fin (S n)),
      mcofactorEx M i j = mcofactor M i j.
  Proof.
    intros. unfold mcofactorEx, mcofactor. unfold mminor.
    rewrite <- mdetEx_eq_mdet. auto.
  Qed.

End mdetEx.


(* ############################################################################ *)
(** * Adjoint Matrix *)
Section madj.
  Context `{HField : Field} {HAeqDec : Dec (@eq A)}.
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

  Notation vsum := (@vsum _ Aadd 0).

  Notation smat n := (smat A n).
  Notation mat1 := (@mat1 _ 0 1).
  Notation mcmul := (@mcmul _ Amul).
  Infix "\.*" := mcmul : mat_scope.
  Notation mmul := (@mmul _ Aadd 0 Amul).
  Infix "*" := mmul : mat_scope.
  Notation mmulv := (@mmulv _ Aadd 0 Amul).
  Infix "*v" := mmulv : mat_scope.
  Notation mdet := (@mdet _ Aadd 0 Aopp Amul 1).
  Notation "| M |" := (mdet M) : mat_scope.
  Notation mdetEx := (@mdetEx _ Aadd 0 Aopp Amul 1).
  Notation mcofactor := (@mcofactor _ Aadd 0 Aopp Amul 1).
  Notation mcofactorEx := (@mcofactorEx _ Aadd 0 Aopp Amul 1).
  
  (* ======================================================================= *)
  (** ** Adjoint matrix (Adjugate matrix, adj(A), A* ) *)
  
  (** Adjoint matrix *)
  Definition madj {n} : smat n -> smat n := 
    match n with
    | O => fun M => M 
    | S n' => fun M i j => mcofactorEx M j i
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
  Lemma mmul_madj_r : forall {n} (M : smat n), M * M\A = |M| \.* mat1.
  Proof.
    intros. apply meq_iff_mnth; intros.
    unfold madj. destruct n. fin.
    rewrite mnth_mmul. unfold mcol.
    replace (fun i0 => mcofactorEx M j i0) with (fun i0 => mcofactor M j i0).
    2:{ extensionality i0. rewrite mcofactorEx_eq_mcofactor. auto. }
    destruct (i ??= j) as [E|E].
    - apply fin2nat_inj in E. subst.
      rewrite vdot_mcofactor_row_same_eq_det.
      rewrite mnth_mcmul. rewrite mnth_mat1_same; auto. ring.
    - apply fin2nat_inj_not in E.
      rewrite (vdot_mcofactor_row_diff_eq0 M i j); auto.
      rewrite mnth_mcmul. rewrite mnth_mat1_diff; auto. ring.
  Qed.

  (** (M\A) * M = |M| * I *)
  Lemma mmul_madj_l : forall {n} (M : smat n), M\A * M = |M| \.* mat1.
  Proof.
    intros. apply meq_iff_mnth; intros.
    unfold madj. destruct n. fin.
    rewrite mnth_mmul. rewrite vdot_comm.
    replace (fun j0 => mcofactorEx M j0 i) with (fun j0 => mcofactor M j0 i).
    2:{ extensionality j0. rewrite mcofactorEx_eq_mcofactor. auto. }
    destruct (i ??= j) as [E|E].
    - apply fin2nat_inj in E. subst.
      rewrite vdot_mcofactor_col_same_eq_det.
      rewrite mnth_mcmul. rewrite mnth_mat1_same; auto. ring.
    - apply fin2nat_inj_not in E.
      rewrite (vdot_mcofactor_col_diff_eq0 M j i); auto.
      rewrite mnth_mcmul. rewrite mnth_mat1_diff; auto. ring.
  Qed.
  
  (** (/|M| .* M\A) * M = mat1 *)
  Lemma mmul_det_cmul_adj_l : forall {n} (M : smat n),
  |M| <> 0 -> (/|M| \.* M\A) * M = mat1.
  Proof.
    intros. rewrite mmul_mcmul_l. rewrite mmul_madj_l. rewrite mcmul_assoc.
    rewrite field_mulInvL; auto. apply mcmul_1_l.
  Qed.

  (** M * (/|M| .* M\A) = mat1 *)
  Lemma mmul_det_cmul_adj_r : forall {n} (M : smat n),
  |M| <> 0 -> M * (/|M| \.* M\A) = mat1.
  Proof.
    intros. rewrite mmul_mcmul_r. rewrite mmul_madj_r. rewrite mcmul_assoc.
    rewrite field_mulInvL; auto. apply mcmul_1_l.
  Qed.  

  (** |M| <> 0 -> (exists N : smat n, N * M = mat1) *)
  Lemma mdet_neq0_imply_mmul_eq1_l : forall {n} (M : smat n),
  |M| <> 0 -> (exists N : smat n, N * M = mat1).
  Proof. intros. exists (/|M| \.* M\A). apply mmul_det_cmul_adj_l. auto. Qed.

  (** |M| <> 0 -> (exists N : smat n, M * N = mat1) *)
  Lemma mdet_neq0_imply_mmul_eq1_r : forall {n} (M : smat n),
  |M| <> 0 -> (exists N : smat n, M * N = mat1).
  Proof. intros. exists (/|M| \.* M\A). apply mmul_det_cmul_adj_r. auto. Qed.

  (** |M| <> 0 -> (exists N : smat n, N * M = mat1 /\ M * N = mat1) *)
  Lemma mdet_neq0_imply_mmul_eq1 : forall {n} (M : smat n),
  |M| <> 0 -> (exists N : smat n, N * M = mat1 /\ M * N = mat1).
  Proof.
    intros. exists (/|M| \.* M\A). split.
    apply mmul_det_cmul_adj_l. auto.
    apply mmul_det_cmul_adj_r. auto.
  Qed.


  (* ======================================================================= *)
  (** ** Cramer rule *)

  (** Cramer rule, which can solve the equation with the form of C*x=b.
      Note, the result is valid only when |C| is not zero *)
  Definition cramerRule {n} (C : smat n) (b : @vec A n) : @vec A n :=
    fun i => mdetEx (msetc C b i) / (mdetEx C).

  (** C *v (cramerRule C b) = b, (The dimension is `S n`) *)
  Lemma cramerRule_eq_S : forall {n} (C : smat (S n)) (b : @vec A (S n)),
  |C| <> 0 -> C *v (cramerRule C b) = b.
  Proof.
    intros. unfold cramerRule. rewrite !mdetEx_eq_mdet.
    remember (msetc C b) as B. apply veq_iff_vnth; intros.
    rewrite vnth_mmulv. unfold vdot. unfold vmap2.
    rewrite vsum_eq with (b:=fun j => (/|C| * (C.[i].[j] * |B j|))%A).
    2:{ intros. rewrite !mdetEx_eq_mdet. field. auto. }
    rewrite <- vsum_cmul_l.
    rewrite vsum_eq
      with (b:=fun j => (vsum (fun k => C.[i].[j] * (b.[k] * mcofactor C k j)))%A).
    2:{ intros j. rewrite <- vsum_cmul_l. f_equal.
        rewrite <- (mdetExCol_eq_mdet _ j). unfold mdetExCol.
        apply vsum_eq; intros k. rewrite HeqB.
        rewrite mnth_msetc_same; auto. f_equal.
        rewrite mcofactor_msetc. auto. }
    rewrite vsum_eq
      with (b:=fun j=> vsum (fun k=> (C.[i].[j] * b.[k] * mcofactor C k j)%A)).
    2:{ intros j. apply vsum_eq; intros k. ring. }
    rewrite vsum_vsum.
    rewrite vsum_eq
      with (b:=fun k=> (b.[k] * vsum (fun j=> C.[i].[j] * mcofactor C k j))%A).
    2:{ intros j. rewrite vsum_cmul_l. apply vsum_eq; intros k. ring. }
    (* `vsum` has only one value when k = i *)
    rewrite vsum_unique with (i:=i) (x:=(|C| * b.[i])%A).
    - field; auto.
    - pose proof (vdot_mcofactor_row_same_eq_det C i).
      unfold vdot in H0. unfold vmap2 in H0. rewrite H0. ring.
    - intros. pose proof (vdot_mcofactor_row_diff_eq0 C i j H0).
      unfold vdot in H1. unfold vmap2 in H1. rewrite H1. ring.
  Qed.

  (** C *v (cramerRule C b) = b *)
  Theorem cramerRule_spec : forall {n} (C : smat n) (b : @vec A n),
  |C| <> 0 -> C *v (cramerRule C b) = b.
  Proof.
    intros. destruct n.
    - cbv. apply v0eq.
    - apply cramerRule_eq_S. auto.
  Qed.

  (** Cramer rule over list *)
  Definition cramerRuleList (n : nat) (lC : dlist A) (lb : list A) : list A :=
    let C : smat n := l2m 0 lC in
    let b : vec n := l2v 0 lb in
    let x := cramerRule C b in
    v2l x.

  (** {cramerRuleList lC lb} = cramerRule {lC} {lb} *)
  Theorem cramerRuleList_spec : forall n (lC : dlist A) (lb : list A),
      let C : smat n := l2m 0 lC in
      let b : vec n := l2v 0 lb in
      l2v 0 (cramerRuleList n lC lb) = cramerRule C b.
  Proof. intros. unfold cramerRuleList. rewrite l2v_v2l. auto. Qed.
  
End madj.

Section test.
  Import QcExt.
  
  Notation cramerRule := (@cramerRule _ Qcplus 0 Qcopp Qcmult 1 Qcinv).
  Notation cramerRuleList := (@cramerRuleList _ Qcplus 0 Qcopp Qcmult 1 Qcinv).
  Notation mdetEx := (@mdetEx _ Qcplus 0 Qcopp Qcmult 1).

  Let lC1 := Q2Qc_dlist [[1;2];[3;4]]%Q.
  Let lb1 := Q2Qc_list [5;6]%Q.
  Let C1 : smat Qc 2 := l2m 0 lC1.
  Let b1 : @vec Qc 2 := l2v 0 lb1.
  (* Compute v2l (cramerRule C1 b1). *)
  (* Compute cramerRuleList 2 lC1 lb1. *)

  Let lC2 := Q2Qc_dlist
               [[1;2;3;4;5];
                [2;4;3;5;1];
                [3;1;5;2;4];
                [4;5;2;3;1];
                [5;4;1;2;3]]%Q.
  Let lb2 := Q2Qc_list [1;2;3;5;4]%Q.
  (* Compute cramerRuleList 5 lC2 lb2. *)
End test.
