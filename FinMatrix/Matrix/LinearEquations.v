(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : System of Linear Equations (or Linear Equations)
  author    : ZhengPu Shi
  date      : 2024.01

  reference :
  1. https://en.wikipedia.org/wiki/System_of_linear_equations

  remark    :
  1. 一些记号：线性方程组的初等变换；或者矩阵的行变换
     [j] + [i] * K   : 第i个方程的K倍加到第j个方程; 第i行的K倍加到第j行
     ([i], [j])      : 交换第i个方程和第j个方程; 交换第i行和第j行
     [i] * K         : 第i个方程乘以非零数K; 第i行乘以非零数k
  2. 为了保持方程组初等变换前后同解，对以上变换有如下要求
     [j] + [i] * K   : 要求 i 和 j 不同
     [i] * K         : 要求 K 非零
 *)

Require Import MatrixInv.
Require MatrixR.


(** * System of Linear Equations (线性方程组) *)
Section SystemOfLinearEquations.
  Context `{HField : Field}.
  Context {AeqDec : Dec (@eq A)}.
  Add Field field_inst : (make_field_theory HField).
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + (-b)).
  Infix "-" := Asub : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv a b := (a * / b). 
  Infix "/" := Adiv : A_scope.
  
  Notation vadd := (@vadd _ Aadd).
  Infix "+" := vadd : vec_scope.
  Notation vdot := (@vdot _ Aadd 0 Amul).
  Notation "< a , b >" := (vdot a b) : vec_scope.
  Notation vcmul := (@vcmul _ Amul).
  Notation "x \.* a" := (vcmul x a) : vec_scope.
  Notation vzero := (vzero Azero).
  
  Notation mat r c := (mat A r c).
  Notation mrowSwap := (@mrowSwap A).
  Notation mrowScale := (@mrowScale _ Amul).
  Notation mrowAdd := (@mrowAdd _ Aadd Amul).

  (** *** 线性方程（简称方程） *)
  Section Eqn.
    
    (* n元线性方程，由系数和常数项构成 *)
    Definition Eqn (n : nat) := (@vec A n * A)%type.

    (* 两个方程相加 *)
    Definition eqnAdd {n} (e1 e2 : Eqn n) : Eqn n :=
      (fst e1 + fst e2, (snd e1 + snd e2)%A).

    (* e1 + e2 = e2 + e1 *)
    Lemma eqnAdd_comm : forall {n} (e1 e2 : Eqn n),
        eqnAdd e1 e2 = eqnAdd e2 e1.
    Proof. intros. unfold eqnAdd; simpl.
           pose proof (vadd_AGroup n). f_equal; agroup. all: apply commutative.
    Qed.

    (* e1 + (e2 + e3) = (e1 + e2) + e3 *)
    Lemma eqnAdd_assoc : forall {n} (e1 e2 e3 : Eqn n),
        eqnAdd e1 (eqnAdd e2 e3) = eqnAdd (eqnAdd e1 e2) e3.
    Proof. intros. unfold eqnAdd; simpl. f_equal; asemigroup. Qed.

    (* 方程乘以K倍 *)
    Definition eqnK {n} (K : A) (e : Eqn n) : Eqn n :=
      (K \.* fst e, K * snd e).

    Lemma eqnK_add : forall {n} (e : Eqn n) (K1 K2 : A),
        eqnK (K1 + K2)%A e = eqnAdd (eqnK K1 e) (eqnK K2 e).
    Proof.
      intros. unfold eqnK, eqnAdd; simpl. f_equal.
      - rewrite vcmul_add. auto.
      - ring.
    Qed.
    
  End Eqn.

  (** *** 线性方程组（简称方程组） *)
  Section Eqns.
    (* A general system of `s` linear equations with `n` unknowns and coefficents.
       Often the coefficents and unknowns are real or complex numbers, but integers 
       and rational numbers are also seen, as are polynomials and elements of an 
       abstract algebraic structure. *)

    (* 含有s个方程的n元线性方程组 *)
    Definition Eqns (n s : nat) := @vec (Eqn n) s.

  End Eqns.

  (** *** 方程组初等变换之交换两行 *)
  Section eqnsSwap.

    (* 方程组第i和j两行交换，记作 ([i], [j]) *)
    Definition eqnsSwap {n s} (e : Eqns n s) (i j : fin s) : Eqns n s := vswap e i j.

    Lemma eqnsSwap_eqnsSwap : forall {n s} (e : Eqns n s) (i j : fin s),
        eqnsSwap (eqnsSwap e i j) j i = e.
    Proof. intros. unfold eqnsSwap. apply vswap_vswap. Qed.

  End eqnsSwap.

  (** *** 方程组初等变换之某行乘以非零常数 *)
  Section eqnsScale.
    
    (* 方程组第i行乘以K，记作 [i] * K。注：要求k非零 *)
    Definition eqnsScale {n s} (e : Eqns n s) (i : fin s) (K : A) : Eqns n s :=
      fun j => if j ??= i then (K \.* fst (e$j), K * snd (e$j)) else e$j.

    Lemma eqnsScale_1 : forall {n s} (e : Eqns n s) (i : fin s), eqnsScale e i 1 = e.
    Proof.
      intros. unfold eqnsScale. apply veq_iff_vnth; intros j.
      destruct (_??=_); subst; auto.
      rewrite vcmul_1_l, identityLeft. rewrite <- surjective_pairing; auto.
    Qed.
      
    Lemma eqnsScale_eqnsScale : forall {n s} (e : Eqns n s) (i : fin s) (K1 K2 : A),
        eqnsScale (eqnsScale e i K1) i K2 = eqnsScale e i (K1*K2).
    Proof.
      intros. unfold eqnsScale. apply veq_iff_vnth; intros j.
      destruct (_??=_); subst; auto; simpl. f_equal.
      - rewrite vcmul_assoc; f_equal. ring.
      - ring.
    Qed.
  End eqnsScale.

  (** *** 方程组初等变换之某行乘以倍数后加至另一行 *)
  Section eqnsAdd.
    
    (* 方程组第i行乘以K加到第j行，记作 [j] + [i] * K。注：要求i和j不同 *)
    Definition eqnsAdd {n s} (e : Eqns n s) (i j : fin s) (K : A) : Eqns n s :=
      fun k => if k ??= j then eqnAdd (eqnK K (e$i)) (e$j) else e$k.

    Lemma eqnsAdd_K0 : forall {n s} (e : Eqns n s) (i j : fin s), eqnsAdd e i j 0 = e.
    Proof.
      intros. apply veq_iff_vnth; intros k.
      unfold eqnsAdd. destruct (_??=_); subst; auto.
      unfold eqnAdd, eqnK. simpl. rewrite vcmul_0_l. rewrite ring_mul_0_l at 1.
      rewrite !identityLeft. rewrite <- surjective_pairing; auto.
    Qed.

    Lemma eqnsAdd_eqnsAdd : forall {n s} (e : Eqns n s) (i j : fin s) (K1 K2 : A),
        i <> j -> eqnsAdd (eqnsAdd e i j K1) i j K2 = eqnsAdd e i j (K1+K2)%A.
    Proof.
      intros. apply veq_iff_vnth; intros k. unfold eqnsAdd.
      destruct (_??=_); subst; try easy.
      destruct (_??=_); subst; try easy.
      destruct (_??=_); subst; try easy.
      rewrite eqnAdd_assoc. f_equal.
      rewrite eqnK_add. rewrite eqnAdd_comm. auto.
    Qed.
    
  End eqnsAdd.

  (** ** 方程组的解 *)
  Section isAnswer.
    
    (** n元有序数组(c1,c2,...,cn)\T 是方程组 e 的一个“解” *)
    Definition isAnswer {n s} (e : Eqns n s) (c : @vec A n) : Prop :=
      forall i, <fst (e $ i), c> = snd (e $ i).

    (** 若c是方程组e的一个解，则c也是 ([i],[j]) 后的方程组的解 *)
    Lemma isAnswer_eqnsSwap :
      forall {n s} (e : Eqns n s) (c : @vec A n) (i j : fin s),
        isAnswer e c -> isAnswer (eqnsSwap e i j) c.
    Proof.
      intros. unfold isAnswer, eqnsSwap in *. intros k.
      unfold vswap. destruct (_??=_); auto. destruct (_??=_); auto.
    Qed.

    (** 若c是方程组e经过 ([i],[j]) 后的一个解，则c也是e的解 *)
    Lemma isAnswer_eqnsSwap_rev :
      forall {n s} (e : Eqns n s) (c : @vec A n) (i j : fin s),
        isAnswer (eqnsSwap e i j) c -> isAnswer e c.
    Proof.
      intros.
      pose proof (isAnswer_eqnsSwap (eqnsSwap e i j) c j i H).
      rewrite eqnsSwap_eqnsSwap in H0. auto.
    Qed.
    
    (** 若c是方程组e的一个解，则c也是 [i] * K 后的方程组的解 *)
    Lemma isAnswer_eqnsScale :
      forall {n s} (e : Eqns n s) (c : @vec A n) (i : fin s) (K : A),
        isAnswer e c -> isAnswer (eqnsScale e i K) c.
    Proof.
      intros. unfold isAnswer, eqnsScale in *. intros k.
      destruct (_??=_); subst; simpl; auto. rewrite vdot_vcmul_l.
      specialize (H i). rewrite <- H. auto.
    Qed.
    
    (** 若c是方程组e经过[i] * K 后的一个解，则c也是e的解 *)
    Lemma isAnswer_eqnsScale_rev :
      forall {n s} (e : Eqns n s) (c : @vec A n) (i : fin s) (K : A),
        K <> 0 -> isAnswer (eqnsScale e i K) c -> isAnswer e c.
    Proof.
      intros.
      pose proof (isAnswer_eqnsScale (eqnsScale e i K) c i (1/K) H0).
      rewrite eqnsScale_eqnsScale in H1.
      replace (K * (1/K)) with 1 in H1. rewrite eqnsScale_1 in H1. auto.
      field; auto.
    Qed.

    (** 若c是方程组e的一个解，则c也是 [j] + [i] * K 后的方程组的解 *)
    Lemma isAnswer_eqnsAdd :
      forall {n s} (e : Eqns n s) (c : @vec A n) (i j : fin s) (K : A),
        isAnswer e c -> isAnswer (eqnsAdd e i j K) c.
    Proof.
      intros. unfold isAnswer, eqnsAdd in *. intros k.
      destruct (_??=_); auto.
      unfold eqnAdd, eqnK; simpl. rewrite vdot_vadd_l.
      rewrite vdot_vcmul_l. f_equal; auto. f_equal; auto.
    Qed.

    (** 若c是方程组e经过 [j] + [i] * K 后的一个解，则c也是e的解 *)
    Lemma isAnswer_eqnsAdd_rev :
      forall {n s} (e : Eqns n s) (c : @vec A n) (i j : fin s) (K : A),
        i <> j -> isAnswer (eqnsAdd e i j K) c -> isAnswer e c.
    Proof.
      intros. 
      pose proof (isAnswer_eqnsAdd (eqnsAdd e i j K) c i j (-K) H0).
      rewrite eqnsAdd_eqnsAdd in H1; auto.
      replace (K - K) with 0 in H1 by ring. rewrite eqnsAdd_K0 in H1; auto.
    Qed.
    
  End isAnswer.
  
  Section isAnswers.

    (* 方程组 e 的所有解组成的集合称为这个方程组的“解集” *)
    (* 从方程组的解集中，并且还符合实际问题需要的解时，称为“可行解” *)
    Definition isAnswers {n s t} (e : Eqns n s)
      (cs : @vec (@vec A n) t) : Prop :=
      (vforall cs (fun c => isAnswer e c)) /\
        (forall c, ~ vmem cs c -> ~ (isAnswer e c)).
    
    (* 若方程组有两个解集，则这两个解集等价 *)
    Lemma isAnswers_imply_equiv :
      forall {n s t1 t2} (e : Eqns n s)
        (cs1 : @vec (@vec A n) t1) (cs2 : @vec (@vec A n) t2),
        isAnswers e cs1 -> isAnswers e cs2 -> vequiv cs1 cs2.
    Proof.
      intros. destruct H as [H1A H1B], H0 as [H2A H2B].
      unfold vequiv. split.
      - destruct (vmems_dec cs1 cs2) as [H|H]; auto.
        unfold vmems, vforall in *.
        apply not_all_ex_not in H. destruct H as [i H]. (* cs1$i 不在 cs2 中 *)
        specialize (H2B (cs1 i) H).                     (* cs1$i 不是 e 的解 *)
        specialize (H1A i).                             (* cs1$i 是 e 的解 *)
        easy.
      - destruct (vmems_dec cs2 cs1) as [H|H]; auto.
        unfold vmems, vforall in *.
        apply not_all_ex_not in H. destruct H as [i H]. (* cs2$i 不在 cs1 中 *)
        specialize (H1B (cs2 i) H).                     (* cs2$i 不是 e 的解 *)
        specialize (H2A i).                             (* cs2$i 是 e 的解 *)
        easy.
    Qed.

    (* 若一个解集与方程组的解集等价，则这个新的解集也是方程组的解集 *)
    Lemma isAnswers_if_equiv :
      forall {n s t1 t2} (e : Eqns n s)
        (cs1 : @vec (@vec A n) t1) (cs2 : @vec (@vec A n) t2),
        isAnswers e cs1 -> vequiv cs1 cs2 -> isAnswers e cs2.
    Proof.
      intros. destruct H as [H1A H1B]. destruct H0 as [H2A H2B]. hnf. split.
      - unfold vmems, vforall in *. intros. destruct (H2B i) as [j H].
        rewrite <- H. auto.
      - intros. apply H1B. intro. destruct H.
        unfold vmems, vmem, vforall, vexist in *.
        destruct H0 as [i H0]. destruct (H2A i) as [j H1].
        rewrite <- H0, <- H1. exists j. auto.
    Qed.
    
  End isAnswers.

  (** *** 同解 *)
  Section sameAnswers.

    (* 若方程组I与II的解集等价，则称I和II同解 *)
    Definition sameAnswers {n s1 s2 : nat} (e1 : Eqns n s1) (e2 : Eqns n s2) : Prop :=
      forall (t : nat) (cs : @vec (@vec A n) t), isAnswers e1 cs <-> isAnswers e2 cs.

    Lemma sameAnswers_refl : forall {n s} (e : Eqns n s), sameAnswers e e.
    Proof. intros. hnf. tauto. Qed.

    Lemma sameAnswers_syms : forall {n s1 s2} (e1 : Eqns n s1) (e2 : Eqns n s2),
        sameAnswers e1 e2 -> sameAnswers e2 e1.
    Proof. intros. hnf in *. intros. split; intros; apply H; auto. Qed.
    
    Lemma sameAnswers_trans :
      forall {n s1 s2 s3} (e1 : Eqns n s1) (e2 : Eqns n s2) (e3 : Eqns n s3),
        sameAnswers e1 e2 -> sameAnswers e2 e3 -> sameAnswers e1 e3.
    Proof.
      intros. hnf in *. intros. split; intros.
      apply H0, H; auto. apply H, H0; auto.
    Qed.

    (* 方程组初等变换 ([i],[j]) 保持同解 *)
    Lemma sameAnswers_eqnsSwap : forall {n s} (e : Eqns n s) (i j : fin s),
        sameAnswers e (eqnsSwap e i j).
    Proof.
      intros. unfold sameAnswers, isAnswers; intros. split; intros [H1 H2]; split.
      - intro k. apply isAnswer_eqnsSwap; auto.
      - intros c H. specialize (H2 c H). intro. destruct H2.
        apply isAnswer_eqnsSwap_rev in H0; auto.
      - intros k. specialize (H1 k); simpl in H1.
        apply isAnswer_eqnsSwap_rev in H1; auto.
      - intros c H. specialize (H2 c H). intro. destruct H2.
        apply isAnswer_eqnsSwap; auto.
    Qed.

    (* 方程组初等变换 [i] * K 保持同解 *)
    Lemma sameAnswers_eqnsScale : forall {n s} (e : Eqns n s) (i : fin s) (K : A),
        K <> 0 -> sameAnswers e (eqnsScale e i K).
    Proof.
      intros. unfold sameAnswers, isAnswers; intros. split; intros [H1 H2]; split.
      - intro k. apply isAnswer_eqnsScale; auto.
      - intros c H3. specialize (H2 c H3). intro. destruct H2.
        apply isAnswer_eqnsScale_rev in H0; auto.
      - intros k. specialize (H1 k); simpl in H1.
        apply isAnswer_eqnsScale_rev in H1; auto.
      - intros c H3. specialize (H2 c H3). intro. destruct H2.
        apply isAnswer_eqnsScale; auto.
    Qed.

    (* 方程组初等变换 [j] + [i] * K 保持同解 *)
    Lemma sameAnswers_eqnsAdd : forall {n s} (e : Eqns n s) (i j : fin s) (K : A),
        i <> j -> sameAnswers e (eqnsAdd e i j K).
    Proof.
      intros. unfold sameAnswers, isAnswers; intros. split; intros [H1 H2]; split.
      - intro k. apply isAnswer_eqnsAdd; auto.
      - intros c H3. specialize (H2 c H3). intro. destruct H2.
        apply isAnswer_eqnsAdd_rev in H0; auto.
      - intros k. specialize (H1 k); simpl in H1.
        apply isAnswer_eqnsAdd_rev in H1; auto.
      - intros c H3. specialize (H2 c H3). intro. destruct H2.
        apply isAnswer_eqnsAdd; auto.
    Qed.

  End sameAnswers.

  (** ** 方程组的初等变换 *)
  Section EqnsTrans.
    
    (** 方程组的初等变换 *)
    Inductive EqnsTrans {n s} : Eqns n s -> Eqns n s -> Prop :=
    | ETswap (i j : fin s) : forall e : Eqns n s, EqnsTrans e (eqnsSwap e i j)
    | ETscale (i : fin s) (K : A) : forall e : Eqns n s,
        K <> 0 -> EqnsTrans e (eqnsScale e i K)
    | ETadd (i j : fin s) (K : A) : forall e : Eqns n s,
        i <> j -> EqnsTrans e (eqnsAdd e i j K)
    | ETtrans : forall e1 e2 e3 : Eqns n s,
        EqnsTrans e1 e2 -> EqnsTrans e2 e3 -> EqnsTrans e1 e3.

    (* 方程组的初等变换保持同解 *)
    Lemma sameAnswers_eqnsTrans : forall {n s} (e1 e2 : Eqns n s),
        EqnsTrans e1 e2 -> sameAnswers e1 e2.
    Proof.
      intros. induction H as [i j H|i K H|i j K H|e1 e2 e3 H1 H2].
      - apply sameAnswers_eqnsSwap.
      - apply sameAnswers_eqnsScale; auto.
      - apply sameAnswers_eqnsAdd; auto.
      - apply sameAnswers_trans with e2; auto.
    Qed.

  End EqnsTrans.
  
  (** *** 方程组的系数矩阵 *)
  Section coefMat.
        
    (* 取出s个方程的n元线性方程组的系数矩阵 *)
    Definition coefMat {n s} (e : Eqns n s) : mat s n := vmap fst e.

  End coefMat.
  
  (** *** 方程组的增广矩阵 *)
  Section extMat.
    
    (* 将s个方程的n元线性方程组转换为s行(n+1)列的增广矩阵 *)
    Definition eqns2extMat {n s} (e : Eqns n s) : mat s (S n) :=
      mconscT (vmap fst e) (vmap snd e).

    (* 将s行(n+1)列的增广矩阵转换为s个方程的n元线性方程组 *)
    Definition extMat2eqns {n s : nat} (e : mat s (S n)) : Eqns n s :=
      fun i => (vremoveT (e $ i), vtail (e $ i)).

    Lemma eqns2extMat_extMat2eqns : forall {n s} (e : mat s (S n)),
        eqns2extMat (extMat2eqns e) = e.
    Proof.
      intros. unfold eqns2extMat, extMat2eqns. apply meq_iff_mnth; intros i j.
      destruct (j ??= nat2finS n); subst.
      - rewrite mnth_mconscT_n; auto.
      - rewrite mnth_mconscT_lt with (H:=nat2finS_neq_imply_lt j n0).
        rewrite vnth_vmap. simpl. rewrite vnth_vremoveT.
        rewrite fin2SuccRange_fin2PredRange. auto.
    Qed.

    Lemma extMat2eqns_eqns2extMat : forall {n s} (e : Eqns n s),
        extMat2eqns (eqns2extMat e) = e.
    Proof.
      intros. unfold eqns2extMat, extMat2eqns. apply veq_iff_vnth; intros i.
      rewrite vnth_mconscT. rewrite vremoveT_vconsT, vtail_vconsT.
      rewrite !vnth_vmap. rewrite <- surjective_pairing; auto.
    Qed.
    
  End extMat.

  (** *** 矩阵的初等行变换 *)
  Section MRT.

    (* MRT: Matrix Row Transformn *)
    Inductive MRT {r c} : mat r c -> mat r c -> Prop :=
    | MRTswap (i j : fin r) : forall M : mat r c, MRT M (mrowSwap M i j)
    | MRTscale (i : fin r) (K : A) : forall M : mat r c, K <> 0 -> MRT M (mrowScale M i K)
    | MRTadd (i j : fin r) (K : A) : forall M : mat r c, i <> j -> MRT M (mrowAdd M i j K)
    | MRTrefl : forall M : mat r c, MRT M M
    | MRTtrans : forall M1 M2 M3 : mat r c, MRT M1 M2 -> MRT M2 M3 -> MRT M1 M3.

  End MRT.

  (** ** 阶梯形矩阵 *)
  Section EchelonForm.
    (* 阶梯形矩阵:
       1. 丘老师的版本
       (1) 零行在下方（如果有零行）
       (2) 非零行的主元的列指标随着行指标的递增而严格增大
       2. 尝试1
       (1) 计算第i行和第S i行的主元位置，记作opivot(i), opivot(S i)。
           若零行则无主元，若非零行则有主元。
       (2) match opivot(i), opivot(S i) with
           | _, None => 继续递归
           | None, Some _ => False
           | Some j, Some j' => j < j' /\ 继续递归
     *)

    Notation vpivot := (@vpivot _ _ Azero).

    (** a,b两个向量是“相邻行阶梯形”的 *)
    Definition EchelonNear {n} (a b : @vec A n) : Prop :=
      match vpivot a, vpivot b with
      | _, None => True             (* b无主元即可 *)
      | None, Some _ => False        (* 若a无主元，但b有主元，则错误 *)
      | Some i, Some i' => fin2nat i < fin2nat i' (* 若a,b都有主元，则序号严格小于 *)
      end.

    (** 头部加入0保持“相邻行阶梯形” *)
    Lemma echoelonNear_vconsH_0 : forall {n} (a b : @vec A n),
        EchelonNear a b -> EchelonNear (vconsH 0 a) (vconsH 0 b).
    Proof.
      intros. hnf in *.
      destruct (vpivot a) as [ia|].
      - destruct (vpivot b) as [ib|].
        +  ?
      EchelonNear (vconsH 0 (vremoveT M (nat2finS r))) (vconsH 0 (vtail M))



    (** 矩阵M是阶梯形矩阵 *)
    Definition Echelon {r c} (M : mat r c) : Prop :=
      r <= 1 \/
        (forall (i : fin r),
            fin2nat i < r -> EchelonNear (M$i) (M$(fin2SameRangeSucc i))).

    (** 0行的矩阵是阶梯形矩阵 *)
    Lemma echelon_rows0 : forall {c} (M : mat 0 c), Echelon M.
    Proof. intros. hnf; intros. auto. Qed.

    (** 1行的矩阵是阶梯形矩阵 *)
    Lemma echelon_rows1 : forall {c} (M : mat 1 c), Echelon M.
    Proof. intros. hnf; intros. auto. Qed.
    
    (** 0列的矩阵是阶梯形矩阵 *)
    Lemma echelon_cols0 : forall {r} (M : mat r 0), Echelon M.
    Proof. intros. hnf; intros. right; intros. hnf. auto. Qed.

    (** 与矩阵最底行满足“相邻行阶梯形”的向量加入矩阵底部后仍是阶梯形 *)
    Lemma echelon_vconsT : forall {r c} (M : mat (S r) c) (a : @vec A c),
        EchelonNear (M $ (nat2finS r)) a -> Echelon M -> Echelon (vconsT M a).
    Proof.
      intros.
      Admitted.

    (** 矩阵左侧加入一列零元素仍然是阶梯形  *)
    Lemma echelon_mconscH_vzero : forall {r c} (M : mat r c),
        Echelon (mconscH vzero M).
    Proof.
      induction r.
      - intros; apply echelon_rows0.
      - intros.
        rewrite <- (vconsT_vremoveT_vtail M (Azero:=vzero)).
        rewrite <- vconsT_vzero_0.
        rewrite mconscH_vconsT_vconsT_eq_vconsT_mconscH_vconsH.
        remember (mconscH vzero (vremoveT M)) as M0.
        remember (vconsH 0 (vtail M)) as a.
        (* 再分解出 M0 的最后一行 *)
        destruct r.
        + apply echelon_rows1.
        + apply echelon_vconsT.
          * rewrite HeqM0, Heqa. rewrite vnth_mconscH.
            rewrite vnth_vzero. ?
            replace (mconscH vzero (vremoveT M) (nat2finS r))
              with (vconsH 0 ((vremoveT M) $ (nat2finS r))).
            2:{ remember (vremoveT M) as M1.
?            admit.
            rewrite H.
            Search mconscH.
            hnf.
            unfold mconscH.
            assert (Echelon M0). admit.
        Check vconsT (mconscH vzero (vremoveT M)) (vconsH 0 (vtail M)).
        replace vzero with (@vconsH _ r Azero vzero); auto.
        2:{ apply 
              replace (mconscH (vconsH 0 vzero) (vconsT (vremoveT M) (vtail M)))
          with (vconsT (mconscH vzero (vremoveT M)) (vconsH Azero (vtail M))).
            
            
        Check @vzero (S r) = vconsH Azero vzero.
        replace vzero with (vconsH Azero vzero) at 1.
        Check (mconscH vzero (vconsT (vremoveT M) (vtail M))).
        Check vconsT (mconscH vzero (vremoveT M)) (vconsH Azero (vtail M)).
        vzero.
        Check (vconsT (
        specialize (IHr c (vremoveT M)).
        rewrite <- (mconscH_mheadc_mremovecH M).
        
        Abort.

    
    (** 任意一个矩阵都可以经过一系列初等行变换化成阶梯形矩阵 *)
    Theorem existEchelonByMRT : forall {r c} (M : mat r c),
      exists N : mat r c, MRT M N /\ Echelon N.
    Proof.
      induction r.
      - (* 0行的矩阵是阶梯形矩阵 *)
        intros. exists M. split. constructor. hnf. intros. lia.
      - induction c.
        + (* 0列的矩阵是阶梯形矩阵 *)
          intros. exists M. split. constructor. hnf. intros.
          unfold opivoti, opivotSi. rewrite !vpivot_vec0 in *. auto.
        + intros M.
          rewrite <- (mconscH_mheadc_mremovecH M).
          pose proof (IHc (mremovecH M)). destruct H as [N0 [HN01 HN02]].
          (* 看第1列是否全零 *)
          destruct (Aeqdec (mheadc M) vzero) as [H|H].
          * (* 第1列是全零 *)
            exists (mconscH (mheadc M) (mremovecH M)). split.
            ** constructor.
            ** rewrite H.
               remember (mremovecH M) as M0.
?            
          * (* 第1列不是全零 *)
        
          Search (Matrix.mat _ _ _ -> _).
          Check 
          Search mconscH.
          Check mconscH.
          Check M i.
          assert (

      
        e1 e2 : Eqns n s),
        EqnsTrans e1 e2 -> sameAnswers e1 e2.
    Proof.
      intros. induction H as [i j H|i K H|i j K H|e1 e2 e3 H1 H2].
      - apply sameAnswers_eqnsSwap.
      - apply sameAnswers_eqnsScale; auto.
      - apply sameAnswers_eqnsAdd; auto.
      - apply sameAnswers_trans with e2; auto.
    Qed.

  End EchelonForm.

    (** 简化行阶梯形矩阵 *)
    
    (** 矩阵M是简化行阶梯形矩阵 *)

        (** 序列中的指标严格递增. 即：从头到尾遍历序列中的元素时，
      (1) 若元素是None，则其余元素都必须是 None
      (2) 否则当前元素是Some i的形式，然后下一个元素必须是两种情形之一，
          要么是 None，要么是 Some j的形式（其中，i < j）。*)

    
    (* 零行 M$i = vzero *)
    (* 非零行 M$i <> vzero *)
    
    (* 主元 *)

    Inductive EqnsTrans {n s} : Eqns n s -> Eqns n s -> Prop :=
    | ETswap (i j : fin s) : forall e : Eqns n s, EqnsTrans e (eqnsSwap e i j)
    | ETscale (i : fin s) (K : A) : forall e : Eqns n s,
        K <> 0 -> EqnsTrans e (eqnsScale e i K)
    | ETadd (i j : fin s) (K : A) : forall e : Eqns n s,
        i <> j -> EqnsTrans e (eqnsAdd e i j K)
    | ETtrans : forall e1 e2 e3 : Eqns n s,
        EqnsTrans e1 e2 -> EqnsTrans e2 e3 -> EqnsTrans e1 e3.

    (* 方程组的初等变换保持同解 *)
    Lemma sameAnswers_eqnsTrans : forall {n s} (e1 e2 : Eqns n s),
        EqnsTrans e1 e2 -> sameAnswers e1 e2.
    Proof.
      intros. induction H as [i j H|i K H|i j K H|e1 e2 e3 H1 H2].
      - apply sameAnswers_eqnsSwap.
      - apply sameAnswers_eqnsScale; auto.
      - apply sameAnswers_eqnsAdd; auto.
      - apply sameAnswers_trans with e2; auto.
    Qed.
    
  

  (** ** 简化阶梯形矩形 *)

End SystemOfLinearEquations.
?

  (* Vector equation form *)

  (* 使用cramer rule解方程组（未区分有解、无解、多解，并且系数阵必须是方阵 *)
  Definition solveUnknownsByCramerRule {n} (e : Eqns n n) : @vec A n :=
    @cramerRule _ Aadd 0 Aopp Amul 1 Ainv n (leCoef e) (leConst e).
End general_form.    


(* 2024.02.29 张子航ppt中最后一个例子，验证解方程的能力 *)
Section test.

  (* 在R上进行 *)
  Import MatrixR.
  Check cramerRule.
  Section 
  Require Import Reals.
  Open Scope R.

  Let solveUnknownsByCramerRule {n} :=
        (@solveUnknownsByCramerRule _ Rplus R0 Ropp Rmult R1 Rinv n).
  Let e1 := Build_Eqns 3 3
              (l2m 0 [[6;0;1];[0;4;1];[-3;-2;1]])
              (l2v 0 3 [4;0;2]).
  Compute v2l (solveUnknownsByCramerRule e1).
  
  (* Import MatrixR. *)
  Check @l2m R 0 3 3 [[6;0;1];[0;4;1];[-3;-2;1]].
  Check Build_t. t 3 3.
* coq代码
  ```coq
  (* 第一种用法，可以求解方程（但缺点是 R 的表达式复杂而看不清，可用 Qc 来改进，但无理数不支持 *)
  Compute v2l (cramerRule (@l2m 3 3 [[6;0;1];[0;4;1];[-3;-2;1]]) (@l2v 3 [4;0;2])).
  (* 第二种用法，可用交互式环境得到更好看的结果，即使是 R 类型。 *)
  Variable a b c : R.
  Goal cramerRule (@l2m 3 3 [[6;0;1];[0;4;1];[-3;-2;1]]) (@l2v 3 [4;0;2]) = l2v [a;b;c].
  Proof. veq; field_simplify.  (* a = 1/3, b = -1/2, c=2 *) Abort.
  (* 第三种用法，一旦根据上一步知道了结果，那么就可以直接验证了 *)
  Goal <cramerRule (@l2m 3 3 [[6;0;1];[0;4;1];[-3;-2;1]]) (@l2v 3 [4;0;2]),
    @l2v 3 [3;3;1]> = 1.5.
    cbv. field.
  Qed.
  ```
* 这个例子也能看出一些 ring, field, lra, 等策略的区别。
  
  Check mat.

End test.
(* 2024.02.29 张子航ppt中最后一个例子，验证解方程的能力 *)
Variable a : @Eqns 3 4.
Compute v2l (unknowns a).
Definition unknowns := nat.

Check Eqns.unknowns.
  Section general_form.

  Record Eqns := {
      un
  Context {m n : nat}.
  Check mat A m n.

