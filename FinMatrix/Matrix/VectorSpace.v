(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : vector space
  author    : ZhengPu Shi
  date      : 2024.01

  remark    :
  1. 向量空间是线性空间的具体情形。其元素形如 @vec A c。
  (1) 若A为实数，称为 real vector space
  (2) 若A为复数，称为 complex vector space
 *)


Require Import LinearSpace.
Require Import Vector.

Set Implicit Arguments.
Unset Strict Implicit.

Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv Ale Alt Altb Aleb a2r.

Open Scope A_scope.
Open Scope vec_scope.
Open Scope VectorSpace_scope.


(* ===================================================================== *)
(** ** Linearly combination (线性组合) *)
Section lcomb.
  Context `{HVectorSpace : VectorSpace}.
  Add Field field_inst : (make_field_theory F).

  Notation "0" := Azero : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation "a - b" := ((a + - b)%A) : A_scope.

  Notation vzero := (vzero 0%A).
  Notation vadd := (@vadd _ Aadd).
  Infix "+" := vadd : vec_scope.
  Notation vopp := (@vopp _ Aopp).
  Notation "- v" := (vopp v) : vec_scope.
  Notation vsub a b := (a + - b).
  Notation "a - b" := ((a + (-b))%V) : vec_scope.
  Notation vcmul := (@vcmul _ Amul _).
  Infix "\.*" := vcmul : vec_scope.
  Notation vdot := (@vdot _ Aadd Azero Amul).

  Infix "+" := Vadd : VectorSpace_scope.
  Notation "0" := Vzero : VectorSpace_scope.
  Notation "- v" := (Vopp v) : VectorSpace_scope.
  Notation Vsub u v := (u + -v).
  Infix "-" := Vsub : VectorSpace_scope.
  Infix "\.*" := Vcmul : VectorSpace_scope.
  Notation vsum := (@vsum _ Vadd 0 _).
  
  (** Linear combination of v1,v2, ..., vn by coefficients c1,c2, ..., cn *)
  Definition lcomb {n} (cs : @vec A n) (vs : @vec V n) : V :=
    vsum (vmap2 Vcmul cs vs).

  (** 0 * v1 + 0 * v2 + ... + 0 * vn = 0 *)
  Lemma lcomb_coef_0 : forall {n} (vs : @vec V n), lcomb vzero vs = 0.
  Proof.
    intros. unfold lcomb. apply vsum_eq0. intros. rewrite vnth_vmap2.
    rewrite vnth_vzero. rewrite vs_vcmul_0_l. auto.
  Qed.

  (** c1 * 0 + c2 * 0 + ... + cn * 0 = 0 *)
  Lemma lcomb_vec_0 : forall {n} (cs : @vec A n), lcomb cs (@Vector.vzero _ Vzero _) = 0.
  Proof.
    intros. unfold lcomb. apply vsum_eq0. intros. rewrite vnth_vmap2.
    rewrite vnth_vzero. rewrite vs_vcmul_0_r. auto.
  Qed.

  (** (c1 + c2) * v = c1 * v + c2 * v *)
  Lemma lcomb_coef_add : forall {n} (vs : @vec V n) c1 c2,
      lcomb (c1 + c2)%V vs = lcomb c1 vs + lcomb c2 vs.
  Proof.
    intros. unfold lcomb. rewrite vsum_add. apply vsum_eq; intros.
    rewrite !vnth_vmap2. rewrite vs_vcmul_aadd. auto.
  Qed.

  (** (- c) * v = - (c * v) *)
  Lemma lcomb_coef_opp : forall {n} (vs : @vec V n) c,
      lcomb (- c)%V vs = - (lcomb c vs).
  Proof.
    intros. unfold lcomb. rewrite vsum_opp. apply vsum_eq; intros.
    rewrite !vnth_vmap2. rewrite vnth_vopp. rewrite vs_vcmul_opp. auto.
  Qed.

  (** (c1 - c2) * v = c1 * v - c2 * v *)
  Lemma lcomb_coef_sub : forall {n} (vs : @vec V n) c1 c2,
      lcomb (c1 - c2)%V vs = lcomb c1 vs - lcomb c2 vs.
  Proof.
    intros. rewrite lcomb_coef_add. rewrite lcomb_coef_opp. auto.
  Qed.

  (** (a .* c) .* v = a .* (c .* v) *)
  Lemma lcomb_coef_cmul : forall {n} (vs : @vec V n) a c,
      lcomb (a \.* c)%V vs = a \.* (lcomb c vs).
  Proof.
    intros. unfold lcomb. rewrite vsum_cmul_l_ext.
    - apply vsum_eq; intros. rewrite !vnth_vmap2. rewrite vnth_vcmul.
      apply vs_vcmul_assoc.
    - intros. apply vs_vcmul_0_r.
    - intros. apply vs_vcmul_vadd.
  Qed.

  (** (veye i) * v = v $ i *)
  Lemma lcomb_coef_veye : forall {n} (vs : @vec V n) i,
      lcomb (veye Azero Aone i) vs = vs.[i].
  Proof.
    intros. unfold lcomb. apply vsum_unique with (i:=i).
    - rewrite vnth_vmap2. rewrite vnth_veye_eq. apply vs_vcmul_1_l.
    - intros. rewrite vnth_vmap2. rewrite vnth_veye_neq; auto. apply vs_vcmul_0_l.
  Qed.

  (** (insert c i ci) * vs = c * (remove vs i) + ci * (vs.i) *)
  Lemma lcomb_coef_vinsert :
    forall {n} (c : @vec A n) (vs : @vec V (S n)) (i : fin (S n)) (ci : A),
      lcomb (vinsert c i ci) vs =
        Vadd (lcomb c (vremove vs i)) (Vcmul ci vs.[i]).
  Proof.
    intros. unfold lcomb.
    rewrite (vmap2_vinsert_l (Azero:=Azero)(Bzero:=Vzero)(Czero:=Vzero)).
    rewrite vsum_vinsert. auto.
  Qed.
    
  (** (insert c i 0) * vs = c * (remove vs i) *)
  Lemma lcomb_coef_vinsert_0 :
    forall {n} (c : @vec A n) (vs : @vec V (S n)) (i : fin (S n)),
      lcomb (vinsert c i Azero) vs = lcomb c (vremove vs i).
  Proof.
    intros. rewrite lcomb_coef_vinsert. rewrite vs_vcmul_0_l at 1. monoid.
  Qed.

  (** (insert c i 0) * vs = (insert c i (-1)) * vs + vs.i *)
  Lemma lcomb_coef_vinsert_neg1 :
    forall {n} (c : @vec A n) (vs : @vec V (S n)) (i : fin (S n)),
      lcomb (vinsert c i Azero) vs =
        Vadd (lcomb (vinsert c i (Aopp Aone)) vs) (vs$i).
  Proof.
    intros. rewrite !lcomb_coef_vinsert. rewrite associative. f_equal.
    replace (vs i) with (Aone \.* vs i) at 3 by apply vs_vcmul_1_l.
    rewrite <- vs_vcmul_aadd. f_equal. group.
  Qed.

  (** (vset cs i a) * vs = cs * vs + (a - cs $ i) * (vs $ i) *)
  Lemma lcomb_coef_vset :
    forall {n} (cs : @vec A n) (vs : @vec V n) (i : fin n) (a : A),
      lcomb (vset cs i a) vs = lcomb cs vs + (a - cs $ i)%A \.* (vs $ i).
  Proof.
    intros. unfold lcomb.
    replace ((a - cs$i)%A \.* vs$i)
      with (vsum (vset (@Vector.vzero _ Vzero n) i ((a - cs$i)%A \.* vs i))).
    - apply vsum_add. intros j. rewrite !vnth_vmap2. destruct (i ??= j).
      + rewrite e. rewrite !vnth_vset_eq. rewrite <- vs_vcmul_aadd. f_equal. ring.
      + rewrite !vnth_vset_neq; auto. rewrite vnth_vzero. monoid.
    - apply vsum_unique with (i:=i).
      + rewrite vnth_vset_eq. auto.
      + intros. rewrite vnth_vset_neq; auto.
  Qed.

  (** cs * (vset vs i u) = cs * vs + (cs $ i) * (u - vs $ i) *)
  Lemma lcomb_vec_vset :
    forall {n} (cs : @vec A n) (vs : @vec V n) (i : fin n) (u : V),
      lcomb cs (vset vs i u) = lcomb cs vs + (cs $ i) \.* (u - vs $ i).
  Proof.
    intros. unfold lcomb.
    replace (cs$i \.* (u - vs$i))
      with (vsum (vset (@Vector.vzero _ Vzero n) i (cs$i \.* (u - vs$i)))).
    - apply vsum_add. intros j. rewrite !vnth_vmap2. destruct (i ??= j).
      + rewrite e. rewrite !vnth_vset_eq. rewrite <- vs_vcmul_vadd. f_equal.
        rewrite commutative. rewrite associative. rewrite inverseLeft. monoid.
      + rewrite !vnth_vset_neq; auto. rewrite vnth_vzero. monoid.
    - apply vsum_unique with (i:=i).
      + rewrite vnth_vset_eq. auto.
      + intros. rewrite vnth_vset_neq; auto.
  Qed.

  (** lcomb (vremove cs i) (vremove vs i) = (lcomb cs vs) - (cs.i * vs.i) *)
  Lemma lcomb_vremove_vremove : forall {n} (cs : @vec A (S n)) (vs : @vec V (S n)) i,
      lcomb (vremove cs i) (vremove vs i) = (lcomb cs vs) - (cs$i \.* vs$i).
  Proof.
    intros. unfold lcomb. rewrite (@vmap2_vremove_vremove _ _ _ Azero Vzero Vzero).
    rewrite vsum_vremove. auto.
  Qed.
  
  (** lcomb (vconsH c cs) vs = c * (vhead vs) + (lcomb cs (vremoveH vs)) *)
  Lemma lcomb_coef_vconsH : forall {n} (cs : @vec A n) (vs : @vec V (S n)) (c : A),
      lcomb (vconsH c cs) vs = c \.* (vhead vs) + lcomb cs (vremoveH vs).
  Proof.
    intros. unfold lcomb. rewrite vsumS_head. f_equal.
    - rewrite vnth_vmap2. f_equal. rewrite vhead_eq. f_equal. apply sig_eq_iff; auto.
    - apply vsum_eq; intros i. rewrite !vnth_vmap2. f_equal.
      erewrite vnth_vconsH_gt0. rewrite fin2PredRangePred_fin2SuccRangeSucc. auto.
      Unshelve. rewrite fin2nat_fin2SuccRangeSucc. lia.
  Qed.
  
  (** lcomb (vconsT cs c) vs = (lcomb cs (vremoveT vs)) + c * (vtail vs) *)
  Lemma lcomb_coef_vconsT : forall {n} (cs : @vec A n) (vs : @vec V (S n)) (c : A),
      lcomb (vconsT cs c) vs = lcomb cs (vremoveT vs) + c \.* (vtail vs).
  Proof.
    intros. unfold lcomb. rewrite vsumS_tail. f_equal.
    - apply vsum_eq; intros i. rewrite !vnth_vmap2. f_equal.
      erewrite vnth_vconsT_lt. f_equal. apply fin2PredRange_fin2SuccRange.
    - rewrite vnth_vmap2. f_equal.
      rewrite vnth_vconsT_n; auto. rewrite fin2nat_nat2finS; auto.
      Unshelve. rewrite fin2nat_fin2SuccRange. apply fin2nat_lt.
  Qed.

  (** lcomb cs (vconsT vs u) = (lcomb (vremoveT cs) vs) + (vtail cs) * u *)
  Lemma lcomb_vec_vconsT : forall {n} (cs : @vec A (S n)) (vs : @vec V n) (u : V),
      lcomb cs (vconsT vs u) = lcomb (vremoveT cs) vs + (vtail cs) \.* u.
  Proof.
    intros. unfold lcomb. rewrite vsumS_tail. f_equal.
    - apply vsum_eq; intros i. rewrite !vnth_vmap2. f_equal.
      erewrite vnth_vconsT_lt. f_equal. apply fin2PredRange_fin2SuccRange.
    - rewrite vnth_vmap2. f_equal.
      rewrite vnth_vconsT_n; auto. rewrite fin2nat_nat2finS; auto.
      Unshelve. rewrite fin2nat_fin2SuccRange. apply fin2nat_lt.
  Qed.

  (** lcomb cs (vconsH u vs) = (vhead cs) * u + (lcomb (vremoveH cs) vs) *)
  Lemma lcomb_vec_vconsH : forall {n} (cs : @vec A (S n)) (vs : @vec V n) (u : V),
      lcomb cs (vconsH u vs) = (vhead cs) \.* u + lcomb (vremoveH cs) vs.
  Proof.
    intros. unfold lcomb. rewrite vsumS_head. f_equal.
    - rewrite vnth_vmap2. f_equal. rewrite vhead_eq. f_equal. apply sig_eq_iff; auto.
    - apply vsum_eq; intros i. rewrite !vnth_vmap2. f_equal.
      erewrite vnth_vconsH_gt0. f_equal. apply fin2PredRangePred_fin2SuccRangeSucc.
      Unshelve. rewrite fin2nat_fin2SuccRangeSucc. lia.
  Qed.

  (** lcomb (vconsT cs c) (vconsT vs v) = (lcomb cs vs) + c * v *)
  Lemma lcomb_vconsT_vconsT : forall {n} (cs : @vec A n) (vs : @vec V n) c v,
      lcomb (vconsT cs c) (vconsT vs v) = lcomb cs vs + c \.* v.
  Proof.
    intros. unfold lcomb. rewrite vsumS_tail. f_equal.
    - apply vsum_eq; intros i. rewrite !vnth_vmap2. erewrite !vnth_vconsT_lt.
      rewrite !fin2PredRange_fin2SuccRange. auto.
    - rewrite vnth_vmap2. erewrite !vnth_vconsT_n; auto.
      all: rewrite fin2nat_nat2finS; auto.
      Unshelve. rewrite fin2nat_fin2SuccRange. apply fin2nat_lt.
      rewrite fin2nat_fin2SuccRange. apply fin2nat_lt.
  Qed.

  (** lcomb (vconsH c cs) (vconsH v vs) = c * v + (lcomb cs vs) *)
  Lemma lcomb_vconsH_vconsH : forall {n} (cs : @vec A n) (vs : @vec V n) c v,
      lcomb (vconsH c cs) (vconsH v vs) = c \.* v + lcomb cs vs.
  Proof.
    intros. unfold lcomb. rewrite vsumS_head. f_equal.
    apply vsum_eq; intros i. rewrite !vnth_vmap2. erewrite !vnth_vconsH_gt0.
    rewrite !fin2PredRangePred_fin2SuccRangeSucc. auto.
    Unshelve. rewrite fin2nat_fin2SuccRangeSucc. lia.
    rewrite fin2nat_fin2SuccRangeSucc. lia.
  Qed.

  (** lcomb (vapp cs ds) (vapp us vs) = (lcomb cs us) + (lcomb ds vs) *)
  Lemma lcomb_vapp_vapp : forall {n m} (cs : @vec A n) (ds : @vec A m)
                            (us : @vec V n) (vs : @vec V m),
      lcomb (vapp cs ds) (vapp us vs) = (lcomb cs us) + (lcomb ds vs).
  Proof.
    intros. unfold lcomb. rewrite vmap2_vapp_vapp.
    remember (vmap2 Vcmul cs us) as u.
    remember (vmap2 Vcmul ds vs) as v.
    apply vsum_vapp.
  Qed.

  (** lcomb (lcomb u D) v = lcomb u (lcomb D v) *)
  (* For example:
     (u1,u2,u3) [D11,D12] [v1]  记作 u*D*v，
                [D21,D22] [v2]
                [D31,D32]
     (u*D)*v = <u,col(D,1)> v1 + <u,col(D,2)> v2
             = (u1D11+u2D21+u3D31)v1 + (u1D12+u2D22+u3D32)v2
     u*(D*v) = u1 <row(D,1),v> + u2 <row(D,2),v> + u3 <row(D,3),v>
             = u1(D11v1+D12v2)+u2(D21v1+D22v2)+u3(D31v1+D32v2) *)
  Lemma lcomb_assoc : forall {r c} (u : @vec A c) (D : @vec (@vec A r) c) (v : @vec V r),
      lcomb (fun j => vdot u (fun i => D i j)) v = lcomb u (fun i : fin c => lcomb (D i) v).
  Proof.
    intros. unfold lcomb, vdot, vmap2.
    pose proof (vsum_vsum_exchg c r (fun i j => Vcmul (Amul (u i) (D i j)) (v j))).
    match goal with
    | H: ?a1 = ?a2 |- ?b1 = ?b2 => replace b1 with a2; [replace b2 with a1|]; auto
    end.
    - f_equal. extensionality i. apply vsum_cmul_extX; intros.
      apply vs_vcmul_0_r. apply vs_vcmul_vadd. apply vs_vcmul_assoc.
    - f_equal. extensionality i. apply vsum_cmul_extV; intros; auto.
      apply vs_vcmul_0_l. apply vs_vcmul_aadd.
  Qed.

  (** (∃ ds, vs = fun i => lcomb ds.i vs) -> (∀ i, ∃ cs, lcomb cs vs = vs.i) *)
  Lemma lcomb_any_ex_imply_all_ex : forall {r s} (us : @vec V r) (vs : @vec V s),
      (exists ds : @vec (@vec A r) s, vs = fun i => lcomb (ds$i) us) ->
      (forall i : fin s, exists cs : @vec A r, lcomb cs us = vs i).
  Proof. intros. destruct H as [d H]. rewrite H. exists (d i); auto. Qed.

  (* Tips, this proof is tricky:
     1. a special form: ∀ i, ∃ c, lcomb c u = v.i |- ∃ d, v = fun i => lcomb (d.i) u
     2. induction on parameter n and use vconsH to use inductive hypothesis
   *)
  (** (∀ i, ∃ cs, lcomb cs us = vs.i) -> (∃ ds, vs = fun i => lcomb ds.i us) *)
  Lemma lcomb_all_ex_imply_any_ex : forall {r s} (us : @vec V r) (vs : @vec V s),
      (forall i : fin s, exists cs : @vec A r, lcomb cs us = vs i) ->
        (exists ds : @vec (@vec A r) s, vs = fun i => lcomb (ds$i) us).
  Proof.
    intros. generalize dependent s. induction s; intros.
    - exists (@mkvec0 _ (@Vector.vzero _ Azero r)). apply v0eq.
    - rewrite <- (vconsH_vhead_vremoveH vs). 
      assert (exists cs : vec r, vhead vs = lcomb cs us).
      { specialize (H fin0). destruct H as [cs H]. exists cs. rewrite H. auto. }
      assert (forall i : fin s, exists cs : vec r, lcomb cs us = vremoveH vs i).
      { intros. specialize (H (fin2SuccRangeSucc i)). destruct H as [cs H].
        exists cs. rewrite H. auto. }
      destruct H0 as [c0 H0].
      specialize (IHs (vremoveH vs) H1). destruct IHs as [c1 IHs].
      rewrite H0,IHs. unfold vconsH.
      exists (fun i : fin (S s) =>
           match (fin2nat i ??= 0)%nat with
           | left _ => c0
           | right n => c1 (fin2PredRangePred i (neq_0_lt_stt (fin2nat i) n))
           end).
      apply veq_iff_vnth. intros. destruct (_??=_)%nat; auto.
  Qed.
    
End lcomb.


(** ** linear equation *)
Section leqs.
  Context `{HVectorSpace : VectorSpace}.
  Notation lcomb := (@lcomb _ _ Vadd Vzero Vcmul).

  (* 含有 s 个方程的 n 元线性方程组。
     其中，a称为系数，x称为未知量，b称为常数项。*)
  Record leqs {n s : nat} := {
      leqs_a : @vec (@vec A n) s;
      leqs_b : @vec V s
    }.

  (* 若n元有序数组(c1,c2,...,cn)'代入方程后使得每个方程是恒等式，则称它是
     该方程组的一个解。方程组的所有解组成的集合称为这个方程组的解集。
     符合实际问题需要的解称为可行解。*)
  
  (* x is the answer of the equation `e` *)
  Definition leqsAnswer {n s} (e : @leqs n s) (x : @vec V n) : Prop :=
    vmap (fun ai => lcomb ai x) (leqs_a e) = (leqs_b e).
  
  (* n元线性方程组，s和n之间可能的关系：s = n, s < n, s > n *)

  (* 如何求解线性方程组？方程组的消元法。 *)
  (* 线性方程组的初等变换，三种。 *)
  (* 阶梯形方程组，简化阶梯形方程组 *)
  (* Check mrowK. *)
  (* Check mrowSwap. *)
  (* Check mrowKAdd. *)

  (* 可以在这个模块中开发线性方程组的理论 *)
  (* MatrixGauss *)
(* 若n元线性方程组I与II的解集相同，则称方程组I与II同解。
   n元线性方程组的“同解”关系是等价关系。
   不难看出，n元线性方程组经过初等变换1,2,3，得到的方程组与原方程同解。
   因此，经过一系列初等变换变成的简化阶梯形方程组与原线性方程组同解。*)

  (*  在求解过程中，只对线性方程组的系数和常数项进行运算，相应的有系数矩阵和增广矩阵。 *)
   
End leqs.
 

(** ** linearly representable *)
Section lrep.
  Context `{HVectorSpace : VectorSpace}.

  (* Notation "0" := Azero : A_scope. *)
  (* Notation vzero := (vzero 0%A). *)
  (* Notation vadd := (@vadd _ Aadd). *)
  (* Notation vopp := (@vopp _ Aopp). *)
  (* Notation vsub := (@vsub _ Aadd Aopp). *)
  (* Infix "+" := vadd : vec_scope. *)
  (* Notation "- v" := (vopp v) : vec_scope. *)
  (* Infix "-" := vsub : vec_scope. *)

  (* Infix "+" := Vadd : VectorSpace_scope. *)
  (* Notation "0" := Vzero : VectorSpace_scope. *)
  (* Notation "- v" := (Vopp v) : VectorSpace_scope. *)
  (* Notation Vsub u v := (u + -v). *)
  (* Infix "-" := Vsub : VectorSpace_scope. *)
  (* Notation vsum := (@vsum _ Vadd 0 _). *)
  Notation lcomb := (@lcomb _ _ Vadd Vzero Vcmul).

  (* 向量 u 可由向量组 vs 线性表示 *)
  Definition lrep {n} (vs : @vec V n) (u : V) : Prop :=
    exists (cs : @vec A n), lcomb cs vs = u.

  (* 向量 u 不能由向量组 vs 线性表示 *)
  Definition nolrep {n} (vs : @vec V n) (u : V) := (~ (lrep vs u)).

  (* 向量组 vs 中的任意向量 v 可由 vs 线性表示 *)
  Lemma lrep_in : forall {n} (vs : @vec V n), vforall vs (lrep vs).
  Proof. intros. hnf. intros. hnf. exists (veye Azero Aone i). apply lcomb_coef_veye. Qed.
  
End lrep.


(** ** 向量组可由向量组“线性表示(线性表出)” *)
Section lreps.
  Context `{HVectorSpace : VectorSpace}.

  (* Notation "0" := Azero : A_scope. *)
  (* Notation vzero := (vzero 0%A). *)
  (* Notation vadd := (@vadd _ Aadd). *)
  (* Notation vopp := (@vopp _ Aopp). *)
  (* Notation vsub := (@vsub _ Aadd Aopp). *)
  (* Infix "+" := vadd : vec_scope. *)
  (* Notation "- v" := (vopp v) : vec_scope. *)
  (* Infix "-" := vsub : vec_scope. *)

  (* Infix "+" := Vadd : VectorSpace_scope. *)
  (* Notation "0" := Vzero : VectorSpace_scope. *)
  (* Notation "- v" := (Vopp v) : VectorSpace_scope. *)
  (* Notation Vsub u v := (u + -v). *)
  (* Infix "-" := Vsub : VectorSpace_scope. *)
  (* Notation vsum := (@vsum _ Vadd 0 _). *)
  Notation lcomb := (@lcomb _ _ Vadd Vzero Vcmul).
  Notation lrep := (@lrep _ _ Vadd Vzero Vcmul).

  (* 向量组 vs 可线性表示向量组 us *)
  Definition lreps {r s} (vs : @vec V s) (us : @vec V r) : Prop :=
    vforall us (lrep vs).

  (* 向量组 us 不能由向量组 vs 线性表示 *)
  Definition nolreps {r s} (vs : @vec V r) (us : @vec V s) := (~ (lreps vs us)).

  (** lreps is reflexive *)
  Lemma lreps_refl : forall {r} (vs : @vec V r), lreps vs vs.
  Proof.
    intros. unfold lreps, vforall, lrep. intros.
    exists (veye Azero Aone i). rewrite lcomb_coef_veye. auto.
  Qed.

  (** If `us` could represent `vs` and `vs` could represent `u`, then `us` could
      represent `u` *)
  Lemma lreps_lrep : forall {r s} (us : @vec V r) (vs : @vec V s) (u : V),
      lreps us vs -> lrep vs u -> lrep us u.
  Proof.
    intros. unfold lreps, vforall in H. unfold lrep in *.
    destruct H0 as [c H0]. rewrite <- H0.
    apply (lcomb_all_ex_imply_any_ex (Azero:=Azero)) in H.
    destruct H as [d H]. rewrite H.
    exists (fun i => vsum Aadd Azero (vmap2 Amul c (fun j => d j i))).
    rewrite <- lcomb_assoc. f_equal.
  Qed.

  (** lreps is transitive *)
  Lemma lreps_trans :
    forall {r s t} (us : @vec V r) (vs : @vec V s) (ws : @vec V t),
      lreps us vs -> lreps vs ws -> lreps us ws.
  Proof.
    (* 丘老师的证明与此不同，也许我的证明更简单一些。 *)
    intros. unfold lreps, vforall. intros. apply lreps_lrep with (vs:=vs); auto.
  Qed.
  
End lreps.


(* ===================================================================== *)
(** ** Equivalent vectors *)
Section vsequiv.
  Context `{HVectorSpace : VectorSpace}.
  Notation lreps := (@lreps _ _ Vadd Vzero Vcmul).

  (** Two vector systems `us` and `vs` are equivalent *)
  Definition vsequiv {r s} (us : @vec V r) (vs : @vec V s) : Prop :=
    lreps us vs /\ lreps vs us.

  Infix "\~" := vsequiv (at level 70).
  
  Lemma vsequiv_refl : forall {n} (vs : @vec V n), vs \~ vs.
  Proof. intros. hnf. split; apply lreps_refl. Qed.

  Lemma vsequiv_sym : forall {r s} (us : @vec V r) (vs : @vec V s), us \~ vs -> vs \~ us.
  Proof. intros. hnf in *. destruct H; auto. Qed.

  Lemma vsequiv_trans : forall {r s t} (us : @vec V r) (vs : @vec V s) (ws : @vec V t),
      us \~ vs -> vs \~ ws -> us \~ ws.
  Proof.
    intros. hnf in *. destruct H,H0. split.
    apply lreps_trans with vs; auto.
    apply lreps_trans with vs; auto.
  Qed.
  
End vsequiv.


(* ===================================================================== *)
(** ** Span (由向量组生成(张成)的子空间 *)
Section lspan.
  Context `{HVectorSpace : VectorSpace}.
  Notation lrep := (@lrep _ _ Vadd Vzero Vcmul).

  Instance lspan_Struct {n} (vs : @vec V n) : SubSpaceStruct (lrep vs).
  Proof.
    unfold lrep. constructor.
    - exists (vzero Azero). apply lcomb_coef_0.
    - intros. pose proof u.prf; pose proof v.prf; simpl in *.
      destruct H as [c H], H0 as [c0 H0]. rewrite <- H, <- H0.
      exists (@vadd _ Aadd _ c c0). apply lcomb_coef_add.
    - intros. pose proof v.prf; simpl in *.
      destruct H as [c H]. rewrite <- H.
      exists (@vcmul _ Amul _ a c). apply lcomb_coef_cmul.
  Qed.

  (** 由向量组 vs 张成的子空间，记作 <vs> 或 <v1,v2,...,vn> *)
  #[export] Instance lspan {n} (vs : @vec V n) : VectorSpace Hadd Hzero Hopp Hcmul :=
    makeSubSpace (lspan_Struct vs).
End lspan.

          
(* 延长组相关，则缩短组必相关 *)
(* 缩短组无关，则延长组必无关   *)
(* 列多可由列少线性表出，则列多相关 *)
(* ===================================================================== *)
(** ** Linear Dependent, Linear Independent *)
Section ldep.
  Context `{HVectorSpace : VectorSpace}.
  Context {AeqDec : Dec (@eq A)}.
  Context {VeqDec : Dec (@eq V)}.

  Notation "- a" := (Aopp a) : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "1" := Aone : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv a b := (a * / b).
  Infix "/" := Adiv : A_scope.

  Infix "+" := Vadd : VectorSpace_scope.
  Notation "0" := Vzero : VectorSpace_scope.
  Notation vzero := (vzero Azero).
  Notation vsub := (@vsub _ Aadd Aopp).
  Infix "-" := vsub : vec_scope.
  Notation lcomb := (@lcomb _ _ Vadd Vzero Vcmul).
  Notation lrep := (@lrep _ _ Vadd Vzero Vcmul).
  Notation nolrep := (@nolrep _ _ Vadd Vzero Vcmul).
  Notation lreps := (@lreps _ _ Vadd Vzero Vcmul).
  Notation nolreps := (@nolreps _ _ _ Vadd Vzero Vcmul).

  (** Vectors {v1, v2, ..., vn} are linearly dependent *)
  (* 存在不全为0的系数，使得线性组合等于零向量 *)
  Definition ldep {n} (vs : @vec V n) : Prop :=
    exists (cs : @vec A n), cs <> vzero /\ lcomb cs vs = 0.

  (* Vectors v1, v2, ..., vn are linearly independent *)
  Definition lindep {n} (vs : @vec V n) : Prop := ~(ldep vs).

  (* 向量组 vs 要么相关，要么无关 *)
  Lemma ldep_or_lindep : forall {n} (vs : @vec V n), ldep vs \/ lindep vs.
  Proof. intros. unfold lindep. apply classic. Qed.
  
  (* 向量线性无关，iff，只有系数全为0的线性组合才会等于零向量。*)
  Lemma lindep_iff_coef0 : forall {n} (vs : @vec V n),
      lindep vs <-> (forall cs, lcomb cs vs = 0 -> cs = vzero).
  Proof.
    intros. unfold lindep, ldep. split; intros.
    - apply not_ex_all_not with (n:=cs) in H. apply not_and_or in H.
      destruct H; try easy. apply NNPP in H. auto.
    - intro. destruct H0 as [c [H0 H0']]. specialize (H c H0'). easy.
  Qed.

  (** 使用线性无关的向量组vs作出的两种线性组合时，必然是相同的系数 *)
  Lemma lindep_imply_coef_same : forall {n} (vs : @vec V n) c1 c2,
      lindep vs -> lcomb c1 vs = lcomb c2 vs -> c1 = c2.
  Proof.
    intros. rewrite lindep_iff_coef0 in H. specialize (H (c1 - c2)).
    apply vsub_eq0_iff_eq. apply H. rewrite lcomb_coef_sub. rewrite H0.
    apply vs_vadd_vopp_r.
  Qed.

  (** 若向量组vs线性无关，且向量u可由vs线性表出，则表出方式唯一 *)
  Lemma lindep_imply_coef_uniq : forall {n} (vs : @vec V n) u,
      lindep vs -> lrep vs u -> exists ! cs, u = lcomb cs vs.
  Proof.
    intros. unfold lrep in H0. destruct H0 as [cs H0]. exists cs. hnf. split; auto.
    intros. rewrite <- H0 in H1. apply lindep_imply_coef_same in H1; auto.
  Qed.

  (** 包含零向量的向量组，必定线性相关 *)
  Lemma ldep_if_contain_0 : forall {n} (vs : @vec V n), (exists i, vs $ i = Vzero) -> ldep vs.
  Proof.
    intros. destruct H as [i H]. hnf. exists (veye Azero Aone i). split.
    - apply veye_neq0. apply field_1_neq_0.
    - rewrite lcomb_coef_veye. auto.
  Qed.
  
  (** 线性无关的向量组，必不含零向量 *)
  Lemma lindep_then_all_not0 : forall {n} (vs : @vec V n),
      lindep vs -> forall i, vs $ i <> Vzero.
  Proof.
    intros n vs H. apply not_ex_all_not. intro. apply ldep_if_contain_0 in H0; auto.
  Qed.

  (** 单个向量线性相关，iff，该向量为零 *)
  Lemma ldep_vec1_iff_eq0 : forall (vs : @vec V 1), ldep vs <-> vs = (fun i => Vzero).
  Proof.
    intros. split; intros.
    - unfold ldep in H. destruct H as [c [H H']]. cbv in H'.
      rewrite vs_vadd_0_l in H'. apply vs_vcmul_eq0_imply_k0_or_v0 in H'. destruct H'.
      + rewrite v1eq_iff in H. erewrite nat2finS_eq in H. cbv in H.
        apply H in H0. easy.
      + apply v1eq_iff. erewrite nat2finS_eq; auto. apply H0.
    - apply ldep_if_contain_0. exists (nat2finS 0). rewrite H. auto.
  Qed.
  
  (** 单个向量线性无关，iff，该向量不为零 *)
  Lemma lindep_vec1_iff_neq0 : forall (vs : @vec V 1), lindep vs <-> vs <> (fun i => Vzero).
  Proof. intros. unfold lindep. rewrite ldep_vec1_iff_eq0. easy. Qed.
  
  (** 两个原则：
      1. 如果向量组的一个部分组线性相关，那么整个向量组也线性相关
      2. 如果向量组线性无关，那么它的任何一个部分组也线性无关
      表现出来是如下的几组引理
   *)

  (** vs线性相关，则{u,vs}线性相关 *)
  Lemma ldep_imply_vconsH_ldep : forall {n} (vs : @vec V n) (u : V),
      ldep vs -> ldep (vconsH u vs).
  Proof.
    intros. hnf in *. destruct H as [cs [H H0]].
    (* c1v1+c2v2+...+cnvn=0 |- du+d1v1+...+dnvn = 0 *)
    exists (vconsH Azero cs). split.
    - apply vconsH_neq0_iff. auto.
    - rewrite lcomb_vconsH_vconsH. rewrite H0. monoid. apply vs_vcmul_0_l.
  Qed.

  (** vs线性相关，则{vs,u}线性相关 *)
  Lemma ldep_imply_vconsT_ldep : forall {n} (vs : @vec V n) (u : V),
      ldep vs -> ldep (vconsT vs u).
  Proof.
    intros. hnf in *. destruct H as [cs [H H0]].
    (* c1v1+c2v2+...+cnvn=0 |- d1v1+d2v2+...+dnvn+duvu = 0 *)
    exists (vconsT cs Azero). split.
    - apply vconsT_neq0_iff. auto.
    - rewrite lcomb_vconsT_vconsT. rewrite H0. monoid. apply vs_vcmul_0_l.
  Qed.
  
  (** {u,vs}线性无关，则vs线性无关 *)
  Lemma vconsH_lindep_imply_lindep : forall {n} (vs : @vec V n) (u : V),
      lindep (vconsH u vs) -> lindep vs.
  Proof.
    intros. hnf in *. intros. destruct H. apply ldep_imply_vconsH_ldep; auto.
  Qed.
  
  (** {vs,u}线性无关，则vs线性无关 *)
  Lemma vconsT_lindep_imply_lindep : forall {n} (vs : @vec V n) (u : V),
      lindep (vconsT vs u) -> lindep vs.
  Proof.
    intros. hnf in *. intros. destruct H. apply ldep_imply_vconsT_ldep; auto.
  Qed.

  (** vremoveH vs 线性相关，则 vs 线性相关 *)
  Lemma vremoveH_ldep_imply_ldep : forall {n} (vs : @vec V (S n)),
      ldep (vremoveH vs) -> ldep vs.
  Proof.
    intros. rewrite <- vconsH_vhead_vremoveH. apply ldep_imply_vconsH_ldep; auto.
  Qed.

  (** vremoveT vs 线性相关，则 vs 线性相关 *)
  Lemma vremoveT_ldep_imply_ldep : forall {n} (vs : @vec V (S n)),
      ldep (vremoveT vs) -> ldep vs.
  Proof.
    intros. rewrite <- (vconsT_vremoveT_vtail vs (Azero:=Vzero)).
    apply ldep_imply_vconsT_ldep. auto.
  Qed.

  (** vs 线性无关，则 vremoveH vs 线性无关 *)
  Lemma lindep_imply_vremoveH_lindep : forall {n} (vs : @vec V (S n)),
      lindep vs -> lindep (vremoveH vs).
  Proof.
    intros. unfold lindep in *. intro. destruct H.
    apply vremoveH_ldep_imply_ldep; auto.
  Qed.

  (** vs 线性无关，则 vremoveT vs 线性无关 *)
  Lemma lindpe_imply_vremoveT_lindep : forall {n} (vs : @vec V (S n)),
      lindep vs -> lindep (vremoveT vs).
  Proof.
    intros. unfold lindep in *. intro. destruct H.
    apply vremoveT_ldep_imply_ldep; auto.
  Qed.

  (** us线性相关，则{us,vs}线性相关 *)
  Lemma ldep_imply_vapp_ldep_L : forall {n m} (us : @vec V n) (vs : @vec V m),
      ldep us -> ldep (vapp us vs).
  Proof.
    intros. hnf in *. destruct H as [cs [H H0]].
    (* c1u1+...+cnun=0 |- e1u1+...+enun + f1v1+...+fmfm = 0 *)
    exists (vapp cs (@Vector.vzero _ Azero m)). split.
    - rewrite vapp_eq0_iff. apply or_not_and. auto.
    - rewrite lcomb_vapp_vapp. rewrite H0. rewrite lcomb_coef_0. monoid.
  Qed.

  (** vs线性相关，则{us,vs}线性相关 *)
  Lemma ldep_imply_vapp_ldep_R : forall {n m} (us : @vec V n) (vs : @vec V m),
      ldep vs -> ldep (vapp us vs).
  Proof.
    intros. hnf in *. destruct H as [ds [H H0]].
    (* d1v1+...+dnvn=0 |- e1u1+...+enun + f1v1+...+fmfm = 0 *)
    exists (vapp (@Vector.vzero _ Azero n) ds). split.
    - rewrite vapp_eq0_iff. apply or_not_and. auto.
    - rewrite lcomb_vapp_vapp. rewrite H0. rewrite lcomb_coef_0. monoid.
  Qed.

  (** {us,vs}线性无关，则us线性无关 *)
  Lemma vapp_lindep_imply_lindep_L : forall {n m} (us : @vec V n) (vs : @vec V m),
      lindep (vapp us vs) -> lindep us.
  Proof.
    unfold lindep. intros. intro. destruct H. apply ldep_imply_vapp_ldep_L; auto.
  Qed.

  (** {us,vs}线性无关，则vs线性无关 *)
  Lemma vapp_lindep_imply_lindep_R : forall {n m} (us : @vec V n) (vs : @vec V m),
      lindep (vapp us vs) -> lindep vs.
  Proof.
    unfold lindep. intros. intro. destruct H. apply ldep_imply_vapp_ldep_R; auto.
  Qed.
    
  (** vs(n)线性相关，则vs(n+m)线性相关 *)
  Lemma vheadN_ldep_imply_ldep : forall {n m} (vs : @vec V (n + m)),
      ldep (vheadN vs) -> ldep vs.
  Proof.
    intros. rewrite <- vapp_vheadN_vtailN. apply ldep_imply_vapp_ldep_L; auto.
  Qed.
    
  (** vs(m)线性相关，则vs(n+m)线性相关 *)
  Lemma vtailN_ldep_imply_ldep : forall {n m} (vs : @vec V (n + m)),
      ldep (vtailN vs) -> ldep vs.
  Proof.
    intros. rewrite <- vapp_vheadN_vtailN. apply ldep_imply_vapp_ldep_R; auto.
  Qed.
    
  (** vs(n+m)线性无关，则vs(n)线性无关 *)
  Lemma lindep_imply_vheadN_lindep : forall {n m} (vs : @vec V (n + m)),
      lindep vs -> lindep (vheadN vs).
  Proof.
    unfold lindep. intros. intro. destruct H. apply vheadN_ldep_imply_ldep; auto.
  Qed.
    
  (** vs(n+m)线性无关，则vs(m)线性无关 *)
  Lemma lindep_imply_vtailN_lindep : forall {n m} (vs : @vec V (n + m)),
      lindep vs -> lindep (vtailN vs).
  Proof.
    unfold lindep. intros. intro. destruct H. apply vtailN_ldep_imply_ldep; auto.
  Qed.
  
  (** 线性相关 <-> 其中至少有一个向量可以由其余向量线性表示 *)
  Lemma ldep_iff_exist_lrep : forall {n} (vs : @vec V (S n)),
      ldep vs <-> exists i, lrep (vremove vs i) (vs $ i).
  Proof.
    intros. unfold ldep,lrep. split; intros.
    - destruct H as [c [H H1]]. apply vneq_iff_exist_vnth_neq in H.
      destruct H as [i H]. exists i.
      (* c1v1+c2v2+civi=0 -> d1v1+d2v2=vi. So, d:=(-c1/ci,-c2/ci) *)
      exists (vmap (fun x => Aopp x / (c$i)) (vremove c i)).
      rewrite (@vmap_vremove _ _ Azero Azero). rewrite lcomb_vremove_vremove.
      rewrite vnth_vmap. rewrite !vs_vcmul_opp at 1. rewrite group_opp_opp.
      rewrite field_mulInvR; auto. rewrite vs_vcmul_1_l at 1.
      replace (vmap (fun x => - x / c i) c) with (vcmul (Amul:=Amul) (- (/ c i)) c).
      + rewrite lcomb_coef_cmul. rewrite H1. rewrite vs_vcmul_0_r at 1. monoid.
      + apply veq_iff_vnth; intros j. rewrite vnth_vcmul, vnth_vmap.
        rewrite !ring_mul_opp_l at 1. f_equal. amonoid.
    - destruct H as [i [c H]].
      (* c := (c1,c2,..,c(i-1),-1,c(i+1),...,cn) *)
      exists (vinsert c i (Aopp Aone)). split.
      + apply vinsert_neq0_iff. right. apply field_neg1_neq_0.
      + pose proof (lcomb_coef_vinsert_0 c vs i).
        pose proof (lcomb_coef_vinsert_neg1 c vs i).
        rewrite H0 in H1. rewrite H in H1.
        symmetry in H1. apply vs_add_eqR_imply0 in H1. auto.
  Qed.

  (** 线性无关 <-> 其中每一个向量都不能由其余向量线性表示 *)
  Lemma lindep_iff_none_lrep : forall {n} (vs : @vec V (S n)),
      lindep vs <-> forall i, ~ (lrep (vremove vs i) (vs $ i)).
  Proof.
    intros. unfold lindep. rewrite ldep_iff_exist_lrep. split; intro.
    apply not_ex_all_not; auto. apply all_not_not_ex; auto.
  Qed.

  (** 向量u可以由vs线性表示，则{vs,u}线性相关 *)
  Lemma lrep_imply_vconsT_ldep : forall {n} (vs : @vec V n) (u : V),
      lrep vs u -> ldep (vconsT vs u).
  Proof.
   intros. unfold lrep,ldep in *. destruct H as [cs H].
   (* c1v1+civi=u |- d1v1+divi+dnu = 0, So, d:=(c1,ci,-1) *)
   exists (vconsT cs (-(1))). split.
   - rewrite vconsT_eq0_iff. apply or_not_and. right. apply field_neg1_neq_0.
   - rewrite lcomb_vconsT_vconsT. rewrite H.
     rewrite vs_vcmul_opp1. apply vs_vadd_vopp_r.
  Qed.

  (** 向量u可以由vs线性表示，则{u,vs}线性相关 *)
  Lemma lrep_imply_vconsH_ldep : forall {n} (vs : @vec V n) (u : V),
      lrep vs u -> ldep (vconsH u vs).
  Proof.
   intros. unfold lrep,ldep in *. destruct H as [cs H].
   (* c1v1+civi=u |- d1u+d2v2+divi = 0, So, d:=(-1,c2,ci) *)
   exists (vconsH (-(1)) cs). split.
   - rewrite vconsH_eq0_iff. apply or_not_and. left. apply field_neg1_neq_0.
   - rewrite lcomb_vconsH_vconsH. rewrite H.
     rewrite vs_vcmul_opp1 at 1. apply vs_vadd_vopp_l.
  Qed.
  
  (** 设向量组vs线性无关，向量组{vs,u}线性相关，则向量u可由vs线性表示 *)
  Theorem ldep_vconsT_lindep_imply_lrep : forall {n} (vs : @vec V n) (u : V),
      lindep vs -> ldep (vconsT vs u) -> lrep vs u.
  Proof.
    intros. unfold lindep, ldep in *. destruct H0 as [cs [H0 H1]].
    destruct (Aeqdec (vtail cs) Azero) as [H2|H2].
    - (* 若 c.n <> 0，则 (c1,c2,...,cn) 不全为0，并且 c1v1+c2v2+..+cnvn=0,
         于是 v1,v2,...,vn 线性相关，与 H 矛盾 *)
      assert (exists cs, cs <> vzero /\ lcomb cs vs = 0); try tauto.
      exists (vremoveT cs). split.
      + apply vremoveT_neq0_if; auto.
      + rewrite lcomb_vec_vconsT in H1. rewrite H2 in H1.
        rewrite vs_vcmul_0_l in H1 at 1. rewrite vs_vadd_0_r in H1. auto.
    - (* 从而，u = (-c1/cn)*v1 + (-c2/cn)*v2 + ... *)
      hnf. exists (vcmul (Amul:=Amul) (- / vtail cs) (vremoveT cs)).
      rewrite lcomb_coef_cmul. rewrite lcomb_vec_vconsT in H1.
      remember (lcomb (vremoveT cs) vs) as v1. rewrite vs_vcmul_opp.
      apply group_opp_uniq_r in H1. rewrite <- H1. rewrite vs_vcmul_vopp.
      rewrite group_opp_opp. rewrite <- vs_vcmul_assoc.
      rewrite field_mulInvL; auto. apply vs_vcmul_1_l.
  Qed.
  
  (** 设向量组vs线性无关，向量组{u,vs}线性相关，则向量u可由vs线性表示 *)
  Theorem ldep_vconsH_lindep_imply_lrep : forall {n} (vs : @vec V n) (u : V),
      lindep vs -> ldep (vconsH u vs) -> lrep vs u.
  Proof.
    intros. unfold lindep, ldep in *. destruct H0 as [cs [H0 H1]].
    destruct (Aeqdec (vhead cs) Azero) as [H2|H2].
    - (* 若 c.1 <> 0，则 (c1,c2,...,cn) 不全为0，并且 c1v1+c2v2+..+cnvn=0,
         于是 v1,v2,...,vn 线性相关，与 H 矛盾 *)
      assert (exists cs, cs <> vzero /\ lcomb cs vs = 0); try tauto.
      exists (vremoveH cs). split.
      + apply vremoveH_neq0_if; auto.
      + rewrite lcomb_vec_vconsH in H1. rewrite H2 in H1.
        rewrite vs_vcmul_0_l in H1 at 1. rewrite vs_vadd_0_l in H1. auto.
    - (* 从而，u = (-c1/c1)*v1 + (-c2/c1)*v2 + ... *)
      hnf. exists (vcmul (Amul:=Amul) (- / vhead cs) (vremoveH cs)).
      rewrite lcomb_coef_cmul. rewrite lcomb_vec_vconsH in H1.
      remember (lcomb (vremoveH cs) vs) as v1. rewrite vs_vcmul_opp.
      rewrite <- vs_vcmul_vopp. apply group_opp_uniq_r in H1. rewrite H1.
      rewrite <- vs_vcmul_assoc. rewrite field_mulInvL; auto. apply vs_vcmul_1_l.
  Qed.
  
  (** 设向量组vs线性无关，则：向量u可由vs线性表示，当且仅当，向量组{vs,u}线性相关 *)
  Corollary lrep_iff_vconsT_ldep : forall {n} (vs : @vec V n) (u : V),
      lindep vs -> (lrep vs u <-> ldep (vconsT vs u)).
  Proof.
    intros. split; intros.
    - apply lrep_imply_vconsT_ldep; auto.
    - apply ldep_vconsT_lindep_imply_lrep; auto.
  Qed.
  
  (** 设向量组vs线性无关，则：向量u可由vs线性表示，当且仅当，向量组{u,vs}线性相关 *)
  Corollary lrep_iff_vconsH_ldep : forall {n} (vs : @vec V n) (u : V),
      lindep vs -> (lrep vs u <-> ldep (vconsH u vs)).
  Proof.
    intros. split; intros.
    - apply lrep_imply_vconsH_ldep; auto.
    - apply ldep_vconsH_lindep_imply_lrep; auto.
  Qed.

  (* 此性质直观的理解是：线性相关的向量组调整顺序后仍然相关。此处仅仅是头尾两个位置 *)
  (** 向量{u,vs}线性相关，当且仅当，向量组{vs,u}线性相关 *)
  Corollary vconsH_ldep_iff_vconsT_ldep : forall {n} (vs : @vec V n) (u : V),
      ldep (vconsH u vs) <-> ldep (vconsT vs u).
  Proof.
    intros. destruct (ldep_or_lindep vs).
    - split; intros.
      + apply ldep_imply_vconsT_ldep; auto.
      + apply ldep_imply_vconsH_ldep; auto.
    - split; intros.
      + apply lrep_iff_vconsH_ldep in H0; auto. apply lrep_iff_vconsT_ldep; auto.
      + apply lrep_iff_vconsT_ldep in H0; auto. apply lrep_iff_vconsH_ldep; auto.
  Qed.
  
  (** 设向量组vs线性无关，则：向量u不能由vs线性表示，当且仅当，向量组{vs,u}线性无关 *)
  Corollary nolrep_iff_vconsT_lindep : forall {n} (vs : @vec V n) (u : V),
      lindep vs -> (nolrep vs u <-> lindep (vconsT vs u)).
  Proof.
    intros. unfold nolrep, lindep. apply not_iff_compat.
    apply lrep_iff_vconsT_ldep; auto.
  Qed.

  (* 设v1,v2,...,vs线性无关，并且
     u1 = a11v1 + ... + a1svs,
     ...
     us = as1v1 + ... + assvs,
     证明：u1,...,us线性无关的充要条件是
           |a11 ... a1s|
     |A| = |...        | <> 0
           |as1 ... ass|
     
     于是，以下命题互相等价。
     (1) 向量组 v1,v2,...,vs 线性无关
     (2) 上述齐次线性方程组只有零解
     (3) |A| <> 0
   *)

  (** p90, 例7，替换定理：
      设向量组v1,...,vn线性无关，u=c1v1+...+cnvn。若ci<>0，则用u替换vi后得到的
      向量组v1,...,v(i-1),u,v(i+1),...,vn也线性相关 *)
  Lemma lindep_subst : forall {n} (vs : @vec V n) (cs : @vec A n) (i : fin n),
      lindep vs -> cs $ i <> Azero -> lindep (vset vs i (lcomb cs vs)).
  Proof.
    intros. unfold lindep, ldep in *. intro. destruct H. destruct H1 as [ds [H1 H2]].
    (* Let cs=c1,c2,...,cn; ds=d1,d2,...,dn. That is,
       d1v1+d2v2+...+di(c1v1+c2v2+...+cnvn) + ... + dnvn = 0
       ---------------------------------------------------------------------
       cs' := {d1,d2,...,d(i-1),0,d(i+1),...,dn} + di*{c1,c2,...,cn} *)
    exists (vadd (Aadd:=Aadd) (vset ds i Azero) (vcmul (Amul:=Amul) (ds $ i) cs)). split.
    - apply vneq_iff_exist_vnth_neq in H1. destruct H1 as [j H1].
      apply vneq_iff_exist_vnth_neq.
      destruct (i ??= j).
      + (* if i = j, then: 0 + ds.i*cs.i <> 0 *)
        rewrite <- e in *.
        exists i. rewrite vnth_vadd. rewrite vnth_vset_eq. rewrite identityLeft.
        rewrite vnth_vcmul. rewrite vnth_vzero in *.
        apply field_mul_neq0_iff; auto.
      + (* if i <> j, case (ds.i =? 0) *)
        destruct (Aeqdec (ds$i) Azero).
        * (* if ds.i = 0, ds.j <> 0, then: ds.j + 0 <> 0 *)
          exists j. rewrite e. rewrite vcmul_0_l. rewrite vadd_0_r.
          rewrite vnth_vset_neq; auto.
        * (* if ds.i <> 0, then: 0 + ds.i*cs.i <> 0 *)
          exists i. rewrite vnth_vadd. rewrite vnth_vset_eq. rewrite vnth_vcmul.
          monoid. apply field_mul_neq0_iff; auto.
    - rewrite <- H2 at 2.
      rewrite lcomb_coef_add. rewrite lcomb_coef_cmul. rewrite lcomb_coef_vset.
      rewrite lcomb_vec_vset. rewrite vs_vcmul_vadd. asemigroup.
      rewrite vs_vcmul_aadd. rewrite vs_vcmul_vopp. rewrite vs_vcmul_opp at 1.
      rewrite vs_vcmul_0_l at 1. amonoid.
  Qed.

  (* p95, 引理1，设向量组v1,v2,...,vr可由向量组u1,u2,...,us线性表出，
     如果r>s，则v1,v2,...,vr线性相关 *)
  Lemma lreps_more_imply_ldep : forall {r s} (vs : @vec V r) (us : @vec V s),
      lreps us vs -> r > s -> ldep vs.
  Proof.
    intros. unfold lreps,vforall in *. induction r. lia.
    destruct (r ??= s)%nat.
    2:{
      assert (r > s). lia.
      pose proof (IHr (vremoveH vs)).
      assert (forall i, lrep us (vremoveH vs i)).
      { intro. specialize (H (fin2SuccRangeSucc i)). auto. }
      specialize (H2 H3 H1).
      apply vremoveH_ldep_imply_ldep; auto. }
    - subst. clear IHr H0.
      (* c1u1+c2u2+...+cnun = vs.i *)
      destruct (ldep_or_lindep vs); auto. exfalso.
(*       Search lrep. ? *)
(*       Search (lindep). *)
(* lindep_imply_coef_uniq: *)
(*   forall {n : nat} [vs : vec n] [u : V], *)
(*   lindep vs -> lrep vs u -> exists ! cs : vec n, u = lcomb cs vs *)
(* lindep_iff_none_lrep: *)
(*   forall {n : nat} (vs : vec (S n)), *)
(*   lindep vs <-> (forall i : fin (S n), ~ lrep (vremove vs i) (vs$i)) *)
(* lindep_subst: *)
(*   forall {n : nat} [vs cs : vec n] [i : fin n], *)
(*   lindep vs -> cs$i <> Azero -> lindep (vset vs i (lcomb cs vs)) *)
      
(*       Search ldep. *)
(*       rewrite (vconsH_vhead_vremoveH). *)
(*       apply lrep_imply_vconsH_ldep. *)
(*       lrep_imply_vconsH_ldep: *)
(*   forall {n : nat} [vs : vec n] [u : V], lrep vs u -> ldep (vconsH u vs) *)
(* lrep_imply_vconsT_ldep: *)
(*   forall {n : nat} [vs : vec n] [u : V], lrep vs u -> ldep (vconsT vs u) *)



      (* induction s. *)
      (* + apply ldep_vec1_iff_eq0. apply veq_iff_vnth; intros i. *)
      (*   specialize (H fin0). unfold lrep in H. destruct H as [cs H]. *)
      (*   cbv in H. rewrite H. f_equal. destruct i. apply sig_eq_iff. lia. *)
      (* + *)
      (*   rewrite (vconsH_vhead_vremoveH). *)
      (*   Search (ldep (vconsH _ _)). *)
      (*   apply ldep_imply_vconsH_ldep. *)
      (*   apply IHs with (us:=vremoveH us). *)
      (*   intros. *)
      (*   apply lrep_iff_vconsH_ldep. *)
      (*   simpl in H. *)
  Abort.

  
End ldep.


(* ===================================================================== *)
(** ** Maximal linearly independent system 极大线性无关组 *)
Section lmis.
  Context `{HVectorSpace : VectorSpace}.
  Context {AeqDec : Dec (@eq A)}.
  Context {VeqDec : Dec (@eq V)}.
  Notation lcomb := (@lcomb _ _ Vadd Vzero Vcmul).
  Notation lrep := (@lrep _ _ Vadd Vzero Vcmul).
  Notation lreps := (@lreps _ _ Vadd Vzero Vcmul).
  Notation ldep := (@ldep _ Azero _ Vadd Vzero Vcmul).
  Notation lindep := (@lindep _ Azero _ Vadd Vzero Vcmul).
  Notation vsequiv := (@vsequiv _ _ Vadd Vzero Vcmul).

  (** 向量组 ms 是向量组 vs 的极大线性无关组 *)
  Definition lmis {n s} (vs : @vec V n) (ms : @vec V s) : Prop :=
    vmems ms vs /\
      lindep ms /\
      (vforall vs (fun v => ~(vmem ms v) -> ldep (vconsT ms v))) .

  (** 向量组与其极大线性无关组等价 *)
  Lemma lmis_vsequiv_self : forall {n s} (vs : @vec V n) (ms : @vec V s),
      lmis vs ms -> vsequiv vs ms.
  Proof.
    intros. unfold lmis, vsequiv in *. destruct H as [H [H1 H2]].
    unfold vmems,vmem,vexist,vforall,lreps,vforall in *. split.
    - intros. pose proof (lrep_in vs). unfold vforall in H0.
      specialize (H i). destruct H as [j H]. rewrite <- H. auto.
    - intros. specialize (H2 i). pose proof (vmem_dec ms (vs i)).
      destruct H0 as [H0|H0].
      + destruct H0 as [j H0]. rewrite <- H0. apply lrep_in.
      + epose proof (lrep_iff_vconsT_ldep (vs i) H1). apply H3; auto.
  Qed.

  (** 向量组的任意两个极大线性无关组等价 *)
  Corollary lmis_vsequiv_any :
    forall {n s t} (vs : @vec V n) (ms1 : @vec V s) (ms2 : @vec V t),
      lmis vs ms1 -> lmis vs ms2 -> vsequiv ms1 ms2.
  Proof.
    intros. apply lmis_vsequiv_self in H, H0.
    apply vsequiv_trans with vs; auto. apply vsequiv_sym; auto.
  Qed.
  
  (** 向量u可由向量组vs线性表出当且仅当u可由vs的一个极大线性线性无关组线性表出 *)
  Corollary lrep_iff_lrepByLmis :
    forall {n s} (vs : @vec V n) (ms : @vec V s) (u : V),
      lmis vs ms -> (lrep vs u <-> lrep ms u).
  Proof.
    intros. apply lmis_vsequiv_self in H. unfold vsequiv in H. destruct H.
    split; intros. apply (lreps_lrep H0 H1). apply (lreps_lrep H H1).
  Qed.
  
End lmis.

(*
(* ===================================================================== *)
(** ** Basis *)
Section lbasis.
  Context `{HVectorSpace : VectorSpace}.
  Notation lcomb := (@lcomb _ _ Vadd Vzero Vcmul).
  Notation lindep := (@lindep _ Azero _ Vadd Vzero Vcmul).
  Notation lspan := (@lspan _ _ Vadd Vzero Vcmul).

  (** Elements v1,v2,...,vn of V are said to consistute a basis of V *)
  Definition lbasis {n} (vs : @vec V n) : Prop :=
    lindep vs /\ lspan vs.

  (** Elements v1, v2, . . . , vn of a linear space V constitute a basis of 
      that linear space if and only if, given any element u of V , there exist 
      uniquely determined scalars c1, c2, . . . , cn such that
      u = c1v1 + c2v2 + · · · + cnvn  *)
  Theorem lbasis_if_unique_cs : forall {n} (vs : @vec V n),
      lbasis vs <-> forall u : V, exists! (cs : @vec A n), lcomb cs vs = u.
  Proof.
    intros. split; intros.
    - hnf in H. destruct H as [H H']. hnf in H'. specialize (H' u).
      rewrite <- unique_existence. split; auto.
      hnf. intros c1 c2 H1 H2. rewrite <- H2 in H1.
      apply lindep_imply_coef_uniq in H1; auto.
    - hnf. split.
      + apply lindep_iff_unique0. intros. specialize (H Vzero).
        apply unique_existence in H. destruct H. hnf in H1.
        erewrite H1; auto. apply lcomb_c0_eq0.
      + unfold lspan. intros. specialize (H u). destruct H as [c [H H']].
        exists c; auto.
  Qed.
    
End lbasis.


(** ** Linear Transformations *)
Section ltrans.
  Context `{HField : Field A Aadd Azero Aopp Amul Aone Ainv}.
  Context `(HV : @VectorSpace A Aadd Azero Aopp Amul Aone Ainv HField
                   V Vadd Vzero Vopp Vcmul).
  Context `(HW : @VectorSpace A Aadd Azero Aopp Amul Aone Ainv HField
                   W Wadd Wzero Wopp Wcmul).
  Notation Vsub u v := (Vadd u (Vopp v)).
  Notation Wsub u v := (Wadd u (Wopp v)).

  (* Let V and W be linear spaces over some field K. A function T : V → W is said 
     to be a linear transformation if T (u + v) = T (u) + T (v) and T (cv) = cT (v) 
     for all elements u and v of V and for all elements c of K. *)
  Definition ltrans (T : V -> W) : Prop :=
    (forall u v, T (Vadd u v) = Wadd (T u) (T v)) /\ (forall v c, T (Vcmul c v) = Wcmul c (T v)).

  (** ltrans T -> T(u + v) = T(u) + T(v) *)
  Lemma ltrans_add : forall (T : V -> W),
      ltrans T -> forall u v, T (Vadd u v) = Wadd (T u) (T v).
  Proof. intros. hnf in H. destruct H; auto. Qed.

  (** ltrans T -> T(a * v) = a * T(v) *)
  Lemma ltrans_cmul : forall (T : V -> W),
      ltrans T -> forall a v, T (Vcmul a v) = Wcmul a (T v).
  Proof. intros. hnf in H. destruct H; auto. Qed.

  (** ltrans T -> T(- v) = - T(v) *)
  Lemma ltrans_opp : forall (T : V -> W),
      ltrans T -> forall v, T (Vopp v) = Wopp (T v).
  Proof.
    intros. hnf in H. destruct H; auto.
    rewrite <- !vs_vcmul_opp1. rewrite H0. rewrite vs_vcmul_opp1. auto.
  Qed.

  (** ltrans T -> T(u - v) = T(u) - T(v) *)
  Lemma ltrans_sub : forall (T : V -> W),
      ltrans T -> forall u v, T (Vsub u v) = Wsub (T u) (T v).
  Proof.
    intros. hnf in H. rewrite ltrans_add; auto. rewrite ltrans_opp; auto.
  Qed.
  
  (** ltrans T -> T(0) = 0 *)
  Lemma ltrans_zero : forall (T : V -> W), ltrans T -> T Vzero = Wzero.
  Proof.
    intros. hnf in H.
    replace (Vzero) with (Vsub Vzero Vzero) by group.
    rewrite ltrans_sub; auto. group.
  Qed.
    
  (** T (c1v1 + c2v2 + · · · + cnvn) 
      = T (c1v1) + T (c2v2) + · · · + T (cnvn)
      = c1w1 + c2w2 + · · · + cnwn *)
  Lemma ltrans_linear : forall {n} (T : V -> W) (cs : @vec A n)
                           (v : @vec V n) (w : @vec W n),
      ltrans T -> (forall i, w$i = T(v$i)) ->
      T (lcomb (Vadd:=Vadd)(Vzero:=Vzero)(Vcmul:=Vcmul) cs v) =
        lcomb (Vadd:=Wadd)(Vzero:=Wzero)(Vcmul:=Wcmul) cs w.
  Proof.
    intros. unfold lcomb.
    apply eq_trans with
      (vsum (Aadd:=Wadd)(Azero:=Wzero) (vmap T (vmap2 Vcmul cs v))).
    - rewrite <- (vsum_vmap (Aadd:=Vadd)(Azero:=Vzero)); auto.
      apply ltrans_zero; auto. apply ltrans_add; auto.
    - apply vsum_eq; intros. rewrite !vnth_vmap, !vnth_vmap2.
      rewrite ltrans_cmul; auto. rewrite H0. auto.
  Qed.
  
End ltrans.
*)

(** ** 向量的范数，赋范向量空间 *)


(* ===================================================================== *)
(** ** Vector Space *)

(** Vector forms a linear space (called `Vector Space`) *)
Section vectorSpace.
  Context `{HField : Field A Aadd Azero Aopp Amul Aone Ainv}.
  
  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vcmul := (@vcmul _ Amul).
  
  #[export] Instance vectorSpace {n : nat} :
    VectorSpace (V:=vec n) vadd vzero vopp vcmul.
  Proof.
    constructor; try apply vadd_AGroup; intros.
    apply vcmul_1_l. rewrite vcmul_assoc; auto.
    apply vcmul_add. apply vcmul_vadd.
  Qed.

End vectorSpace.
Arguments vectorSpace {A Aadd Azero Aopp Amul Aone Ainv} HField {n}.

Section props.
  Context `{HField : Field A Aadd Azero Aopp Amul Aone Ainv}.
  Notation vectorSpace := (vectorSpace HField).

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vsub := (@vsub _ Aadd Aopp).
  Notation vcmul := (@vcmul _ Amul).
  Notation vsum := (@vsum _ Aadd Azero).
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Notation lcomb := (@lcomb _ _ vadd vzero vcmul).
  Notation lrep := (@lrep _ _ vadd vzero vcmul).
  Notation ldep := (@ldep _ Azero _ vadd vzero vcmul).
  Notation lindep := (@lindep _ Azero _ vadd vzero vcmul).

  (** (lcomb cs vs).i = ∑(vmap2 Amul cs (vcol vs i)) *)
  Lemma vnth_lcomb : forall {n r} (cs : @vec A r) (vs : @mat A r n) (i : fin n),
      (lcomb cs vs) $ i = vsum (vmap2 Amul cs (mcol vs i)).
  Proof. intros. unfold lcomb. rewrite vnth_vsum. auto. Qed.

  (** lcomb over vectors from `vmap2 vapp us vs` *)
  Lemma lcomb_vec_vmap2_vapp :
    forall (m n r : nat) (cs : @vec A r)
      (us : @mat A r m) (vs : @mat A r n) (i : fin (m + n)),
      lcomb cs (vmap2 vapp us vs) i = vapp (lcomb cs us) (lcomb cs vs) i.
  Proof.
    intros. rewrite vnth_lcomb. destruct (fin2nat i ??< m).
    - rewrite vnth_vapp_L with (H:=l). unfold lcomb.
      rewrite vnth_vsum. apply vsum_eq; intros j.
      rewrite !vnth_vmap2. rewrite !vnth_vcmul. f_equal. rewrite !vnth_mcol.
      rewrite vnth_vmap2. rewrite vnth_vapp_L with (H:=l); auto.
    - assert (m <= fin2nat i). lia. rewrite vnth_vapp_R with (H:=H). unfold lcomb.
      rewrite vnth_vsum. apply vsum_eq; intros j.
      rewrite !vnth_vmap2. rewrite !vnth_vcmul. f_equal. rewrite !vnth_mcol.
      rewrite vnth_vmap2. rewrite vnth_vapp_R with (H:=H). auto.
  Qed.

  (** F^n的下述子集U是一个子空间 U = {(a1,...,ak,0,...,0) | ai ∈ F, 1 <= k < n } *)
  Section topKWithZero_SubSpace.
    Context {n k : nat}.
    Context {Hk : 1 <= k < n}.

    Instance topKWithZero_SubSpaceStruct
      : SubSpaceStruct
          (fun v => forall (i:fin n),
               if (fin2nat i ??> k)%nat then v$i = Azero else True).
    Proof.
      constructor; intros.
      - destruct (_??<_); auto.
      - destruct (_??<_); auto. rewrite vnth_vadd.
        pose proof (u.prf). pose proof (v.prf). simpl in *.
        specialize (H i). specialize (H0 i).
        destruct (_??<_) in H,H0; try lia. rewrite H,H0. monoid.
      - destruct (_??<_); auto. rewrite vnth_vcmul.
        pose proof (v.prf). simpl in *. specialize (H i).
        destruct (_??<_) in H; try lia. rewrite H. apply ring_mul_0_r.
    Qed.

    #[export] Instance topKWithZero_SubSpace : VectorSpace Hadd Hzero Hopp Hcmul :=
      makeSubSpace topKWithZero_SubSpaceStruct.
  End topKWithZero_SubSpace.

  (** F^n的下述子集U是一个子空间 U = {(a1,0,a3,0,...0,an) | ai ∈ F, i=1,3,...,n} *)
  Section oddWithZero_SubSpace.
    Context {n : nat}.
    
    Instance oddWithZero_SubSpaceStruct
      : SubSpaceStruct
          (fun v => forall (i : fin n),
               if ((fin2nat i mod 2) ??= 0)%nat then v$i = Azero else True).
    Proof.
      constructor; intros.
      - destruct (_??=_)%nat; auto.
      - destruct (_??=_)%nat; auto. rewrite vnth_vadd.
        pose proof (u.prf). pose proof (v.prf). hnf in H,H0.
        specialize (H i). specialize (H0 i).
        destruct (_??=_)%nat in H,H0; try lia. rewrite H,H0. monoid.
      - destruct (_??=_)%nat; auto. rewrite vnth_vcmul.
        pose proof (v.prf). hnf in H. specialize (H i).
        destruct (_??=_)%nat in H; try lia. rewrite H. apply ring_mul_0_r.
    Qed.

    #[export] Instance oddWithZero_SubSpace : VectorSpace Hadd Hzero Hopp Hcmul :=
      makeSubSpace oddWithZero_SubSpaceStruct.
  End oddWithZero_SubSpace.

  (** 添加或去掉向量的一些分量构成的延伸组与缩短组的一对性质：
      1. 如果向量组线性无关，那么把每个向量在相同位置添上m个分量得到的延伸组也线性无关
      2. 如果向量组线性相关，那么把每个向量在相同位置去掉m个分量得到的缩短组也线性相关 

      如何表示“延伸组和缩短组”？
      1. 如何表示“延伸的向量”，“缩短的向量”？
      (1) 在头部加入/去掉数个元素，在尾部加入/去掉数个元素，在任意位置加入/去掉数个元素
      (2) 在任意位置的操作包含了头部或尾部。
      3. 如何表示“延伸组”，“缩短组”？
      (1) 关键是要对向量组在相同的位置进行操作。
      (2) 还可以换一种思路，不进行具体的操作，但是可以判断两个向量是否具有“延伸组”或
      “缩短组”的关系？

      给定v1,...,vs，记其延伸组为 v1',...,vs'，
      则从 k1v1'+...ksvs'=0 可得到 k1v1+...+ksvs=0。
      若v1,...,vs线性无关，则可知k1=...=ks=0，从而v1',...,vs'也线性无关。
   *)

  (** 若向量组线性无关，每个向量的相同位置添上m个分量后的延伸组线性无关。*)
  Section lindep_extend.
    
    (** 在每个向量头部都加入数个元素后保持线性无关 *)
    Lemma lindep_extend_head :
      forall {m n r} (us : @vec (@vec A m) r) (vs : @vec (@vec A n) r),
        lindep vs -> lindep (vmap2 vapp us vs).
    Proof.
      intros. unfold lindep, ldep in *. intro. destruct H.
      destruct H0 as [cs [H H0]]. exists cs. split; auto.
      rewrite veq_iff_vnth. rewrite veq_iff_vnth in H0. intros.
      specialize (H0 (fin2AddRangeAddL i)).
      rewrite vnth_vzero in *. rewrite <- H0 at 2.
      rewrite lcomb_vec_vmap2_vapp. erewrite vnth_vapp_R.
      rewrite fin2AddRangeAddL'_fin2AddRangeAddL. auto.
      Unshelve. rewrite fin2nat_fin2AddRangeAddL. lia.
    Qed.

    (** 在每个向量尾部都加入数个元素后保持线性无关 *)
    Lemma lindep_extend_tail :
      forall {m n r} (us : @vec (@vec A m) r) (vs : @vec (@vec A n) r),
        lindep us -> lindep (vmap2 vapp us vs).
    Proof.
      intros. unfold lindep, ldep in *. intro. destruct H.
      destruct H0 as [cs [H H0]]. exists cs. split; auto.
      rewrite veq_iff_vnth. rewrite veq_iff_vnth in H0. intros.
      specialize (H0 (fin2AddRangeR i)).
      rewrite vnth_vzero in *. rewrite <- H0 at 2.
      rewrite lcomb_vec_vmap2_vapp. erewrite vnth_vapp_L.
      rewrite fin2AddRangeR'_fin2AddRangeR. auto.
      Unshelve. rewrite fin2nat_fin2AddRangeR. apply fin2nat_lt.
    Qed.

    (** 对每个向量都插入1个元素后保持线性无关 *)
    Lemma lindep_extend_insert :
      forall {n r} (vs : @vec (@vec A n) r) (i : fin (S n)) (a : A),
        lindep vs -> lindep (vmap (fun v => vinsert v i a) vs).
    Proof.
      intros. unfold lindep, ldep in *. intro. destruct H.
      destruct H0 as [cs [H H0]]. exists cs. split; intros; auto.
      rewrite veq_iff_vnth. intros j. rewrite veq_iff_vnth in H0.
      destruct (fin2nat j ??< fin2nat i).
      - specialize (H0 (fin2SuccRange j)).
        rewrite vnth_vzero in *. rewrite <- H0 at 2. rewrite !vnth_lcomb.
        apply vsum_eq; intros k. rewrite !vnth_vmap2. f_equal. unfold mcol.
        rewrite !vnth_vmap. rewrite (@vnth_vinsert_lt _ Azero) with (j:=j); auto.
      - specialize (H0 (fin2SuccRangeSucc j)).
        rewrite vnth_vzero in *. rewrite <- H0 at 2. rewrite !vnth_lcomb.
        apply vsum_eq; intros k. rewrite !vnth_vmap2. f_equal. unfold mcol.
        rewrite !vnth_vmap. rewrite (@vnth_vinsert_gt _ Azero) with (j:=j); auto.
        lia. apply fin2nat_lt.
    Qed.

  End lindep_extend.

  (** 若向量组线性相关，每个向量的相同位置去掉m个分量后的延伸组线性相关。*)
  Section ldep_shorten.
    
    (** 在每个向量头部都去掉数个元素后保持线性相关 *)
    Lemma ldep_shorten_head : forall {m n r} (vs : @vec (@vec A (m + n)) r),
        ldep vs -> ldep (vmap vtailN vs).
    Proof.
      intros. unfold ldep in *. destruct H as [cs [H H0]]. exists cs. split; auto.
      rewrite veq_iff_vnth. rewrite veq_iff_vnth in H0. intros.
      specialize (H0 (fin2AddRangeAddL i)). rewrite vnth_vzero in *.
      rewrite <- H0 at 2. rewrite !vnth_lcomb. apply vsum_eq; intros j.
      rewrite !vnth_vmap2. f_equal.
    Qed.
    
    (** 在每个向量尾部都去掉数个元素后保持线性相关 *)
    Lemma ldep_shorten_tail : forall {m n r} (vs : @vec (@vec A (m + n)) r),
        ldep vs -> ldep (vmap vheadN vs).
    Proof.
      intros. unfold ldep in *. destruct H as [cs [H H0]]. exists cs. split; auto.
      rewrite veq_iff_vnth. rewrite veq_iff_vnth in H0. intros.
      specialize (H0 (fin2AddRangeR i)). rewrite vnth_vzero in *.
      rewrite <- H0 at 2. rewrite !vnth_lcomb. apply vsum_eq; intros j.
      rewrite !vnth_vmap2. f_equal.
    Qed.

    (** 对每个向量都删除1个元素后保持线性相关 *)
    Lemma ldep_shorten_delete :
      forall {n r} (vs : @vec (@vec A (S n)) r) (i : fin (S n)) (a : A),
        ldep vs -> ldep (vmap (fun v => vremove v i) vs).
    Proof.
      intros. unfold ldep in *. destruct H as [cs [H H0]]. exists cs. split; intros; auto.
      rewrite veq_iff_vnth. intros j. rewrite veq_iff_vnth in H0.
      destruct (fin2nat j ??< fin2nat i).
      - specialize (H0 (fin2SuccRange j)).
        rewrite vnth_vzero in *. rewrite <- H0 at 2. rewrite !vnth_lcomb.
        apply vsum_eq; intros k. f_equal. apply veq_iff_vnth; intros s.
        rewrite !vnth_mcol. rewrite !vnth_vmap.
        rewrite (@vnth_vremove_lt _ Azero); auto. erewrite nth_v2f. f_equal.
        apply fin2nat_imply_nat2fin. rewrite fin2nat_fin2SuccRange. auto.
      - specialize (H0 (fin2SuccRangeSucc j)).
        rewrite vnth_vzero in *. rewrite <- H0 at 2. rewrite !vnth_lcomb.
        apply vsum_eq; intros k. f_equal. apply veq_iff_vnth; intros s.
        rewrite !vnth_mcol. rewrite !vnth_vmap.
        rewrite (@vnth_vremove_ge _ Azero); auto; try lia.
        + erewrite nth_v2f. f_equal. apply fin2nat_imply_nat2fin.
          rewrite fin2nat_fin2SuccRangeSucc. auto.
        + apply fin2nat_lt.
          Unshelve. pose proof (fin2nat_lt j). lia.
          pose proof (fin2nat_lt j). lia.
    Qed.
    
  End ldep_shorten.

  
  (** F^n中的s个向量中的每一个都在这个向量组张成的线性空间中。
      即，vi ∈ <v1,v2,...,vs>, 1<=i<=s, vi∈F^n *)
  Lemma in_lspan : forall {n s} (vs : @vec (@vec A n) s) i,
      Hbelong (ss := lspan_Struct vs) (vs $ i).
  Proof. intros. hnf. apply lrep_in. Qed.
  
  (** 在F^n中，任意向量都能由n个线性无关的向量来线性表示 *)
  Lemma lindep_imply_lrep_any : forall {n} (vs : @vec (@vec A n) n) (u : @vec A n),
      lindep vs -> lrep vs u.
  Proof.
    intros.
    pose proof (in_lspan vs). unfold Hbelong in H0.
    rewrite lindep_iff_coef0 in H.
    unfold lindep,ldep in H. unfold lrep.
  Admitted.
  
  (** 在F^n中，任意n+1个向量都线性相关 *)
  Lemma ldep_Sn : forall {n} (vs : @vec (@vec A n) (S n)), ldep vs.
  Proof.
    (* 丘老师的证明：
       考虑齐次线性方程组 x1v1+x2v2+...+x(n-1)v(n-1)=0，
       它的方程个数n小于未知量个数n+1，因此它有非零解。所以vs线性相关。*)

    (* 我的证明（只有思路，尚未完成）：
       1. 前n个向量要么线性相关，要么线性无关。
       (1). 若线性相关，则这n+1个向量是线性相关的；
       (2). 若线性无关，则第n+1个向量可由前n个向量线性表示，于是这n+1个向量线性相关。*)
    intros.
    rewrite <- (vconsT_vremoveT_vtail vs (Azero:=vzero)).
    assert ({ldep (vremoveT vs)} + {~ (ldep (vremoveT vs))}).
    (* 此可判定性也许无法证明，因为涉及到存在量词 *) admit.
    destruct H.
    - apply ldep_imply_vconsT_ldep. auto.
    -
      Admitted.
    


  (* 几何空间：
     1. 几何空间可以看成是以原点O为起点的所有向量组成的集合V，它有加法和数量乘法两种运算。
     2. 几何空间V的一个非空子集U如果对于向量的加法和数乘都封闭，则称U是V的一个子空间。
     3. 一条直线l可看成是以O为起点，以l上的点为终点的所有向量组成的集合。
     4. 一个平面π可看成是以O为起点，以π上的点为终点的所有向量组成的集合。
   *)
  
  
  (* 自然基的性质 *)
  Section veyes.
    Context {n : nat}.
    Notation veyes := (veyes 0 1).

    (** 任意向量都能写成自然基的线性组合: v * eyes = v *)
    Lemma lcomb_veyes : forall v : vec n, lcomb v (veyes n) = v.
    Proof.
      intros. unfold lcomb. apply veq_iff_vnth. intros.
      (* (v1(1,0,0) + v2(0,1,0) + v3(0,0,1)).i = v.i *)
      rewrite vnth_vsum.
      (* v1(1,0,0).i + v2(0,1,0).i + v3(0,0,1).i = v.i *)
      apply vsum_unique with (i:=i).
      - rewrite vnth_vmap2. rewrite vnth_vcmul. rewrite vnth_veyes_eq. amonoid.
      - intros. rewrite vnth_vmap2. rewrite vnth_vcmul.
        rewrite vnth_veyes_neq; auto. apply ring_mul_0_r.
    Qed.
    
    (** 自然基是线性无关的 *)
    Lemma lindep_veyes : lindep (veyes n).
    Proof.
      intros. unfold lindep, ldep. intro. destruct H as [v [H H0]]. destruct H.
      rewrite lcomb_veyes in H0. auto.
    Qed.

    (** 任意向量 v 都可由自然基线性表示 *)
    Lemma lrep_veyes : forall (v : vec n), lrep (veyes n) v.
    Proof. intros. unfold lrep. exists v. apply lcomb_veyes. Qed.

    (** 任意向量 v，用自然基线性表示的方式唯一 *)
    Lemma lrep_veyes_unique : forall (v : vec n), exists! c, lcomb c (veyes n) = v.
    Proof.
      intros. exists v. split. apply lcomb_veyes. intros. rewrite lcomb_veyes in H. auto.
    Qed.
    
    (* Example ex1_vspan : vspan vecs. *)
    (* Proof. *)
    (*   unfold vspan. intros. exists (mkvec3 (u.1) (u.2) (u.3)). *)
    (*   apply v3eq_iff. cbv. lra. *)
    (* Qed. *)
    
    (* Example ex2_vbasis : vbasis vecs. *)
    (* Proof. *)
    (*   unfold vbasis. split. apply ex1_vlindep. apply ex1_vspan. *)
    (* Qed. *)

  End veyes.
End props.


(*
Section examples.
  Import VectorR.
  Notation vlcomb := (@vlcomb _ _ vadd vzero vcmul).
  Notation vldep := (@vldep _ Azero _ vadd vzero vcmul).
  Notation vlindep := (@vlindep _ Azero _ vadd vzero vcmul).
  Notation vspan := (@vspan _ _ vadd vzero vcmul).
  Notation vbasis := (@vbasis _ Azero _ vadd vzero vcmul).

  (* Example for "linearly dependent" *)
  Section ex1.
    (* The vectors (2, 2, 5), (3, 3, 12) and (5, 5, −1) are linearly dependent
       elements of the real vector space R3, since
       7(2, 2, 5) − 3(3, 3, 12) − (5, 5, −1) = (0, 0, 0).
       Thus if v1 = (2, 2, 5), v2 = (3, 3, 12) and v3 = (5, 5, −1), then the equation
       c1v1 + c2v2 + c3v3 = 0 is satisfied with c1 = 7, c2 = −3 and c3 = −1.) *)
    Let vecs := Vector.mkvec3 (Azero:=vzero)
                  (mkvec3 2 2 5)
                  (mkvec3 3 3 12)
                  (mkvec3 5 5 (-1)%R).
    Let coefs := mkvec3 7 (-3) (-1).
    
    Example ex1_eq1 : vlcomb coefs vecs = vzero.
    Proof. apply v3eq_iff. cbv. lra. Qed.

    Example ex1_ldep : vldep vecs.
    Proof.
      unfold vldep. exists coefs. split.
      - intro. apply v3eq_iff in H. cbv in H. ra.
      - apply ex1_eq1.
    Qed.
  End ex1.

End examples.
 *)

