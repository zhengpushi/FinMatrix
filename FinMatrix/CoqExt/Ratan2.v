(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : atan2
  author    : ZhengPu Shi
  date      : 2021.05
  
  remark    :
  1. https://zh.wikipedia.org/wiki/Atan2
  * 用 atan(y/x) 计算角度时的问题：
    如果 x = 0，除法是未定义的
    arctan 的范围仅是 (-π/2, π/2)，原因是除法y/x丢失了符号信息。
    x和y都可以是正或负，从而有4种可能，对应于4个不同象限。但y/x得到了单个值。
  * 在三角函数中，atan2是atan的一个变种。
    对于任意不同时等于0的实参数 x 和 y，atan2 y x 表达了：以坐标原点为起点，
    指向(x,y)的射线在坐标平面上与x轴正方向之间的角的角度。
     在几何意义上，atan2 y x 等价于 atan (y/x)，但可以处理 x=0而y<>0 时的情形。
  * 函数定义
    atan2 y x =
      atan (y/x),       x > 0
      atan (y/x) + pi,  x < 0, y >= 0
      atan (y/x) - pi,  x < 0, y < 0
      +pi/2,            x = 0, y > 0
      -pi/2,            x = 0, y < 0
      undefined,        x = 0, y = 0  (我定义为 +pi/2，所以简化为 x = 0, y >= 0)
    详见 vangle2C 与 vangle2A 的等价性证明。
  * 该定义的值域是(-π,π]，可通过对负数结果加2π的方法，将结果映射到[0,2π)范围。

  2. https://en.wikipedia.org/wiki/Atan2
  * 在这里还介绍了几个等价的紧凑版本，其等价性及代码生成是Coq验证的强项。以后再补充。
 *)


Require Import RExt.
Require Import RealFunction.

Open Scope R_scope.


(* ######################################################################### *)
(** * atan2 *)

(** atan2 *)
Definition atan2 (y x : R) : R :=
  if x >? 0
  then atan (y/x)               (* x > 0 *)
  else
    if x <? 0
    then
      if y >=? 0
      then atan (y/x) + PI      (* x < 0, y >= 0 *)
      else atan (y/x) - PI      (* x < 0, y < 0 *)
    else
      if y >=? 0
      then PI / 2               (* x = 0, y >= 0 *)
      else - PI / 2             (* x = 0, y < 0 *)
.


(** Automaticaly destruct `dec` *)
Ltac destruct_dec :=
  repeat
    match goal with
    | |- context [dec ?cmp _ _] => destruct (dec cmp)
    end.

Fact atan2_Xgt0 : forall y x, x > 0 -> atan2 y x = atan (y/x).
Proof. intros. unfold atan2,Rltb,Rleb,Acmpb. destruct_dec; lra. Qed.

Fact atan2_Xlt0_Yge0 : forall y x, x < 0 -> y >= 0 -> atan2 y x = (atan (y/x) + PI)%R.
Proof. intros. unfold atan2,Rltb,Rleb,Acmpb. destruct_dec; lra. Qed.

Fact atan2_Xlt0_Ylt0 : forall y x, x < 0 -> y < 0 -> atan2 y x = (atan (y/x) - PI)%R.
Proof. intros. unfold atan2,Rltb,Rleb,Acmpb. destruct_dec; lra. Qed.

Fact atan2_X0_Yge0 : forall y x, x = 0 -> y >= 0 -> atan2 y x = PI/2.
Proof. intros. unfold atan2,Rltb,Rleb,Acmpb. destruct_dec; lra. Qed.

Fact atan2_X0_Ylt0 : forall y x, x = 0 -> y < 0 -> atan2 y x = - PI/2.
Proof. intros. unfold atan2,Rltb,Rleb,Acmpb. destruct_dec; lra. Qed.

(** - PI < atan2 y x <= PI *)
Lemma atan2_bound : forall y x, - PI < atan2 y x <= PI.
Proof.
  intros. pose proof (atan_bound (y/x)).
  bdestruct (x >? 0).
  - rewrite atan2_Xgt0; ra.
  - bdestruct (x <? 0).
    + bdestruct (y >=? 0).
      * rewrite atan2_Xlt0_Yge0; ra.
        assert (y/x <= 0); ra. pose proof (atan_bound_le0 (y/x)); ra.
      * rewrite atan2_Xlt0_Ylt0; ra.
        assert (y < 0); ra. assert (0 < y/x); ra.
        pose proof (atan_bound_gt0 (y/x)); ra.
    + assert (x = 0); ra. bdestruct (0 <=? y).
      * rewrite atan2_X0_Yge0; ra.
      * rewrite atan2_X0_Ylt0; ra.
Qed.

(** An equation about atan2 will be used in the later proof *)
Lemma atan2_sin_cos_eq1 : forall a k : R,
    - PI < a <= PI -> k > 0 ->
    atan2 (sin a * k) (cos a * k) = a.
Proof.
  intros. apply Rsplit_neg_pi_to_pi in H.
  repeat match goal with | H: _ \/ _ |- _ => destruct H as [? | H] end; 
    subst; autorewrite with R.
  - rewrite atan2_X0_Ylt0; ra.
  - rewrite atan2_Xgt0; ra. replace (0/k) with 0; ra. apply atan_0.
  - rewrite atan2_X0_Yge0; ra.
  - assert (sin a < 0). { apply sin_lt_0_var; lra. }
    assert (cos a < 0).
    { rewrite <- RealFunction.cos_2PI_add. apply cos_lt_0; ra. }
    rewrite atan2_Xlt0_Ylt0; ra.
    rewrite atan_ak_bk; ra. cbv; rewrite Rtan_rw.
    rewrite <- Rtrigo_facts.tan_pi_plus; ra. rewrite atan_tan; ra.
  - assert (sin a < 0). { apply sin_lt_0_var; lra. }
    assert (0 < cos a). { apply cos_gt_0; ra. }
    rewrite atan2_Xgt0; ra.
    rewrite atan_ak_bk; ra. cbv; rewrite Rtan_rw. rewrite atan_tan; ra.
  - assert (0 < sin a). { apply sin_gt_0; lra. }
    assert (0 < cos a). { apply cos_gt_0; ra. }
    rewrite atan2_Xgt0; ra.
    rewrite atan_ak_bk; ra. cbv; rewrite Rtan_rw. rewrite atan_tan; ra.
  - assert (0 <= sin a). { apply sin_ge_0; lra. }
    assert (cos a < 0). { apply cos_lt_0; ra. }
    rewrite atan2_Xlt0_Yge0; ra.
    rewrite atan_ak_bk; ra. cbv; rewrite Rtan_rw.
    rewrite <- RealFunction.tan_sub_PI. rewrite atan_tan; ra.
Qed.


(** 2D向量的夹角从几何上看有两种做法，是否等价？
  1. 使用 /_ a b = atan2 <a,b> (aXb)，其值域是 (-π, π]
  2. tan2 by bx - atan2 ay ax
  问：方法1和方法2等价吗？有几步关键性的引理如下。
  
  该问题已经被证明，见 
  https://en.wikipedia.org/wiki/Atan2#Angle sum and difference identity
  其证明需要借助复平面的幅角 Arg，这里暂未进行形式化。
 *)
Lemma atan2_plus_eq : forall x1 y1 x2 y2 : R,
    atan2 y1 x1 + atan2 y2 x2 = atan2 (y1*x2+y2*x1) (x1*x2-y1*y2).
Admitted.

Lemma atan2_minus_eq : forall x1 y1 x2 y2 : R,
    atan2 y1 x1 - atan2 y2 x2 = atan2 (y1*x2-y2*x1) (x1*x2+y1*y2).
Admitted.


(** 0 < x -> y <> 0 -> atan2 (- y) x = - atan2 y x *)
Lemma atan2_y_neg : forall x y : R,
    0 < x -> y <> 0 -> atan2 (- y) x = - atan2 y x.
Proof.
  intros. unfold atan2. rewrite Rdiv_opp_l. rewrite atan_opp.
  bdestruct (0 <? x); auto. bdestruct (x <? 0); ra.
Qed.
  

(** Don't unfold it, avoding too many details *)
Global Opaque atan2.
