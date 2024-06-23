(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix on matrix.
  author    : Zhengpu Shi
  date      : 2023.04
 *)

Require Export Matrix.


(* ======================================================================= *)
(** ** Matrix theory come from common implementations *)

Open Scope mat_scope.

(** general notations *)
(* Notation A := nat. *)
(* Notation A0 := 0. *)
(* Notation Aadd := Nat.add. *)

(** 
  问题：如何表达分块矩阵（子矩阵大小不相同的一般情形）？
  
  1. 注意两个概念的区别：
  高维矩阵
    元素是矩阵的矩阵，要求每个子矩阵都是相同大小。
  分块矩阵
    元素是矩阵的矩阵，但每个子矩阵大小可不相同，不过要求按行和列划分时满足形状要求

  2. 分块矩阵的乘法
    参考 https://zhuanlan.zhihu.com/p/422710424
    对A，B两个矩阵的分块方式有更多要求，A是r*n，B是n*c的。

  3. 如何表达分块分块矩阵，需要继续探索。。。
*)

Section defs.

  (** 这样构造的分块是每个子矩阵都是相同大小，显然不是分块矩阵的完整理论 *)
  Check @mat (@mat _ 3 4).

  (* 
  但因为 mat 结构要求每个元素都是一个相同的类型，而使用mat类型时显然无法表示不同大小。
  一些可能的思路：
  1. prod 也许有能力编码不同类型
  2. 分块时可能需要一个动态构造的类型
   *)

  (* 基础元素类型，要求是一个确定的类型 *)
  Variable A : Type.

  (** 比如这个例子
      1 0 0
      0 2 3
      0 4 5
      可以把它分块成 
      A11 A12
      A21 A22
      其中，A11 = [[1]], A12=[[0 0]], A21是2*1的，A22是2*2的。
  *)

  (* 定义一些矩阵类型 *)
  Definition m11 := @mat A 1 1. (* 1x1 矩阵 *)
  Definition m12 := @mat A 1 2.
  Definition m21 := @mat A 2 1.
  Definition m22 := @mat A 2 2.

  (* 定义一些矩阵元素 *)
  Variable a11 : m11.
  Variable a12 : m12.
  Variable a21 : m21.
  Variable a22 : m22.

  (* 先考虑类型，它可以放到 prod 或 list 中，因为它们都是 Type *)
  Check (m11,m12).
  Check [m11;m12].
  
  (* 再考虑元素，prod可以，list不行 *)
  Check (a11,a12).
  Fail Check [a11;a12].

  (* 也不能放到函数中 *)
  Fail Check fun i : nat => match i with 0 => a11 | _ => a12 end.

  (** 暂时看起来只有 prod 有能力来收集这种不同类型的数据 *)

  (** 看看能否用它来表达矩阵类型？*)

  (* 先手动静态的构造 *)
  Definition m11_12 := (m11 * m12)%type.
  Definition a11_12 : m11_12 := (a11,a12).

  Definition m11_12_21_22 := ((m11 * m12) * (m21 * m22))%type.
  Definition a11_12_21_22 : m11_12_21_22 := ((a11,a12),(a21,a22)).

  (* 如何动态的构造？
     1. 先构造类型，使用 mat 
     2. 再转换为 prod ？
     3. 再构造数据
   *)

  (* “矩阵为元素的矩阵”的类型 *)
  Definition tpMM : @mat Type 2 2 := l2m m11 [[m11;m12];[m21;m22]].

  (* 转换为 prod *)
  Definition tupleMM := m2t_2_2 tpMM.
  Compute tupleMM.

  (* 构造数据 *)
  Fail Definition tupleMM_ex1 : tupleMM nat.
  

End defs.



(** 
(** *** matrix type and basic operation *)
Definition mat (r c : nat) : Type := @mat A r c.

Infix "==" := (eqlistA (eqlistA eq)) : dlist_scope.
Infix "!=" := (fun d1 d2 => ~(d1 == d2)%dlist) : dlist_scope.
Infix "==" := (meq (Aeq:=eq)) : mat_scope.
Infix "!=" := (fun m1 m2 => ~(m1 == m2)%M) : mat_scope.
Notation "m ! i ! j " := (mnth A0 m i j) : mat_scope.

Lemma meq_iff_mnth : forall {r c} (m1 m2 : mat r c),
    m1 == m2 <-> (forall i j : nat, i < r -> j < c -> m1!i!j = m2!i!j)%nat.
Proof. intros. apply meq_iff_mnth. Qed.

(** *** convert between list and matrix *)
Definition l2m (r c : nat) (dl : dlist A) : mat r c := l2m A0 dl.
Definition m2l {r c : nat} (m : mat r c) : dlist A := m2l m.

Lemma m2l_length : forall {r c} (m : mat r c), length (m2l m) = r.
Proof. intros. apply m2l_length. Qed.

Lemma m2l_width : forall {r c} (m : mat r c), width (m2l m) c.
Proof. intros. apply m2l_width. Qed.

Lemma m2l_l2m_id : forall {r c} (dl : dlist A),
    length dl = r -> width dl c -> (m2l (l2m r c dl) == dl)%dlist.
Proof. intros. apply m2l_l2m_id; auto. Qed.

Lemma l2m_m2l_id : forall {r c} (m : mat r c), l2m r c (m2l m) == m.
Proof. intros. apply l2m_m2l_id; auto. Qed.

Lemma l2m_inj : forall {r c} (d1 d2 : dlist A),
    length d1 = r -> width d1 c -> length d2 = r -> width d2 c -> 
    (d1 != d2)%dlist -> l2m r c d1 != l2m r c d2.
Proof. intros. apply l2m_inj; auto. Qed.

Lemma l2m_surj : forall {r c} (m : mat r c), (exists d, l2m r c d == m). 
Proof. intros. apply l2m_surj; auto. Qed.

Lemma m2l_inj : forall {r c} (m1 m2 : mat r c), m1 != m2 -> (m2l m1 != m2l m2)%dlist.
Proof. intros. apply (m2l_inj (A0:=A0)); auto. Qed.

Lemma m2l_surj : forall {r c} (d : dlist A), length d = r -> width d c -> 
    (exists m : mat r c, (m2l m == d)%dlist).
Proof. intros. apply (m2l_surj (A0:=A0)); auto. Qed.

(** *** convert between tuple and matrix *)
Definition t2m_3_3 (t : T_3_3) : mat 3 3 := t2m_3_3 A0 t.
Definition m2t_3_3 (m : mat 3 3) : T_3_3 := m2t_3_3 m.
Definition m2t_1_1 (m : mat 1 1) := m2t_1_1 m.

(** *** build matrix from elements *)
Definition mk_mat_1_1 a11 : mat 1 1 := mk_mat_1_1 (A0:=A0) a11.
Definition mk_mat_3_1 a11 a12 a13 : mat 3 1 := mk_mat_3_1 (A0:=A0) a11 a12 a13.
Definition mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33 : mat 3 3 :=
  mk_mat_3_3 (A0:=A0) a11 a12 a13 a21 a22 a23 a31 a32 a33.

(** *** matrix transposition *)
Definition mtrans {r c : nat} (m : mat r c) : mat c r := mtrans m.
Notation "m \T" := (mtrans m) : mat_scope.

Lemma mtrans_trans : forall {r c} (m : mat r c), m \T\T == m.
Proof. intros. apply mtrans_trans. Qed.

(** *** matrix mapping *)
Definition mmap {r c} f (m : mat r c) : mat r c := mmap f m.
Definition mmap2 {r c} f (m1 m2 : mat r c) : mat r c := mmap2 f m1 m2.

Lemma mmap2_comm : forall {r c} (m1 m2 : mat r c) f (fcomm : Commutative f eq),
    mmap2 f m1 m2 == mmap2 f m2 m1.
Proof. intros. apply mmap2_comm; auto. Qed.

Lemma mmap2_assoc : forall {r c} f (m1 m2 m3 : mat r c) (fassoc : Associative f eq),
    mmap2 f (mmap2 f m1 m2) m3 == mmap2 f m1 (mmap2 f m2 m3).
Proof. intros. apply mmap2_assoc; auto. Qed.


(* ======================================================================= *)
(** ** Matrix theory applied to this type *)


(* ======================================================================= *)
(** ** Usage demo *)
Section test.
  Let l1 := [[1;2;3];[4;5;6]].
  Let m1 := l2m 2 2 l1.
  (* Compute m2l m1.       (* = [[1; 2]; [3; 4]] *) *)
  (* Compute m2l (mmap S m1).       (* = [[2; 3]; [4; 5]] *) *)

  Variable a11 a12 a21 a22 : nat.
  Let m2 := l2m 2 2 [[a11;a12];[a21;a22]].
  (* Compute m2l m2.       (* = [[a11; a12]; [a21; a22]] *) *)
  (* Compute m2l (mmap S m2).     (* = [[S a11; S a12]; [S a21; S a22]] *) *)
  
End test.

*)
