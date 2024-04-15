(* 
   purpose  : examples for matrix inversion in presentation 2024.04.16
   author   : ZhengPu Shi
   date     : 2024.04.15
 *)

Require MatrixNat MatrixZ MatrixQc MatrixR.

(* 有限集类型，用于表示向量、矩阵等的下标 *)
Section ex_fin.
  (* 导入库 *)
  Import Fin.

  (* 有限集类型，“小于 n 的自然数类型” 记作 'I_n *)
  Print fin.
  (* Inductive fin (n : nat) : Set :=  Fin : forall i : nat, i < n -> 'I_n. *)
  
  (* 每个 'I_n 对象都需要 i < n 的证明 *)
  Check @Fin 3 1. (* Fin 1 : 1 < 3 -> 'I_3 *)

  (* 'I_3 类型只能是以下的这三个项 *)
  Check @Fin 3 0 _ : 'I_3.
  Check @Fin 3 1 _ : 'I_3.
  Check @Fin 3 2 _ : 'I_3.

  (* 由于证明无关性， @Fin n i H1 和 @Fin n i H2 相等 *)
  Goal forall n i (H1 H2 : i < n), @Fin n i H1 = @Fin n i H2.
  Proof. intros. f_equal. apply proof_irrelevance. Qed.

  (* 如何构造一个 'I_n 对象？ *)
  
  (* 'I_0 对象会证明所有命题 *)
  Goal forall P : Prop, fin 0 -> P.
  Proof. intros. destruct H. lia. Qed.

  (* 可用 nat2finS 构造 'I_(S n) 类型的项，记作 #i *)
  Check @nat2finS 2 1.  (* #1 : 'I_3 *)
  Check #1 : 'I_3.      (* #1 : 'I_3 *)

  (** 一些可能碰到的问题 *)
  
  (* 当 i 不小于 n 时， 使用默认值 @Fin n 0。需要特别注意！ *)
  Compute #5 : 'I_3.  (* = Fin 0 (Nat.lt_0_succ 2) : 'I_3 *)

  (* fin n 是依赖类型，即，类型依赖于值的一种类型。
     优点之一是更强的类型描述能力，缺点之一是太强的类型约束 *)
  Variable i1 : fin 3.
  Check i1 : fin (1 + 2). (* 由于 1 + 2 可归约到 3，这是合法的 *)
  
  Variable n m : nat. Variable i2 : fin (n + m).
  Fail Check i2 : fin (m + n).
  (* The term "i2" has type "'I_(n + m)" while it is expected to have type "'I_(m + n)". *)
  (* Coq无法自动利用 n + m = m + n 这一事实。
     因为该等式只在全称量词下成立，而类型检查算法也许无法处理 *)

  (* 可以 cast_fin 函数来转换 *)
  Variable H : n + m = m + n.
  Check cast_fin H i2 : fin (m + n).
End ex_fin.

  
(* 元素类型为nat的向量 *)
Section ex_nat_vec.
  (* 导入库，打开作用域 *)
  Import MatrixNat.  Open Scope vec_scope.

  (* 使用列表来创建稠密向量 *)
  Let v1 : vec 5 := l2v [1;2;3;4;5;6;7].
  (* 查看向量内容 *)
  Compute v2l v1.  (* = [1; 2; 3; 4; 5] : list A *)

  (* 使用函数来创建稀疏向量 *)
  Let v2 : vec 5 := fun i => match (fin2nat i) with 1 => 3 | _ => 0 end.
  Compute v2l v2.  (* = [0; 3; 0; 0; 0] *)

  (* 取出元素 *)
  Compute v1.[#1].  (* #1 是第2个元素，下标从0开始，计算机惯例 *)
  Compute v1.2.     (* .2 是第2个元素，下标从1开始，数学惯例 *)
  (* 元素求和 *)
  Compute vsum add 0 v1.  (* = 15 *)
  (* 向量加法 *)
  Compute v2l (v1 + v2).   (* = [1; 5; 3; 4; 5] : list A *)
End ex_nat_vec.


(* 元素类型为nat的矩阵 *)
Section ex_nat_mat.
  (* 导入库，打开作用域 *)
  Import MatrixNat.  Open Scope mat_scope.

  (* 使用列表来创建稠密矩阵 *)
  Let M1 : mat 2 3 := l2m [[1;2;3];[4]].
  Compute m2l M1. (* = [[1; 2; 3]; [4; 0; 0]] : dlist A *)

  (* 使用函数来创建矩阵 *)
  Let M2 : mat 3 3 := fun i j => if (i ??= j)%fin then 1 else 0.
  Compute m2l M2.  (* = [[1; 0; 0]; [0; 1; 0]; [0; 0; 1]] : dlist A *)

  (* 取出元素 *)
  Compute M1.[#0].[#1].  (* = 2 : A *)    Compute M1.1.2.  (* = 2 : A *)
  (* 矩阵加法 *)
  Compute m2l (M2 + M2).  (* = [[2; 0; 0]; [0; 2; 0]; [0; 0; 2]] : dlist A *)
  (* 矩阵转置 *)
  Compute m2l (M1\T).   (* = [[1; 4]; [2; 0]; [3; 0]] : dlist A *)
  (* 对角矩阵 *)
  Compute m2l (mdiagMk (@l2v 3 [1;2;3])). (* = [[1; 0; 0]; [0; 2; 0]; [0; 0; 3]] : dlist A *)
End ex_nat_mat.

(* 元素类型为Z的向量 *)
Section ex_Z_vec.
  Import MatrixZ.  Open Scope vec_scope.

  Let u := @l2v 3 [1;2;-3].
  Let v := @f2v 3 (fun i => -1 + nat2Z i)%Z.
  Compute v2l (u + v).          (* 向量加法 *)
  Compute v2l (- u).            (* 取反 *)
  Compute v2l (u - v).          (* 减法 *)
  Compute v2l (5 \.* u).        (* 数乘 *)
  Compute <u, v>.               (* 点乘 *)
  Compute vsum u.               (* 求和 *)
  Check vunit u.                (* 单位向量谓词 *)
  Check u _|_ v.                (* 正交（二维和三维上也即垂直） *)

  (* 与这些操作有关的大量性质，例如 *)
  Check vsum_vsum.     (* 两次求和可交换下标 *)
  (* : forall (r c : nat) (a : Vector.vec r),
          vsum (fun i : 'I_r => vsum (fun j : 'I_c => a i j)) =
          vsum (fun j : 'I_c => vsum (fun i : 'I_r => a i j)) *)
  
  Check vdot_comm.     (* 点乘交换 *)
  (* : forall a b : vec ?n,  <a,b> = <b,a> *)
  
End ex_Z_vec.

(* 元素类型为Z的矩阵 *)
Section ex_Z_mat.
  Import MatrixZ.  Open Scope mat_scope.
  
  Let M1 := @l2m 3 3 [[1;2;3];[4;5;6];[7;8;9]].
  Let M2 := @l2m 3 3 [[1;4;5];[2;3;8];[9;7;6]].
  Compute m2l (M1 + M1).        (* 矩阵加法 *)
  Compute m2l (M1 - M2).        (* 减法 *)
  Compute m2l (- M1).           (* 取反 *)
  Compute m2l (5 \.* M1).       (* 数乘 *)
  Compute m2l (M1 * M2).        (* 乘法 *)
  Compute tr M1.                (* 迹 *)
  Compute mdet M2.              (* 行列式 *)
  Compute m2l (madj M1).        (* 伴随矩阵(adjoint) *)
End ex_Z_mat.
