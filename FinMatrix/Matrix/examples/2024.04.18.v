(* 
   purpose  : examples in presentation
   author   : ZhengPu Shi
   date     : 2024.04.18
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

(* Vector over monoid $\langle \mathbb{N},+,0\rangle$ *)
Section vec_monoid_nat.
  Import MatrixNat.  Open Scope vec_scope.

  (* 创建向量 *)
  Let a : vec 5 := l2v [1;2;3;4;5;6;7].
  Let b : vec 5 := fun i => match (fin2nat i) with 1 => 3 | _ => 0 end.
  Compute v2l a.  (* = [1; 2; 3; 4; 5] : list A *)
  Compute v2l b.  (* = [0; 3; 0; 0; 0] *)

  (* 取元素，两种 notation *)
  Compute a.[#1].  (* = 2 *) (* #1 是第2个元素，下标从0开始，计算机惯例 *)
  Compute a.2.      (* = 2 *) (* .2 是第2个元素，下标从1开始，数学惯例 *)

  (* 向量加法 *)
  Compute v2l (a + b).   (* = [1; 5; 3; 4; 5] : list A *)

  (* 元素求和 *)
  Compute vsum a.  (* = 15 *)
End vec_monoid_nat.

(* Conversion between $\mathtf{vec,cvec,rvec}$ *)
Section vec_cvec_rvec.
  Import MatrixNat.  Open Scope vec_scope.

  (* 创建 向量、列矩阵、行矩阵 *)
  Let a : vec 3 := l2v [1;2;3].
  Let b : cvec 3 := l2m [[4];[5];[6]].
  Let c : rvec 3 := l2m [[7;8;9]].

  (* 向量 <-> 列矩阵 *)
  Check v2cv a.  (* v2cv a : cvec 3 *)
  Check cv2v b.  (* cv2v b : vec 3 *)
  
  (* 向量 <-> 行矩阵 *)
  Check v2rv a.  (* v2rv a : rvec 3 *)
  Check rv2v c.  (* rv2v c : vec 3 *)
  
End vec_cvec_rvec.

(* Matrix over monoid $\langle \mathbb{N},+,0\rangle$ *)
Section mat_monoid_nat.
  Import MatrixNat.  Open Scope mat_scope.

  (* 创建稠密矩阵 *)
   Let M : mat 2 3 := l2m [[1;2;3];[4]].
  Compute m2l M. (* = [[1; 2; 3]; [4; 0; 0]] : dlist A *)

  (* 创建系数矩阵 *)
  Let N : mat 3 3 := fun i j => if (i ??= j)%fin then 1 else 0.
  Compute m2l N.  (* = [[1; 0; 0]; [0; 1; 0]; [0; 0; 1]] : dlist A *)

  (* 取出元素 *)
  Compute M.[#0].[#1].  (* = 2 : A *)    Compute M.1.2.  (* = 2 : A *)
  (* 矩阵加法 *)
  Compute m2l (N + N).  (* = [[2; 0; 0]; [0; 2; 0]; [0; 0; 2]] : dlist A *)
  (* 矩阵转置 *)
  Compute m2l (M\T).   (* = [[1; 4]; [2; 0]; [3; 0]] : dlist A *)
  (* 创建对角矩阵 *)
  Compute m2l (mdiagMk (@l2v 3 [1;2;3])). (* = [[1; 0; 0]; [0; 2; 0]; [0; 0; 3]] : dlist A *)
End mat_monoid_nat.

(* Vector over ring $\langle \mathbb{Z},+,0,-x,*,1\rangle$ *)
Section vec_ring_Z.
  Import MatrixZ.  Open Scope vec_scope.
  Let u := @l2v 3 [1;2;-3].  (*  u = [1; 2; -3] *)
  Let v := @f2v 3 (fun i => -1 + nat2Z i)%Z. (* v = [-1; 0; 1] *)

  (* 向量取反 *)
  Compute v2l (- u).         (* = [-1; -2; 3] *)
  (* 向量减法 *)
  Compute v2l (u - v).       (* = [2; 2; -4] *)
  (* 向量数乘 *)
  Compute v2l (5 \.* u).     (* = [5; 10; -15] *)
  (* 向量点乘 *)
  Compute <u, v>.            (* = -4 *)
  (* 向量求和 *)
  Compute vsum u.            (* = 0 *)

  (* 谓词：一个向量是单位向量 *)
  Check vunit u.
  (* 谓词：两个向量是正交的（二维和三维上也称垂直） *)
  Check u _|_ v.

  (* <向量加法, 零向量, 向量取反> 构成交换群，可用群论自动完成部分证明 *)
  Check vadd_AGroup.   (* : forall n : nat, AGroup vadd vzero vopp *)
End vec_ring_Z.

(* Matrix over ring $\langle \mathbb{Z},+,0,-x,*,1\rangle$ *)
Section mat_ring_Z.
  Import MatrixZ.  Open Scope mat_scope.
  Let M := @l2m 3 3 [[1;2;3];[4;5;6];[7;8;9]].
  Let N := @l2m 3 3 [[1;4;5];[2;3;8];[9;7;6]].
  Let a := @l2v 3 [1;2;3].

  (* 矩阵取反 *)
  Compute m2l (- M).     (* = [[-1; -2; -3]; [-4; -5; -6]; [-7; -8; -9]] *)
  (* 矩阵减法 *)
  Compute m2l (M - N).   (* = [[0; -2; -2]; [2; 2; -2]; [-2; 1; 3]] *)
  (* 矩阵数乘 *)
  Compute m2l (5 \.* M). (* = [[5; 10; 15]; [20; 25; 30]; [35; 40; 45]] *)
  (* 矩阵乘法 *)
  Compute m2l (M * N).   (* = [[32; 31; 39]; [68; 73; 96]; [104; 115; 153]] *)
  (* 矩阵乘向量(向量先被转换为列矩阵) *)
  Compute v2l (M *v a).  (* = [14; 32; 50] : list A *)
  (* 向量乘矩阵(向量先被转换为行矩阵) *)
  Compute v2l (a v* M).  (* = [30; 36; 42] : list A *)

  (* 方阵的迹 *)
  Compute mtrace M.  (* = 15 *)     Compute tr M.
  (* 方阵的行列式 *)
  Compute mdet N.    (* = 137 *)    Compute |N|.
  (* 方阵的伴随矩阵(adjoint matrix) *)
  Compute m2l (madj M).   (* = [[-3; 6; -3]; [6; -12; 6]; [-3; 6; -3]] *)

  (* 谓词：一个方阵是可逆的 *)
  Check minvertible M.
  (* 谓词：一个方阵是奇异的 *)
  Check msingular M.

  (* <矩阵加法, 零矩阵, 矩阵取反> 构成交换群，可用群论自动完成部分证明 *)
  Check madd_AGroup.   (* : forall r c : nat, AGroup madd mat0 mopp *)
End mat_ring_Z.

(* Vector over field $\langle \mathbb{R},+,0,-x,*,1,/x\rangle$ *)
Section vec_field_R.
  Import MatrixR. Open Scope vec_scope.
  Variable n : nat. Variable a b : vec n.
  Variable c1 c2 : vec 2. Variable c3 c4 : vec 3.

  (* The projection component of a onto b *)
  Check vproj.     (* : vec ?n -> vec ?n -> vec ?n *)

  (* The perpendicular component of b respect to a *)
  Check vperp.     (* : vec ?n -> vec ?n -> vec ?n *)

  (* Two non-zero vectors are collinear, if the components are proportional *)
  Check a // b.      Check vcoll a b.
  (* Two non-zero vectors are parallel, if positive proportional *)
  Check a //+ b.     Check vpara a b.
  (* Two non-zero vectors are antiparallel, if negative proportional *)
  Check a //- b.     Check vantipara a b.
  (* Length of a vector *)
  Check || a ||.        Check vlen a.

  (* Normalization of a non-zero *)
  Check vnorm a.
  (* The angle between vector a and b, Here, $\theta \in [0,\pi]$ *)
  Check a /_ b.   Check vangle a b.

  (* 2D vector angle from one to another. Here, $\theta \in (-\pi,\pi]$ *)
  Check c1 /2_ c2.   Check vangle2 c1 c2.

  (* The cross product of 3D vectors *)
  Check c3 \x c4.    Check v3cross c3 c4.
End vec_field_R.

(* Matrix over field $\langle \mathbb{R},+,0,-x,*,1,/x\rangle$ *)
Section mat_field_R.
  Import MatrixR. Open Scope mat_scope.

  (** 矩阵在几何方面的应用 *)
  
  (* 谓词：一个矩阵是正交的 *)
  Check morth.       (* : smat ?n -> Prop *)

  (** Orthogonal matrix will keep length. *)
  Check morth_keep_length. (* : forall {n} (M : smat n) (a : vec n),
                              morth M -> ||M *v a|| = ||a||. *)
  (* Orthogonal matrix will keep angle. *)
  Check morth_keep_angle. (* : forall {n} (M : smat n) (a b : vec n),
                             morth M -> (M *v a) /_ (M *v b) = a /_ b. *)
  (* Orthogonal matrix with determinant 1 keep v3cross *)
  Check morth_keep_v3cross_det1. (* : forall (M : smat 3) (a b : vec 3),
      morth M -> mdet M = 1 -> (M *v a) \x (M *v b) = (M *v (a \x b)). *)

  (* SO(n): Special Orthogonal Group, Rotation Group. (orthogonal + determiant 1) *)
  Check SOn.
  (* <SO(n), M+N, mat1, M\T> is a group *)
  Check SOn_Group.  (* : forall n : nat, Group SOn_mul SOn_1 SOn_inv *)

  (** 矩阵在代数方面的应用，比如利用逆矩阵解方程 *)
  
  (* Cramer rule, which can solve the equation with the form of A*x=b *)
  Check cramerRule.  (* : smat ?n -> vec ?n -> vec ?n *)

  (* Check the invertibility of matrix `M` *)
  Check minvertiblebGE.  (* : smat ?n -> bool *)
  (* Inverse matrix (option version) *)
  Check minvoGE.    (* : smat ?n -> option (smat ?n) *)
  (* Inverse matrix (with identity matrix as default value) *)
  Check minvGE.     (* : smat ?n -> smat ?n *)
  (* Inverse matrix with lists for input and output *)
  Check minvListGE. (* : nat -> dlist A -> dlist A *)
  (* Solve the equation with the form of A*x=b. *)
  Check solveEqGE.     (* : smat ?n -> vec ?n -> vec ?n *)

  (* Check the invertibility of matrix `M` *)
  Check minvertiblebAM.  (* : smat ?n -> bool *)
  (* Inverse matrix (option version) *)
  Check minvoAM.    (* : smat ?n -> option (smat ?n) *)
  (* Inverse matrix (with identity matrix as default value) *)
  Check minvAM.     (* : smat ?n -> smat ?n *)
  (* Inverse matrix with lists for input and output *)
  Check minvListAM. (* : nat -> dlist A -> dlist A *)
  (* Solve the equation with the form of A*x=b. *)
  Check solveEqAM.     (* : smat ?n -> vec ?n -> vec ?n *)
End mat_field_R.

(* 一些重要的数学性质 *)
Section important_prop.
  Import MatrixR.
  Check vsum_vsum.
  (* : forall (r c : nat) (a : Vector.vec r),
       vsum (fun i : 'I_r => vsum (fun j : 'I_c => a i j)) =
       vsum (fun j : 'I_c => vsum (fun i : 'I_r => a i j)) *)
  
  Check morth_keep_v3cross_det1.
  (* : forall (M : smat 3) (a b : vec 3),
     morth M -> |M| = 1 -> M *v a \x M *v b = M *v (a \x b) *)
  
  Check morth_iff_mcolsOrthonormal.
  (* : forall M : smat ?n, morth M <-> mcolsOrthonormal M *)
  
  Check morth_iff_mrowsOrthonormal.
  (* : forall M : smat ?n, morth M <-> mrowsOrthonormal M *)
End important_prop.

(* 逆矩阵解方程的例子 *)
Section inv_solve_equation.
  Import MatrixQc.
  Open Scope Q_scope.

  Check cramerRuleListQ.
  Check solveEqListQ.
End inv_solve_equation.
