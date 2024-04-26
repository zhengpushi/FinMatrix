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
  Let b : vec 5 := f2v (fun i => match i with 1 => 3 | _ => 0 end).
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
  Let N : mat 3 3 := f2m (fun i j => if (i ??= j) then 1 else 0).
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

  (* 谓词：一个向量是单位向量。定义为：与自身的点积为1 *)
  Check vunit u.             (* : Prop  *)
  Print Vector.vunit.        (* forall a : vec n, <a, a> = 1 *)
  (* 谓词：两个向量是正交的（二维和三维上也称垂直）。定义为：点积为0 *)
  Check u _|_ v.             (* : Prop  *)
  Print Vector.vorth.        (* forall a b : vec n, <a, b> = 0 *)

  (* <向量加法, 零向量, 向量取反> 构成交换群，可用群论自动化证明。见 vsub_xx *)
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

  (* 谓词：一个方阵是可逆的。定义为：存在M'，使得 M'*M=I 并且 M*M'=I *)
  Check minvtble M.
  Print MatrixInvBase.minvtble. (* forall M, exists M', M * M' = I /\ M' * M = I *)
  (* 谓词：一个方阵是奇异的。定义为：不是“可逆的” *)
  Check msingular M.

  (* <矩阵加法, 零矩阵, 矩阵取反> 构成交换群，可用群论自动化证明 *)
  Check madd_AGroup.   (* : forall r c : nat, AGroup madd mat0 mopp *)
End mat_ring_Z.

(* Vector over field $\langle \mathbb{R},+,0,-x,*,1,/x\rangle$ *)
Section vec_field_R.
  Import MatrixR. Open Scope vec_scope.
  Variable n : nat. Variable a b : vec n.

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
  Check || a ||. (* : R *)    Check vlen a.
  Print Vector.vlen.
  (* 原本只在实数域定义了长度，现在扩展为任意的度量空间内 *)

  (* Normalization of a non-zero vector *)
  Check vnorm a.     (* : vec n *)
  (* The angle between vector a and b, Here, $\theta \in [0,\pi]$ *)
  Check a /_ b.  (* : R *)   Check vangle a b.

  (* 2D vector angle from one to another. Here, $\theta \in (-\pi,\pi]$ *)
  Variable c1 c2 : vec 2.
  Check c1 /2_ c2.  (* : R *) Check vangle2 c1 c2.

  (* The cross product of 3D vectors *)
  Variable c3 c4 : vec 3.
  Check c3 \x c4.  (* : vec 3 *)   Check v3cross c3 c4.
End vec_field_R.

Section vec_Qc.
  Import MatrixQc.
  Variable n : nat.
  Variable u : vec n.
  Check || u ||.
  (* Qc上的向量可定义度量空间，度量函数为 a2r *)
  Search a2r.
  Print Hierarchy.ConvertToR.
End vec_Qc.


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
  Check minvtblebGE.  (* : smat ?n -> bool *)
  (* Inverse matrix (option version) *)
  Check minvoGE.    (* : smat ?n -> option (smat ?n) *)
  (* Inverse matrix (with identity matrix as default value) *)
  Check minvGE.     (* : smat ?n -> smat ?n *)
  (* Inverse matrix with lists for input and output *)
  Check minvListGE. (* : nat -> dlist A -> dlist A *)
  (* Solve the equation with the form of A*x=b. *)
  Check solveEqGE.     (* : smat ?n -> vec ?n -> vec ?n *)

  (* Check the invertibility of matrix `M` *)
  Check minvtblebAM.  (* : smat ?n -> bool *)
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
  Check forall (r c : nat) (a : @Vector.vec (@Vector.vec R c) r),
       vsum (fun i : 'I_r => vsum (fun j : 'I_c => a i j)) =
       vsum (fun j : 'I_c => vsum (fun i : 'I_r => a i j)).
  
  Check morth_keep_v3cross_det1.
  (* : forall (M : smat 3) (a b : vec 3),
     morth M -> |M| = 1 -> M *v a \x M *v b = M *v (a \x b) *)
  
  Check morth_iff_mcolsOrthonormal.
  (* : forall M : smat ?n, morth M <-> mcolsOrthonormal M *)
  
  Check morth_iff_mrowsOrthonormal.
  (* : forall M : smat ?n, morth M <-> mrowsOrthonormal M *)
End important_prop.

(* 解方程的例子 *)
Section solve_equation.
  Import MatrixQc.  Open Scope Q_scope.
  Let C := [[6;0;1];[0;4;1];[-3;-2;1]].  Let b := [4;0;2].

  (* 方法1: cramer rule *)
  Compute cramerRuleListQ 3 C b. (* = [1 # 3; -1 # 2; 2] : list Q *)
  
  (* 方法2: $X = C^{-1} b$ *)
  Compute solveEqListQ 3 C b.  (* = [1 # 3; -1 # 2; 2] : list Q *)
  (* 实际上，方法2内部有两种做法，GE和AM，默认使用GE *)
  Compute solveEqListGEQ 3 C b.
  Compute solveEqListAMQ 3 C b.
End solve_equation.

(* 在Qc类型上，Eval cbv 与 Compute 的区别 *)
Section cbv_Compute.
  
  (* 注意，
     Eval cbv in xx
     Compute xx
     这二者的计算速度不同。
     1. 如果都是常数，则二者都很快。
        Compute xx 是 Eval vm_compute in xx 的缩写，它是编译为字节码后运行。
     2. 如果含有 Variable，则二者都很慢，甚至卡死。
        但是如果将某些运算设置为 Opaque，则 Eval cbv in xx 可以工作，但 Compute 仍然卡死。
        并且，无论是否设置 Opaque 选项，Compute都会展开它们
   *)
  Import MatrixQc.
  
  (* 计算“常数构成的表达式” *)
  Section ex1.
    Let M : smat 2 := @l2m 2 2 (Q2Qc_dlist [[1;2];[3;4]]%Q).
    
    (* Compute |M|. *)
    (* = {| this := -2; canon := Qred_involutive (-2) |} *)

    (* Eval cbv in |M|. *)
    (* = {| this := -2; canon := Qred_involutive (-2) |} *)

    (* 如果执行了 Opaque 指令，则 Compute 仍然会展开，而 Eval cbv 会尊重这些指令 *)
    Opaque Qcplus Qcopp Qcmult Q2Qc.

    (* Compute |M|. *)
    (* = {| this := -2; canon := Qred_involutive (-2) |} *)
    
    (* Eval cbv in |M|. *)
    (* = (Q2Qc 0 + 1 * (Q2Qc 4 * 1) + - (Q2Qc 2 * (Q2Qc 3 * 1)))%Qc *)
  End ex1.

  (* 计算“含有变量的表达式” *)
  Section ex2.
    Variable q11 : Q.
    Let M : smat 2 := @l2m 2 2 (Q2Qc_dlist [[q11;2];[3;4]]%Q).
    
    (* 直接计算，基本上会卡死 *)
    (* Compute |M|. *)
    (* Eval cbv in |M|. *)

    (* 执行 Opaque 指令后，Eval cbv 可以运行 *)
    Opaque Qcplus Qcopp Qcmult Q2Qc.
    Eval cbv in |M|.
    (* = (Q2Qc 0 + Q2Qc q11 * (Q2Qc 4 * 1) + - (Q2Qc 2 * (Q2Qc 3 * 1)))%Qc *)
  End ex2.
End cbv_Compute.

(* 用 R 类型处理矩阵 *)
Section solve_equation.
  Import MatrixR.
  
  (* 优点：可处理无理数。此处，将 [6;0;1] 换成了 [6;0;PI] *)
  Let C := [[6;0;PI];[0;4;1];[-3;-2;1]].
  Let b := [4;0;2].

  (* 缺点：计算结果展开太多，不直观 *)
  Compute cramerRuleList 3 C b.
  (* = [(((R1 + R1) * (R1 + R1) *
   ((R1 + R1) * (R1 + R1) * (R1 * R1 + R0) + (- R1 * (- (R1 + R1) * R1 + R0) + R0)) +
   (- R0 * (R0 * (R1 * R1 + R0) + (- R1 * ((R1 + R1) * R1 + R0) + R0)) +
   ... *)

  (* 另一种方法：交互式的进行，并利用 field_simplify 得到简洁的结果 *)
  Variable x1 x2 x3 : A.
  Goal cramerRuleList  3 C b = [x1;x2;x3].
  Proof.
    cbv; list_eq; field_simplify.
(*
  (-8 * PI + 24) / (12 * PI + 36) = x1
goal 2 (ID 250) is:
 (36 + PI * 12)%R <> 0
goal 3 (ID 317) is:
 -24 / (12 * PI + 36) = x2
goal 4 (ID 333) is:
 (36 + PI * 12)%R <> 0
goal 5 (ID 400) is:
 96 / (12 * PI + 36) = x3
goal 6 (ID 416) is:
 (36 + PI * 12)%R <> 0
 *)
  Abort.

  (* 可以看出，此处的分数并未消去公约数，但已经比较便于阅读了。
     我们可以得解析解：
     x1 = (-8 * PI + 24) / (12 * PI + 36);
     x2 = -24 / (12 * PI + 36)
     x3 = 96 / (12 * PI + 36)
   *)

  (* 同理，也可以使用 solveEqList 方法，但最好使用 NoCheck 版本 *)
  Compute solveEqListNoCheck 3 C b.

End solve_equation.

(* SPICE的应用 *)
Section SPICE.
  Import MatrixR.
  Variable n b : nat.             (* n个节点，b条支路 *)
  Variable A : mat n b.         (* 关联矩阵 *)
  Variable U : cvec b.          (* 支路电压 *)
  Variable I : cvec b.          (* 支路电流 *)
  Variable Is : cvec n.         (* 注入电流 *)
  Variable Un : cvec n.         (* 节点电压 *)
  Variable G : smat b.          (* 支路导纳矩阵 *)
  Definition Y := A * G * A\T.      (* 节点导纳矩阵 *)
  Hypotheses KCL : A * I = Is.      (* KCL关系 *)
  Hypotheses KVL : A\T * Un = U.   (* KVL关系 *)
  Hypotheses H1 : G * U = I.         (* 通过导纳描述支路的约束方程 *)

  Lemma eq4 : G * A\T * Un = I.
  Proof. rewrite <- H1. rewrite <- KVL. rewrite mmul_assoc. auto. Qed.

  Lemma eq5 : A * G * A\T * Un = Is.
  Proof. rewrite <- KCL. rewrite !mmul_assoc, <- (mmul_assoc G), eq4. auto. Qed.

  Lemma eq6 : Y * Un = Is.
  Proof. unfold Y. rewrite eq5. auto. Qed.
End SPICE.

(* 有限集Fin *)
Module fin.
  Import Extraction.
  
  (* 本文的实现。参考了 mathcomp.ordinal 的定义和记号 *)
  Module FinMatrix.
    Inductive fin (n : nat) := Fin (i : nat) (E : i < n).
    Notation "''I_' n" := (fin n)  (at level 8).
    Extraction fin.
  End FinMatrix.

  (* 等价于使用sig，但是使用 Inductive 可避免因过于多态的 sig 类型而带来不必要的复杂性 *)
  Module by_sig.
    Definition fin (n : nat) := {i | i < n}.
  End by_sig.

  (* 使用 unit 表示 fin 0 *)
  Module DPIA.
    Definition fin (n : nat) := match n with O => unit |  _ => {i : nat | i < n} end.
    Extraction fin.
  End DPIA.

  (* 使用冗余的下标 *)
  Module method3.
    Definition fin (n : nat) := {i | i <= n}.
    Extraction fin.
    (* 特点：
       1. fin 0 = {0}
          fin 1 = {0,1}
          fin 2 = {0,1,2}
     *)
  End method3.

  (* Coq标准库 *)
  Module CoqStdLib.
    Import Coq.Vectors.Fin.
    Print t.
    Inductive t : nat -> Set := F1 n : t (S n) | FS n (x : t n) : t (S n).
    Extraction t.
  End CoqStdLib.
End fin.

(* 向量 *)
Module vector.
  Import Vector.

  Print vec.
  Locate ".[".
  
End vector.

(* 矩阵 *)
Module matrix.
  Import Matrix.

  Print mat.

  Variable A : Type.  Variable r c : nat.
  Compute mat A r c. (* = 'I_r -> 'I_c -> A : Type *)

  Goal mat A r c = ('I_r -> 'I_c -> A).
  Proof. reflexivity. Qed.

  Definition mat_old := list (list A).
  
  Print mtrans.

  Variable M : @vec (@vec (@vec A 5) 4) 3. (* 元素为 A 的 3*4*5 维的矩阵 *)
  Check M : @vec (@mat A 4 5) 3.           (* 元素为 mat A 4 5 的 3 维向量 *)
  Check M : @mat (@vec A 5) 3 4.           (* 元素为 vec A 5 的 3*4 维的矩阵 *)

  (* 测试代码抽取，以矩阵加法为例 *)
  Recursive Extraction madd.
(* type fin = int

   type 'a vec = fin -> 'a

   let vmap2 f _ a b i =

   let madd aadd r c m n =
       vmap2 (vmap2 aadd c) r m n
 *)
  
End matrix.

(* algebraic_structure *)
Section algebraic_structure.
  Import Hierarchy.
  Context `{SGroup}. Infix "+" := Aadd.
  
  Goal forall a b c k, a = k -> (a + b) + c = k + (b + c).
  Proof. intros. sgroup. Qed.

  Context `{HASGroup : ASGroup A Aadd}.
  Goal forall a0 a1 a2 a3, a0 + (a1 + a2) + a3 = a3 + (a0 + a2) + a1.
  Proof. intros. asgroup. Qed.
End algebraic_structure.

Module compare_mathcomp.
  From mathcomp Require Import matrix fintype.

  (* 测试表达式求值 *)
  (* Variable A : Type. *)
  (* Variable  *)
  Let M : 'M_(2,3) := @const_mx nat 2 3 2.

  (* 转置 *)
  Open Scope ring_scope.
  Check M^T.

  (* 难以求值 *)
  Goal M ord0 ord0 = 2.
    cbv.
    destruct const_mx_key.
    simpl.
    Abort.

  

  (* 测试代码抽取，以矩阵加法为例 *)
  (* Recursive Extraction addmx. *)
  (* 
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module Finite =
  type sort = __
 end

type ordinal = int

type 'rT finfun_on =
| Finfun_nil
| Finfun_cons of Finite.sort * Finite.sort list * 'rT * 'rT finfun_on

type 'rT finfun_of = 'rT finfun_on

type 'r matrix = 'r finfun_of

let mx_val _ _ a =
  a

let matrix_of_fun m n k =
  locked_with k (matrix_of_fun_def m n)

let fun_of_matrix m n a i j =
  fun_of_fin (prod_finType (ordinal_finType m) (ordinal_finType n)) (mx_val m n a) (Obj.magic (i, j))

let map2_mx f m n a b =
  matrix_of_fun m n map2_mx_key (fun i j ->
    f (fun_of_matrix m n a (Obj.magic i) (Obj.magic j)) (fun_of_matrix m n b (Obj.magic i) (Obj.magic j)))

let addmx v m n =
  map2_mx (GRing.add v) m n
 *)
End compare_mathcomp.


(* Gauss Elimination *)
Section GE.
  Import MatrixQc.

  Let A : smat 3 := l2m (Q2Qc_dlist [[0;-2;1];[3;0;-2];[-2;3;0]]%Q).

  (* {1,2}, P1=[[0;1;0];[1;0;0];[0;0;1]], Q1=[[0;1;0];[1;0;0];[0;0;1]] *)
  Let ro1 : @RowOp Qc 2 := ROswap #0 #1.
  Let P1 : smat 3 := rowOps2mat [ro1].
  Let Q1 : smat 3 := rowOps2matInv [ro1].
  Compute m2l P1. Compute m2l (P1*A). Compute m2l Q1.
  Compute m2l (P1 * Q1).

  (* (1/3)*{1}, P2=[[1/3;0;0];[0;1;0];[0;0;1]], Q2=[[3;0;0];[0;1;0];[0;0;1] *)
  Let ro2 : @RowOp Qc 2 := ROscale #0 (Q2Qc (1/3)).
  Let P2 : smat 3 := rowOps2mat [ro2].
  Let Q2 : smat 3 := rowOps2matInv [ro2].
  Compute m2l P2. Compute m2l (P2*P1*A). Compute m2l Q2.
  Compute m2l (P2 * Q2).

  (* {3}+(2)*{1}, P3=[[1;0;0];[0;1;0];[2;0;1]], Q3=[[1;0;0];[0;1;0];[-2;0;1]] *)
  Let ro3 : @RowOp Qc 2 := ROadd #2 #0 (Q2Qc 2).
  Let P3 : smat 3 := rowOps2mat [ro3].
  Let Q3 : smat 3 := rowOps2matInv [ro3].
  Compute m2l P3. Compute m2l (P3*P2*P1*A). Compute m2l Q3.
  Compute m2l (P3 * Q3).

  (* (-1/2)*{2}, P4=[[1;0;0];[0;-1/2;0];[0;0;1]], Q4=[[1;0;0];[0;-2;0];[0;0;1]] *)
  Let ro4 : @RowOp Qc 2 := @ROscale _ 2 #1 (Q2Qc (-1/2)).
  Let P4 : smat 3 := rowOps2mat [ro4].
  Let Q4 : smat 3 := rowOps2matInv [ro4].
  Compute m2l P4. Compute m2l (P4*P3*P2*P1*A). Compute m2l Q4.

  (* {3}+(-3)*{2}, P5=[[1;0;0];[0;1;0];[0;-3;1]], Q5=[[1;0;0];[0;1;0];[0;3;1]] *)
  Let ro5 : @RowOp Qc 2 := @ROadd _ 2 #2 #1 (Q2Qc (-3)).
  Let P5 : smat 3 := rowOps2mat [ro5].
  Let Q5 : smat 3 := rowOps2matInv [ro5].
  Compute m2l P5. Compute m2l (P5*P4*P3*P2*P1*A). Compute m2l Q5.

  (* 6*{3}, P6=[[1;0;0];[0;1;0];[0;0;6]], Q7=[[1;0;0];[0;1;0];[0;0;1/6]] *)
  Let ro6 : @RowOp Qc 2 := @ROscale _ 2 #2 (Q2Qc 6).
  Let P6 : smat 3 := rowOps2mat [ro6].
  Let Q6 : smat 3 := rowOps2matInv [ro6].
  Compute m2l P6. Compute m2l (P6*P5*P4*P3*P2*P1*A). Compute m2l Q6.

  (* {2}+(1/2)*{3}, P7=[[1;0;0];[0;1;1/2];[0;0;1]], Q7=[[1;0;0];[0;1;-1/2];[0;0;1]] *)
  Let ro7 : @RowOp Qc 2 := @ROadd _ 2 #1 #2 (Q2Qc (1/2)).
  Let P7 : smat 3 := rowOps2mat [ro7].
  Let Q7 : smat 3 := rowOps2matInv [ro7].
  Compute m2l P7. Compute m2l (P7*P6*P5*P4*P3*P2*P1*A). Compute m2l Q7.

  (* {1}+(2/3)*{3}, P8=[[1;0;2/3];[0;1;0];[0;0;1]], Q8=[[1;0;-2/3];[0;1;0];[0;0;1]] *)
  Let ro8 : @RowOp Qc 2 := @ROadd _ 2 #0 #2 (Q2Qc (2/3)).
  Let P8 : smat 3 := rowOps2mat [ro8].
  Let Q8 : smat 3 := rowOps2matInv [ro8].
  Compute m2l P8. Compute m2l (P8*P7*P6*P5*P4*P3*P2*P1*A). Compute m2l Q8.

  Let P := P8*P7*P6*P5*P4*P3*P2*P1.
  Let Q := Q1*Q2*Q3*Q4*Q5*Q6*Q7*Q8.
  Compute m2l P.
  Compute m2l Q.
  
  Lemma eq1 : P * A = mat1.
  Proof. Admitted.

  Lemma eq2 : A = Q * mat1.
  (* Proof. meq. Qed. *)
  Proof. Admitted.

  Goal minvtble A.
  Proof.
    hnf. exists P. split. apply eq1.
    (* 要证明 A * P = mat1，
       转化为 Q * mat1 * P = mat1，
       转化为 Q * P = mat1。 *)
    rewrite eq2. rewrite mmul_1_r.
    unfold P,Q.
    unfold P1,P2,P3,P4,P5,P6,P7,P8.
    unfold Q1,Q2,Q3,Q4,Q5,Q6,Q7,Q8.
    rewrite <- !rowOps2matInv_app.
    rewrite !mmul_assoc.
    rewrite <- !rowOps2mat_app.
    rewrite mmul_rowOps2matInv_rowOps2mat_eq1. auto.
    repeat constructor; hnf; try easy.
  Qed.
  
End GE.
