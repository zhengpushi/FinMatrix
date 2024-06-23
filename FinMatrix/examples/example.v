(* 
   purpose  : example usage for FinMatrix
   author   : Zhengpu Shi
   date     : 2024.04.26
 *)

From FinMatrix Require MatrixNat MatrixZ MatrixQc MatrixR MatrixC.

(* Vector over monoid $\langle \mathbb{N},+,0\rangle$ *)
Section vec_monoid_nat.
  Import MatrixNat.
  Open Scope vec_scope.

  (* Create vector by a list *)
  Let a : vec 5 := l2v [1;2;3;4;5;6;7].
  Compute v2l a.  (* = [1; 2; 3; 4; 5] : list A *)

  (* Create matrix by a nat-indexing-function *)
  Let b : vec 5 := f2v (fun i => match i with 1 => 3 | _ => 0 end).
  Compute v2l b.  (* = [0; 3; 0; 0; 0] *)

  (* Get element, there are two notations with different convention *)

  (* #1 is second element, index-start-at-0, computer convention *)
  Compute a.[#1].  (* = 2 *) 

  (* .2 is second element, index-start-at-1, mathematical convention *)
  Compute a.2.      (* = 2 *) 

  (* vector addition *)
  Compute v2l (a + b).   (* = [1; 5; 3; 4; 5] : list A *)

  (* sum of a vector *)
  Compute vsum a.  (* = 15 *)
End vec_monoid_nat.

(* Conversion between $\mathtf{vec,cvec,rvec}$ *)
Section vec_cvec_rvec.
  Import MatrixNat.
  Open Scope vec_scope.

  (* Create vector, column vector(matrix), row vector(matrix) *)
  Let a : vec 3 := l2v [1;2;3].
  Let b : cvec 3 := l2m [[4];[5];[6]].
  Let c : rvec 3 := l2m [[7;8;9]].

  (* vector <-> column vector *)
  Check v2cv a.  (* v2cv a : cvec 3 *)
  Check cv2v b.  (* cv2v b : vec 3 *)
  
  (* vector <-> row vector *)
  Check v2rv a.  (* v2rv a : rvec 3 *)
  Check rv2v c.  (* rv2v c : vec 3 *)
End vec_cvec_rvec.

(* Matrix over monoid $\langle \mathbb{N},+,0\rangle$ *)
Section mat_monoid_nat.
  Import MatrixNat.
  Open Scope mat_scope.

  (* Create matrix by a list *)
  Let M : mat 2 3 := l2m [[1;2;3];[4]].
  Compute m2l M. (* = [[1; 2; 3]; [4; 0; 0]] : dlist A *)

  (* Create matrix by a nat-indexing-function *)
  Let N : mat 3 3 := f2m (fun i j => if (i ??= j) then 1 else 0).
  Compute m2l N.  (* = [[1; 0; 0]; [0; 1; 0]; [0; 0; 1]] : dlist A *)

  (* Get element *)
  Compute M.[#0].[#1].  (* = 2 : A *)    Compute M.1.2.  (* = 2 : A *)

  (* Matrix addition *)
  Compute m2l (N + N).  (* = [[2; 0; 0]; [0; 2; 0]; [0; 0; 2]] : dlist A *)

  (* Matrix transpose *)
  Compute m2l (M\T).   (* = [[1; 4]; [2; 0]; [3; 0]] : dlist A *)

  (* Create a diagonal matrix *)
  Compute m2l (mdiagMk (@l2v 3 [1;2;3])).
  (* = [[1; 0; 0]; [0; 2; 0]; [0; 0; 3]] : dlist A *)
  
End mat_monoid_nat.

(* Vector over ring $\langle \mathbb{Z},+,0,-x,*,1\rangle$ *)
Section vec_ring_Z.
  Import MatrixZ.  Open Scope vec_scope.
  Let u := @l2v 3 [1;2;-3].  (*  u = [1; 2; -3] *)
  Let v := @f2v 3 (fun i => -1 + nat2Z i)%Z. (* v = [-1; 0; 1] *)

  (* Vector negation *)
  Compute v2l (- u).         (* = [-1; -2; 3] *)
  (* Vector subtraction *)
  Compute v2l (u - v).       (* = [2; 2; -4] *)
  (* Vector scalar multiplication *)
  Compute v2l (5 \.* u).     (* = [5; 10; -15] *)
  (* Vector dot product *)
  Compute <u, v>.            (* = -4 *)
  (* Sum of a vector *)
  Compute vsum u.            (* = 0 *)

  (* Predicate: A vector is a unit vector. 
     Defined as: the dot product with itself is 1 *)
  Check vunit u.             (* : Prop  *)
  Print Vector.vunit.        (* forall a : vec n, <a, a> = 1 *)
  
  (* Predicate: Two vectors are orthogonal (also called perpendicular in two 
     and three dimensions). 
     Defined as: dot product is 0 *)
  Check u _|_ v.             (* : Prop  *)
  Print Vector.vorth.        (* forall a b : vec n, <a, b> = 0 *)


  (* <Vector addition, zero vector, vector negation> forms a commutative 
     group, which can be used to help proof by group theory. See vsub_xx *)
  Check vadd_AGroup.   (* : forall n : nat, AGroup vadd vzero vopp *)
End vec_ring_Z.

(* Matrix over ring $\langle \mathbb{Z},+,0,-x,*,1\rangle$ *)
Section mat_ring_Z.
  Import MatrixZ.  Open Scope mat_scope.
  Let M := @l2m 3 3 [[1;2;3];[4;5;6];[7;8;9]].
  Let N := @l2m 3 3 [[1;4;5];[2;3;8];[9;7;6]].
  Let a := @l2v 3 [1;2;3].

  (* Matrix negation *)
  Compute m2l (- M).     (* = [[-1; -2; -3]; [-4; -5; -6]; [-7; -8; -9]] *)
  (* Matrix subtraction *)
  Compute m2l (M - N).   (* = [[0; -2; -2]; [2; 2; -2]; [-2; 1; 3]] *)
  (* Matrix scalar multiplication *)
  Compute m2l (5 \.* M). (* = [[5; 10; 15]; [20; 25; 30]; [35; 40; 45]] *)
  (* Matrix multiplication *)
  Compute m2l (M * N).   (* = [[32; 31; 39]; [68; 73; 96]; [104; 115; 153]] *)
  (* Matrix multiplied by vector (vector is first converted to column matrix) *)
  Compute v2l (M *v a).  (* = [14; 32; 50] : list A *)
  (* Vector multiplied by matrix (vector is first converted to row matrix) *)
  Compute v2l (a v* M).  (* = [30; 36; 42] : list A *)

  (* traces of the square array *)
  Compute mtrace M.  (* = 15 *)     Compute tr M.
  (* Determinant of square matrix *)
  Compute mdet N.    (* = 137 *)    Compute |N|.
  (* Adjoint matrix of square matrix *)
  Compute m2l (madj M).   (* = [[-3; 6; -3]; [6; -12; 6]; [-3; 6; -3]] *)

  (* Predicate: A square matrix is ​​invertible. 
     Defined as: exists M' such that M'*M=I and M*M'=I *)
  Check minvtble M.
  Print MatrixInvBase.minvtble. (* forall M, exists M', M * M' = I /\ M' * M = I *)

  (* Predicate: A square matrix is ​​singular. 
     Defined as: not invertible *)
  Check msingular M.

  (* <Matrix addition, zero matrix, matrix negation> forms a commutative group, 
     which can be used to help proof by group theory *)
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
  (* In the earlier version, the vector length was only defined over the real 
     number. But now it is extended to any metric space. For example, over Qc *)

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
  
  (* The vector on Qc can define the metric space, and the metric function is a2r *)
  Search a2r.
  Print Hierarchy.A2R.
End vec_Qc.


(* Matrix over field $\langle \mathbb{R},+,0,-x,*,1,/x\rangle$ *)
Section mat_field_R.
  Import MatrixR. Open Scope mat_scope.

  (** Applications of matrices in geometry *)
  
  (* Predicate: A matrix is ​​orthogonal *)
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

  (** Applications of matrices in algebra, such as using inverse
      matrices to solve equations *)
  
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

(* Some important mathematical properties *)
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

(* Example of solving equations*)
Section solve_equation.
  Import MatrixQc.  Open Scope Q_scope.
  Let C := [[6;0;1];[0;4;1];[-3;-2;1]].  Let b := [4;0;2].

  (* Method 1: cramer rule *)
  Compute cramerRuleListQ 3 C b. (* = [1 # 3; -1 # 2; 2] : list Q *)
  
  (* Method 2: $X = C^{-1} b$ *)
  Compute solveEqListQ 3 C b.  (* = [1 # 3; -1 # 2; 2] : list Q *)

  (* Actually, there are two methods inside method 2, GE and AM, and GE
     is used by default *)
  Compute solveEqListGEQ 3 C b.
  Compute solveEqListAMQ 3 C b.
End solve_equation.

(* The difference between Eval cbv and Compute in Qc type *)
Section cbv_Compute.
  
  (* NOTE:
       Eval cbv in xx
       Compute xx
     These two evaluation has different speed.
     1. If both are constants, both are fast.
        `Compute xx` is abbreviation of `Eval vm_compute in xx`,
        It is compiled to bytecode and then run.
     2. If Variable is included, both will be slow or even stuck.  
        But if I set some operations to Opaque, `Eval cbv in xx` works, but
        `Compute xx` still gets stuck.  
        And, `Compute xx` will unfold them, regardless of whether the `Opaque` option 
        is set or not *)
  Import MatrixQc.
  
  (* Evaluates expression formed by constants *)
  Section ex1.
    Let M : smat 2 := @l2m 2 2 (Q2Qc_dlist [[1;2];[3;4]]%Q).
    
    (* Compute |M|. *)
    (* = {| this := -2; canon := Qred_involutive (-2) |} *)

    (* Eval cbv in |M|. *)
    (* = {| this := -2; canon := Qred_involutive (-2) |} *)

    (* If `Opaque xx` directives are executed, then:
       `Compute xx` will still unfold them;
       `Eval cbv xx` will respect these directives *)
    Opaque Qcplus Qcopp Qcmult Q2Qc.

    (* Compute |M|. *)
    (* = {| this := -2; canon := Qred_involutive (-2) |} *)
    
    (* Eval cbv in |M|. *)
    (* = (Q2Qc 0 + 1 * (Q2Qc 4 * 1) + - (Q2Qc 2 * (Q2Qc 3 * 1)))%Qc *)
  End ex1.

(* Evaluates expression containing variables *)
  Section ex2.
    Variable q11 : Q.
    Let M : smat 2 := @l2m 2 2 (Q2Qc_dlist [[q11;2];[3;4]]%Q).
    
    (* Direct calculation will basically get stuck *)
    (* Compute |M|. *)
    (* Eval cbv in |M|. *)

    (* After executing the Opaque command, `Eval cbv xx` can run well *)
    Opaque Qcplus Qcopp Qcmult Q2Qc.
    Eval cbv in |M|.
    (* = (Q2Qc 0 + Q2Qc q11 * (Q2Qc 4 * 1) + - (Q2Qc 2 * (Q2Qc 3 * 1)))%Qc *)
  End ex2.
End cbv_Compute.

(* Working with matrices using R types *)
Section solve_equation.
  Import MatrixR.
  
  (* Advantages: Can handle irrational numbers. Here, [6;0;1] is replaced by [6;0;PI] *)
  Let C := [[6;0;PI];[0;4;1];[-3;-2;1]].
  Let b := [4;0;2].

  (* Disadvantage: The calculation results are expanded too much and are not intuitive *)
  Compute cramerRuleList 3 C b.
  (* = [(((R1 + R1) * (R1 + R1) *
   ((R1 + R1) * (R1 + R1) * (R1 * R1 + R0) + (- R1 * (- (R1 + R1) * R1 + R0) + R0)) +
   (- R0 * (R0 * (R1 * R1 + R0) + (- R1 * ((R1 + R1) * R1 + R0) + R0)) +
   ... *)

  (* Another way: do it interactively and use field_simplify to get concise results *)
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

  (* It can be seen that the common denominator has not been eliminated
     in the fraction here, but it is already easier to read.  
     We can get the analytical solution:
     x1 = (-8 * PI + 24) / (12 * PI + 36);
     x2 = -24 / (12 * PI + 36)
     x3 = 96 / (12 * PI + 36)
   *)

  (* Similarly, we can use the solveEqList method, but it is best to use the 
     NoCheck version *)
  Compute solveEqListNoCheck 3 C b.

End solve_equation.

(* Verification of NA (nodal analysis) equations in SPICE system *)
Section SPICE.
  Import MatrixR.
  Variable n b : nat.             (* n nodes，b branches *)
  Variable A : mat n b.         (* association matrix *)
  Variable U : cvec b.          (* branch voltage *)
  Variable I : cvec b.          (* branch current *)
  Variable Is : cvec n.         (* injection current *)
  Variable Un : cvec n.         (* node voltage *)
  Variable G : smat b.          (* branch admittance matrix *)
  Definition Y := A * G * A\T.   (* nodal admittance matrix *)
  Hypotheses KCL : A * I = Is.   (* KCL law *)
  Hypotheses KVL : A\T * Un = U. (* KVL law *)
  Hypotheses H1 : G * U = I.     (* Constraint equation describing the branch 
                                    through admittance *)

  Lemma eq4 : G * A\T * Un = I.
  Proof. rewrite <- H1. rewrite <- KVL. rewrite mmul_assoc. auto. Qed.

  Lemma eq5 : A * G * A\T * Un = Is.
  Proof. rewrite <- KCL. rewrite !mmul_assoc, <- (mmul_assoc G), eq4. auto. Qed.

  Lemma eq6 : Y * Un = Is.
  Proof. unfold Y. rewrite eq5. auto. Qed.
End SPICE.

(* finite set *)
Module fin.
  Import Extraction.
  
  (* Our definition, which have refer to the notation of mathcomp.ordinal *)
  Module FinMatrix.
    Inductive fin (n : nat) := Fin (i : nat) (E : i < n).
    Notation "''I_' n" := (fin n)  (at level 8).
    Extraction fin.
  End FinMatrix.

  (* It is equivalent to using sig, but using Inductive avoids unnecessary 
     complexity caused by an overly polymorphic sig type *)
  Module by_sig.
    Definition fin (n : nat) := {i | i < n}.
  End by_sig.

  (* Another definition, use `unit` to represent `fin 0` *)
  Module by_MaYingYing.
    Definition fin (n : nat) := match n with O => unit |  _ => {i : nat | i < n} end.
    Extraction fin.
  End by_MaYingYing.

  (* Another choice, use an redundant index *)
  Module method3.
    Definition fin (n : nat) := {i | i <= n}.
    Extraction fin.
    (* Here:
         fin 0 = {0}
         fin 1 = {0,1}
         fin 2 = {0,1,2}
     *)
  End method3.

  (* Coq standard library *)
  Module CoqStdLib.
    Import Coq.Vectors.Fin.
    Print t.
    Inductive t : nat -> Set := F1 n : t (S n) | FS n (x : t n) : t (S n).
    Extraction t.
  End CoqStdLib.
End fin.

(* Polymorphic vector *)
Section vector.
  Import Vector.

  Print vec.
  Search vec.
  Locate ".[".
End vector.

(* Polymorphic matrix *)
Section matrix.
  Import Matrix.

  Print mat.

  Variable A : Type.  Variable r c : nat.
  Compute mat A r c. (* = 'I_r -> 'I_c -> A : Type *)

  Goal mat A r c = ('I_r -> 'I_c -> A).
  Proof. reflexivity. Qed.

  Definition mat_old := list (list A).
  
  Print mtrans.

  (* An example of tensor, there are no conversion burden between different types *)
  Variable M : @vec (@vec (@vec A 5) 4) 3. (* A 3*4*5-dimensional tensor over A *)
  Check M : @vec (@mat A 4 5) 3.           (* A 3-dimensional vector over `mat A 4 5` *)
  Check M : @mat (@vec A 5) 3 4.           (* A 3*4-dimensional matrix over `vec A 5` *)
End matrix.

(* Test code extraction, taking matrix addition as an example *)
Module matrix_ocaml_extraction.
  Import Matrix.
  Recursive Extraction madd.
(* type fin = int

   type 'a vec = fin -> 'a

   let vmap2 f _ a b i =

   let madd aadd r c m n =
       vmap2 (vmap2 aadd c) r m n
 *)
End matrix_ocaml_extraction.

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

  (* Test expression evaluation *)
  (* Variable A : Type. *)
  (* Variable  *)
  Let M : 'M_(2,3) := @const_mx nat 2 3 2.

  (* The expression "get the (0,0)th element of a 2*3 constant matrix"
     cannot be evaluated *)
  Goal M ord0 ord0 = 2.
    cbv.
    destruct const_mx_key.
    simpl.
    Abort.

  

  (** Test code extraction, taking matrix addition as an example.
      1. there are magic code.
      2. the implemention is too complex *)
  
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
    (* To prove A * P = mat1, 
       convert to Q * mat1 * P = mat1, 
       convert to Q * P = mat1. *)
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
