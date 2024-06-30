(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on Q.
  author    : Zhengpu Shi
  date      : 2023.12

  1. Enabling more matrix operations with the help of MatrixQc.
     * Motivation
       * Many useful operations are defined on algebraic structures with Leibniz equal,
         but Q type can't define these structures due to it only support Setoid equal.
       * Q is more friendly for typing and printing, then Qc type.
     * Solution
       We can use Qc type internally and use Q type as user-level. We will use the 
       conversion between Q and Qc to encapsulate the input and output, as follows:
       1. use Q2Qc to converting input data of Q type to Qc type
       2. execute the matrix operations with Qc type
       3. use Qc2Q to converting output data of Qc type to Q type.
     * In summary, for inverse matrices with Q (with the help of Qc):
       1. simple input format, and relatively simple output format.
       2. accuately result compared to MATLAB, but fractions are not intuitive.
       3. Leibniz equal is supported.
 *)

Require Export QcExt QExt.
Require Export MatrixModule.
Require MatrixQc.


(* ######################################################################### *)
(** * Matrix theory come from common implementations *)

Include (BasicMatrixTheory ElementTypeQ).

Open Scope Q_scope.
Open Scope vec_scope.
Open Scope mat_scope.


(* ######################################################################### *)
(** * Matrix theory applied to this type *)

(* TODO: instantiate all the modules *)


(** Conversion between vector of Q type and vector of Qc type *)
Definition vecQ2Qc {n} (v : @Vector.vec Q n) : @Vector.vec Qc n :=
  Vector.vmap Q2Qc v.
Definition vecQc2Q {n} (v : @Vector.vec Qc n) : @Vector.vec Q n :=
  Vector.vmap Qc2Q v.

Lemma vnth_vecQ2Qc : forall n (v : @Vector.vec Q n) (i : 'I_n),
    (vecQ2Qc v).[i] = Q2Qc v.[i].
Proof. intros. auto. Qed.

Lemma vnth_vecQc2Q : forall n (v : @Vector.vec Qc n) (i : 'I_n),
    (vecQc2Q v).[i] = Qc2Q v.[i].
Proof. intros. auto. Qed.


(** Conversion between matrix of Q type and matrix of Qc type *)
Definition matQ2Qc {r c} (A : @Matrix.mat Q r c) : @Matrix.mat Qc r c :=
  Matrix.mmap Q2Qc A.
Definition matQc2Q {r c} (A : @Matrix.mat Qc r c) : @Matrix.mat Q r c :=
  Matrix.mmap Qc2Q A.

Lemma vnth_matQ2Qc : forall r c (A : @Matrix.mat Q r c) i j,
    (matQ2Qc A).[i].[j] = Q2Qc A.[i].[j].
Proof. intros. auto. Qed.

Lemma vnth_matQc2Q : forall r c (A : @Matrix.mat Qc r c) i j,
    (matQc2Q A).[i].[j] = Qc2Q A.[i].[j].
Proof. intros. auto. Qed.

(* about "inversion" *)
Section inv.

  Import MatrixQc.

  (** Cramer rule over of Q type *)
  Definition cramerRuleQ {n} (A : Matrix.smat Q n) (b : @Vector.vec Q n)
    : @Vector.vec Q n := cramerRule (matQ2Qc A) (vecQ2Qc b).

  (** {cramerRuleQ lA lb} solves A*x=b *)
  Lemma cramerRuleQ_spec : forall n (A : Matrix.smat Q n) (b : @Vector.vec Q n),
      let x := cramerRuleQ A b in
      mdet (matQ2Qc A) <> 0 ->
      matQ2Qc A *v (vecQ2Qc x) = vecQ2Qc b.
  Proof.
    intros. unfold x. clear x.
    pose proof (cramerRule_spec (matQ2Qc A) (vecQ2Qc b) H). rewrite <- H0.
    f_equal. unfold cramerRuleQ. apply veq_iff_vnth; intros.
    unfold vecQ2Qc. auto_vec. rewrite <- Q2Qc_Qc2Q. f_equal.
  Qed.

  (** Cramer rule over list of Q type *)
  Definition cramerRuleListQ (n : nat) (lA : dlist Q) (lb : list Q) : list Q :=
    let lx_Qc := cramerRuleList n (dlistQ2Qc lA) (listQ2Qc lb) in
    listQc2Q lx_Qc.

  (** {cramerRuleListQ n lA lb} = cramerRuleList n {lA} {lb} *)
  Lemma cramerRuleListQ_spec : forall (n : nat) (lA : dlist Q) (lb : list Q),
      (* Solve equation by Qc *)
      let A : smat n := l2m (dlistQ2Qc lA) in
      let b : vec n := l2v (listQ2Qc lb) in
      let x : vec n := cramerRule A b in
      let lx : list Qc := v2l x in
      let lx_Q : list Q := listQc2Q lx in
      minvtble A -> cramerRuleListQ n lA lb = lx_Q.
  Proof.
    intros. unfold lx_Q, lx, x, A, b in *. clear lx_Q lx x A b.
    pose proof (cramerRuleList_spec n (dlistQ2Qc lA) (listQ2Qc lb)). simpl in H0.
    unfold cramerRuleListQ. rewrite <- H0. rewrite v2l_l2v. auto.
    apply cramerRuleList_length.
  Qed.


  (** Inverse matrix over Q matrix by GE *)
  Definition minvGEQ {n} (A : @Matrix.smat Q n) : @Matrix.smat Q n :=
    matQc2Q (minvGE (matQ2Qc A)).

  (** Inverse matrix over Q matrix by AM *)
  Definition minvAMQ {n} (A : @Matrix.smat Q n) : @Matrix.smat Q n :=
    matQc2Q (minvAM (matQ2Qc A)).

  (** Check matrix invertibility with Q lists as input by GE *)
  Definition minvtblebListGEQ (n : nat) (dl : dlist Q) : bool :=
    minvtblebListGE n (dlistQ2Qc dl).

  (** Inverse matrix with Q lists for input and output by GE *)
  Definition minvListGEQ (n : nat) (dl : dlist Q) : dlist Q :=
    dlistQc2Q (minvListGE n (dlistQ2Qc dl)).

  (** Check matrix invertibility with Q lists as input by AM *)
  Definition minvtblebListAMQ (n : nat) (dl : dlist Q) : bool :=
    minvtblebListAM n (dlistQ2Qc dl).

  (** Inverse matrix with Q lists for input and output by AM *)
  Definition minvListAMQ (n : nat) (dl : dlist Q) : dlist Q :=
    dlistQc2Q (minvListAM n (dlistQ2Qc dl)).
  

  (** Solve the equation with the form of A*x=b by GE over list of Q type. *)
  Definition solveEqListGEQ (n : nat) (lA : dlist Q) (lb : list Q) : list Q :=
    let lA' := dlistQ2Qc lA in
    let lb' := listQ2Qc lb in
    let lx' := solveEqListGE n lA' lb' in
    listQc2Q lx'.

  (** {solveEqListGEQ n lA lb} = solveEqListGE n {lA} {lb} *)
  Lemma solveEqListGEQ_spec : forall (n : nat) (lA : dlist Q) (lb : list Q),
      listQ2Qc (solveEqListGEQ n lA lb) = solveEqListGE n (dlistQ2Qc lA) (listQ2Qc lb).
  Proof. intros. unfold solveEqListGEQ. rewrite listQ2Qc_listQc2Q. auto. Qed.

  (** Solve the equation with the form of A*x=b by AM over list of Q type. *)
  Definition solveEqListAMQ (n : nat) (lA : dlist Q) (lb : list Q) : list Q :=
    let lA' := dlistQ2Qc lA in
    let lb' := listQ2Qc lb in
    let lx' := solveEqListAM n lA' lb' in
    listQc2Q lx'.

  (** {solveEqListAMQ n lA lb} = solveEqListAM n {lA} {lb} *)
  Lemma solveEqListAMQ_spec : forall (n : nat) (lA : dlist Q) (lb : list Q),
      listQ2Qc (solveEqListAMQ n lA lb) = solveEqListAM n (dlistQ2Qc lA) (listQ2Qc lb).
  Proof. intros. unfold solveEqListAMQ. rewrite listQ2Qc_listQc2Q. auto. Qed.

End inv.


(* ######################################################################### *)
(** * Usage demo *)
Section test.
  Open Scope vec_scope.

  (* Example 1: some test *)
  Section ex1.
    Let v1 := @l2v 3 [1;2;-3].
    (* Compute v2l v1. *)

    Let v2 := @f2v 3 (fun i => -1 + nat2Q i).
    (* Compute v2l v2. *)
    
    Let A := @l2m 3 3 [[1;-3;-2];[-2;1;-4];[-1;4;-1]].
    (* Compute m2l A. *)
  End ex1.
  
  (* Example 2: inverse matrix of a `3x3` matrix over Q type *)
  Section ex2.
  (* [1 3 1]   [-1 -1  2]   [1 0 0]
     [2 1 1] * [ 0 -1  1] = [0 1 0]
     [2 2 1]   [ 2  4 -5]   [0 0 1] *)
    Let d1 := [[1;3;1];[2;1;1];[2;2;1]].
    Let d2 := [[-1;-1;2];[0;-1;1];[2;4;-5]].

    (* Now, we can get a friendly experience for typing and printing *)
    (* Compute minvtblebListGEQ 3 d1. *)
    (* Compute minvtblebListAMQ 3 d1. *)
    (* Compute minvListAMQ 3 d1. *)
    (* Compute minvListGEQ 3 d1. *)

    (* Meanwhile, the equality of the result with Q type also satisfy canonical form,
       that means we can use Leibniz equal instad of setoid equal `Qeq` *)
    Goal minvListAMQ 3 d1 = d2.
    Proof. cbv. auto. Qed.

    (* But, note that the input data should be typing directly.
       For example, "1" is equivalent to "2/2" under `Qeq` relation,
       But, "1" is not equal to "2/2" under `eq` relation. *)
    Goal 1 == Qmake 2 2.
    Proof. cbv. auto. Qed.
    
    Goal 1 <> Qmake 2 2.
    Proof. cbv. intros. easy. Qed.

    (* Thus, if we give an equivalent matrix d2' respect to d2, such as: *)
    Let d2' : dlist Q := [[-1;-1;2];[0;-1;Qmake 2 2];[2;4;-5]].
    (* Here, the (2,3) element in d2' is different with d2, and the others are same.
        d2(2,3) = 1
        d2'(2,3) = Qmake 2 2 *)

    (* Now, this previous proof is False *)
    Goal minvListAMQ 3 d1 <> d2'.
    Proof. cbv. intro. inv H. Qed.

    (* But we can verify that they are setoid equal *)
    Infix "==" := (dlistSetoidEq Qeq).
    Goal minvListAMQ 3 d1 == d2.
    Proof. Local Opaque Qeq. cbv. repeat constructor. Qed.
    
  End ex2.

  (* Example 3: solve equation *)
  Section ex3.
    (* Given an equation [A * x = b] as following:
       1 * x + 2 * y = 5
       3 * x + 4 * y = 6 *)
    Let A := [[1;2];[3;4]].
    Let b := [5;6].

    (* Solve equation by cramer-rule *)
    (* Compute cramerRuleListQ 2 A b. *)
    
    (* solve equation by inverse matrix *)
    (* Compute solveEqListGEQ 2 A b. *)
    (* Compute solveEqListAMQ 2 A b. *)
  End ex3.

  (* Example 4: solve equation (bigger) *)
  Section ex4.
    (* Given an equation [A * x = b]: *)
    Let A := [[1;2;3;4;5];
              [2;4;3;5;1];
              [3;1;5;2;4];
              [4;5;2;3;1];
              [5;4;1;2;3]].
    Let b := [1;2;3;5;4].

    (* Compute cramerRuleListQ 5 A b. *)
    (* Compute solveEqListGEQ 5 A b. *)
    (* Compute solveEqListAMQ 5 A b. *)
  End ex4.

  (* Example 5: performance test with `8x8` matrix, and analysis the data-error *)
  Section ex5.
    (* A manually given random `8x8` matrix *)
    Let d1 : dlist Q :=
      [[1;2;3;4;5;6;7;8];
       [2;4;5;6;7;8;9;1];
       [3;5;7;6;8;4;2;1];
       [4;5;7;6;9;8;3;2];
       [5;4;3;7;9;6;8;1];
       [6;5;3;4;7;8;9;2];
       [7;8;6;5;9;2;1;3];
       [8;9;6;3;4;5;2;1]].

    (* Time Compute minvListAMQ 6 d1. (* 0.13s *) *)
    (* Time Compute minvListAMQ 7 d1. (* 1.2s *) *)
    (* Time Compute minvListAMQ 8 d1. (* 14s *) *)

    (* Time Compute minvListGEQ 6 d1. (* 0.04s *) *)
    (* Time Compute minvListGEQ 7 d1. (* 0.13s *) *)
    (* Time Compute minvListGEQ 8 d1. (* 0.61s *) *)
    
    (* Note many elements are in the fraction format of rational numbers.
       The fractions typically do not possess a finite decimal representation. *)
    
    (* How to verify the inverse matrix in MATLAB ? *)
    (*  (1) change the format of rational numbers between fractions and floating *)
    (*      point numbers. *)
    (*  >> format rat *)
    (*  >> format short *)

    (*  (2) inverse matrix of a 6x6 matrix *)
    (*  >> M = [1 2 3 4 5 6; ... *)
    (*          2 4 5 6 7 8; ... *)
    (*          3 5 7 6 8 4; ... *)
    (*          4 5 7 6 9 8; ... *)
    (*          5 4 3 7 9 6; ... *)
    (*          6 5 3 4 7 8] *)
    (*  >> M1 = inv(M) *)
    (*  Note that, the result is equal. *)

    (*  (3) inverse matrix of a 7x7 matrix *)
    (*  >> M = [1 2 3 4 5 6 7; ... *)
    (*          2 4 5 6 7 8 9; ... *)
    (*          3 5 7 6 8 4 2; ... *)
    (*          4 5 7 6 9 8 3; ... *)
    (*          5 4 3 7 9 6 8; ... *)
    (*          6 5 3 4 7 8 9; ... *)
    (*          7 8 6 5 9 2 1] *)
    (*  >> M1 = inv(M) *)
    (*  Note that, the result is equal. *)

    (*  (3) inverse matrix of a 8x8 matrix *)
    (*  >> M = [1 2 3 4 5 6 7 8; ... *)
    (*          2 4 5 6 7 8 9 1; ... *)
    (*          3 5 7 6 8 4 2 1; ... *)
    (*          4 5 7 6 9 8 3 2; ... *)
    (*          5 4 3 7 9 6 8 1; ... *)
    (*          6 5 3 4 7 8 9 2; ... *)
    (*          7 8 6 5 9 2 1 3; ... *)
    (*          8 9 6 3 4 5 2 1] *)
    (*  >> M1 = inv(M) *)
    (*  Note that, the result is a bit different with in Coq. *)
    (*  For example: *)
    (*      in COQ,     M1(1,3)=41846/50943 = 0.8214278704 *)
    (*      in MATLAB,  M1(1,3)=23/28       = 0.8214285714 *)

    (* We can get the (1,3) element quickly, instead of get all elements *)
    Let M : smat 8 := l2m d1.
    (* Time Compute (minvGEQ M).1.3.  (* = 41846 # 50943 : Q *) (* 0.099s *) *)
    (* Time Compute (minvAMQ M).1.3.  (* = 41846 # 50943 : Q *) (* 1.367s *) *)

    (* These two rational numbers are not equal even over Qeq  *)
    Goal ~(Qmake 41846 50943 == Qmake 23 28).
    Proof.
      intro. cbv in H.          (* 1171688%Z = 1171689%Z *)
      easy.
    Qed.
    
    (* The possible reason is that MATLAB performs calculations using floating-point
       numbers, and converting the inaccurate results into fractions cannot compensate
       for the difference.
       On the contrary, Coq uses completely precise results.
       While the exact benefits are unclear, this precision could be beneficial. *)
  End ex5.
  
  (* Example 6: performance test with decimal numbers *)
  Section ex6.
    (* create random data in MATLAB by command ">> rand(10,10)" *)
    Let M :=
          [[0.8147;0.1576;0.6557;0.7060;0.4387;0.2760;0.7513;0.8407;0.3517;0.0759];
           [0.9058;0.9706;0.0357;0.0318;0.3816;0.6797;0.2551;0.2543;0.8308;0.0540];
           [0.1270;0.9572;0.8491;0.2769;0.7655;0.6551;0.5060;0.8143;0.5853;0.5308];
           [0.9134;0.4854;0.9340;0.0462;0.7952;0.1626;0.6991;0.2435;0.5497;0.7792];
           [0.6324;0.8003;0.6787;0.0971;0.1869;0.1190;0.8909;0.9293;0.9172;0.9340];
           [0.0975;0.1419;0.7577;0.8235;0.4898;0.4984;0.9593;0.3500;0.2858;0.1299];
           [0.2785;0.4218;0.7431;0.6948;0.4456;0.9597;0.5472;0.1966;0.7572;0.5688];
           [0.5469;0.9157;0.3922;0.3171;0.6463;0.3404;0.1386;0.2511;0.7537;0.4694];
           [0.9575;0.7922;0.6555;0.9502;0.7094;0.5853;0.1493;0.6160;0.3804;0.0119];
           [0.9649;0.9595;0.1712;0.0344;0.7547;0.2238;0.2575;0.4733;0.5678;0.3371]].

    (* Performance of minvList{AM|GE}Q in Coq:
       dim    minvListAMQ(s)  minvListGEQ(s)
       5      0.34            0.34
       6      2.4             1.2
       7      26              5.1 *)
    (* Time Compute minvListAMQ 7 M. *)
    (* Time Compute minvListGEQ 7 M. *)

    (* Same data, but with only 2 decimal. Because constructive numbers have big cost *)
    Let M1 :=
          [[0.81;0.15;0.65;0.70;0.43;0.27;0.75;0.84;0.35;0.07];
           [0.90;0.97;0.03;0.03;0.38;0.67;0.25;0.25;0.83;0.05];
           [0.12;0.95;0.84;0.27;0.76;0.65;0.50;0.81;0.58;0.53];
           [0.91;0.48;0.93;0.04;0.79;0.16;0.69;0.24;0.54;0.77];
           [0.63;0.80;0.67;0.09;0.18;0.11;0.89;0.92;0.91;0.93];
           [0.09;0.14;0.75;0.82;0.48;0.49;0.95;0.35;0.28;0.12];
           [0.27;0.42;0.74;0.69;0.44;0.95;0.54;0.19;0.75;0.56];
           [0.54;0.91;0.39;0.31;0.64;0.34;0.13;0.25;0.75;0.46];
           [0.95;0.79;0.65;0.95;0.70;0.58;0.14;0.61;0.38;0.01];
           [0.96;0.95;0.17;0.03;0.75;0.22;0.25;0.47;0.56;0.33]].
  (* Performance of minvList{AM|GE}Q in Coq with 2-bit dicimal:
       dim    AM_dig4   AM_dig2   GE_dig4   GE_dig2
       5      0.34      0.13      0.34      0.13
       6      2.4       0.7       1.2       0.4
       7      26        7.3       5.1       1.4 *)
    (* Time Compute minvListAMQ 7 M1. *)
    (* Time Compute minvListGEQ 7 M1. *)
  End ex6.

End test.
