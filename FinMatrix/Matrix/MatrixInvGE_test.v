

Require Import MatrixInvGE QExt QcExt.


(* ############################################################################ *)
(** * Test *)

(* ******************************************************************* *)
(** ** Test inverse matrix on Qc *)

Module MinvGE_Qc := MinvGE FieldElementTypeQc.

Section test_Qc.
  Import MinvGE_Qc.

  Open Scope Q_scope.
  Open Scope Qc_scope.
  Open Scope mat_scope.
  
  (** Example 1: a `3x3` matrix *)
  Section ex1.

    (* [1 3 1]     [-1 -1  2] *)
(*        [2 1 1] <-> [ 0 -1  1] *)
(*        [2 2 1]     [ 2  4 -5] *)
    Let d1 := Q2Qc_dlist [[1;3;1];[2;1;1];[2;2;1]]%Q.
    Let d2 := Q2Qc_dlist [[-1;-1;2];[0;-1;1];[2;4;-5]]%Q.
    (* Note, we need the `Q2Qc` function to typing term of `Qc` type *)
    
    (* Compute minvtblebList 3 d1. *)
    (* Compute minvList 3 d1. *)
    (* Compute minvList 3 d2. *)

    Goal minvList 3 d1 = d2.
    Proof. cbv. list_eq; f_equal; apply proof_irrelevance. Qed.
    
    (* Note, the `canon` part is unnecessary for users.  *)
(*        But we can remove the proof part easily *)
    (* Compute Qc2Q_dlist (minvList 3 d1). *)
  End ex1.

  (* Using Qc type, in summary: *)
(*      1. the input need `Q2Qc` function *)
(*      2. the output has unnecessary proofs *)

  (* We can define more convenient functions with Q type *)
  Open Scope Q_scope.

  (** Check matrix invertibility with rational number lists *)
  Definition minvtblebListQ (n : nat) (d : dlist Q) : bool :=
    minvtblebList n (Q2Qc_dlist d).
  
  (** Inverse matrix with rational number lists *)
  Definition minvListQ (n : nat) (dl : dlist Q) : dlist Q :=
    Qc2Q_dlist (minvList n (Q2Qc_dlist dl)).
  
  (** Example 2: a `3x3` matrix *)
  Section ex2.

    (* [1 3 1]     [-1 -1  2] *)
(*        [2 1 1] <-> [ 0 -1  1] *)
(*        [2 2 1]     [ 2  4 -5] *)
    Let d1 := [[1;3;1];[2;1;1];[2;2;1]].
    Let d2 := [[-1;-1;2];[0;-1;1];[2;4;-5]].
    
    (* Compute minvtblebListQ 3 d1. *)
    (* Compute minvListQ 3 d1. *)
    (* Compute minvListQ 3 d2. *)
    (* Note, we get a friendly experience for typing and printing *)

    (* Meanwhile, the equality of the result with Q type also satisfy canonical form, *)
(*        that means we can use Leibniz equal instad of setoid equal `Qeq` *)
    Goal minvListQ 3 d1 = d2.
    Proof. cbv. auto. Qed.
  End ex2.

  (* Example 3: another matrix *)
  Section ex3.
    (* A manually given random matrix *)
    Let d1 :=
          [[1;2;3;4;5;6;7;8];
           [2;4;5;6;7;8;9;1];
           [3;5;7;6;8;4;2;1];
           [4;5;7;6;9;8;3;2];
           [5;4;3;7;9;6;8;1];
           [6;5;3;4;7;8;9;2];
           [7;8;6;5;9;2;1;3];
           [8;9;6;3;4;5;2;1]].
    (* Time Compute minvListQ 6 d1. (* 0.04 s *) *)
    (* Time Compute minvListQ 7 d1. (* 0.14 s *) *)
    (* Time Compute minvListQ 8 d1. (* 0.62 s *) *)
    (* Note that many elements are in the fraction format of rational numbers. *)
(*        This is reasonable, as fractions typically do not possess a finite decimal  *)
(*        representation. *)
    
    (* How to verify the inverse matrix in MATLAB ? *)
(*      (1) change the format of rational numbers between fractions and floating *)
(*          point numbers. *)
(*      >> format rat *)
(*      >> format short *)

(*      (2) inverse matrix of a 6x6 matrix *)
(*      >> M = [1 2 3 4 5 6; ... *)
(*              2 4 5 6 7 8; ... *)
(*              3 5 7 6 8 4; ... *)
(*              4 5 7 6 9 8; ... *)
(*              5 4 3 7 9 6; ... *)
(*              6 5 3 4 7 8] *)
(*      >> M1 = inv(M) *)
(*      Note that, the result is equal. *)

(*      (3) inverse matrix of a 8x8 matrix *)
(*      >> M = [1 2 3 4 5 6 7 8; ... *)
(*              2 4 5 6 7 8 9 1; ... *)
(*              3 5 7 6 8 4 2 1; ... *)
(*              4 5 7 6 9 8 3 2; ... *)
(*              5 4 3 7 9 6 8 1; ... *)
(*              6 5 3 4 7 8 9 2; ... *)
(*              7 8 6 5 9 2 1 3; ... *)
(*              8 9 6 3 4 5 2 1] *)
(*      >> M1 = inv(M)  *)
(*      Note that, the result is a bit different with in Coq. *)
(*      For example: *)
(*          in COQ,     M1(0,2)=41846/50943 = 0.8214278704 *)
(*          in MATLAB,  M1(0,2)=23/28       = 0.8214285714 *)
(*      *)

    Goal ~(Qmake 41846 50943 == Qmake 23 28).
    Proof.
      intro. cbv in H.          (* 1171688%Z = 1171689%Z *)
      easy.
    Qed.

    (* The possible reason is that MATLAB performs calculations using floating-point  *)
(*        numbers, and converting the inaccurate results into fractions cannot compensate *)
(*        for the difference. *)
(*        On the contrary, Coq uses completely precise results. *)
(*        While the exact benefits are unclear, this precision could be beneficial. *)
  End ex3.

  (* Example 4 : a `8x8` matrix with decimal numbers *)
  Section ex4.
  (* In MATLAB,  *)
(*      >> format short *)
(*      >> M = rand(8,8) *)
(*      Or, manually use these numbers: *)
(*      >> M = [0.8001  0.5797  0.0760  0.9448  0.3897  0.0598  0.7317  0.1835; ... *)
(*              0.4314  0.5499  0.2399  0.4909  0.2417  0.2348  0.6477  0.3685; ... *)
(*              0.9106  0.1450  0.1233  0.4893  0.4039  0.3532  0.4509  0.6256; ... *)
(*              0.1818  0.8530  0.1839  0.3377  0.0965  0.8212  0.5470  0.7802; ... *)
(*              0.2638  0.6221  0.2400  0.9001  0.1320  0.0154  0.2963  0.0811; ... *)
(*              0.1455  0.3510  0.4173  0.3692  0.9421  0.0430  0.7447  0.9294; ... *)
(*              0.1361  0.5132  0.0497  0.1112  0.9561  0.1690  0.1890  0.7757; ... *)
(*              0.8693  0.4018  0.9027  0.7803  0.5752  0.6491  0.6868  0.4868] *)
(*      Compute the inverse matrix *)
(*      >> M1 = inv(M) *)
(*    *)
    Let d1 :=
          [[0.8001;0.5797;0.0760;0.9448;0.3897;0.0598;0.7317;0.1835];
           [0.4314;0.5499;0.2399;0.4909;0.2417;0.2348;0.6477;0.3685];
           [0.9106;0.1450;0.1233;0.4893;0.4039;0.3532;0.4509;0.6256];
           [0.1818;0.8530;0.1839;0.3377;0.0965;0.8212;0.5470;0.7802];
           [0.2638;0.6221;0.2400;0.9001;0.1320;0.0154;0.2963;0.0811];
           [0.1455;0.3510;0.4173;0.3692;0.9421;0.0430;0.7447;0.9294];
           [0.1361;0.5132;0.0497;0.1112;0.9561;0.1690;0.1890;0.7757];
           [0.8693;0.4018;0.9027;0.7803;0.5752;0.6491;0.6868;0.4868]].

    (* Time Compute minvtblebListQ 8 d1. (* 0.15s *) *)
    (* Time Compute minvListQ 5 d1. (* 0.34 *) *)
    (* Time Compute minvListQ 6 d1. (* 1.28 *) *)
    (* Time Compute minvListQ 7 d1. (* 4.8 *) *)
    (* Time Compute minvListQ 8 d1. (* 20.5 *) *)
  End ex4.
  
  (* In summary, for computing inverse matrices with listQ: *)
(*      1. simple input format, and relatively simple output format. *)
(*      2. more accuately result compared to MATLAB, but fractions are not intuitive. *)
(*      3. Leibniz equal is supported. *)
(*    *)
End test_Qc.


(* ======================================================================= *)
(** usage for GE over Qc type *)
Module usage_GE_Qc.
  Module Import GE := MinvGE FieldElementTypeQc.
  Import GE.

  (* Example 1: evaluate inverse matrix *)
  Section ex1.
  (* [1 3 1]   [-1 -1  2]   [1 0 0] *)
(*      [2 1 1] * [ 0 -1  1] = [0 1 0] *)
(*      [2 2 1]   [ 2  4 -5]   [0 0 1] *)
    Let M : smat _ 3 := l2m 0 (Q2Qc_dlist [[1;3;1];[2;1;1];[2;2;1]]%Q).
    Let N : smat _ 3 := l2m 0 (Q2Qc_dlist [[-1;-1;2];[0;-1;1];[2;4;-5]]%Q).

    (* Compute m2l (M\-1). *)
    (* Compute m2l (N\-1). *)
  End ex1.

  (* Example 2: solve equation *)
  Section ex2.
    (* Given an equation [C * x = b] as following: *)
(*        1 * x + 2 * y = 5 *)
(*        3 * x + 4 * y = 6 *)
    Let C : smat _ 2 := l2m 0 (Q2Qc_dlist [[1;2];[3;4]]%Q).
    Let b : vec 2 := l2v 0 (Q2Qc_list [5;6]%Q).
    
    (* solve equation by inverse matrix *)
    (* Compute v2l (solveEq C b). *)
  End ex2.
End usage_GE_Qc.


(* ======================================================================= *)
(** usage for GE over Q type *)
Module usage_GE_Q.
  Module GE := MinvGE FieldElementTypeQc.
  Import GE.

  (* Support matrix inversion over Q type *)
  Section inv_Q.
    (** Inverse matrix over rational number *)
    Definition minv {n} (M : mat Q n n) : mat Qc n n :=
      let M : mat Qc n n := mmap Q2Qc M in
      mmap Qc2Q M.
    
    (** Inverse matrix with list over rational number *)
    Definition minvList (n : nat) (dl : dlist Q) : dlist Q :=
      Qc2Q_dlist (minvList n (Q2Qc_dlist dl)).

    (** use inverse matrix to solve equation [C * x = b] with Q list type *)
    Definition solveEq (n : nat) (C : dlist Q) (b : list Q) : list Q :=
      let C' : smat _ n := l2m 0 (Q2Qc_dlist C) in
      let b' : vec n := l2v 0 (Q2Qc_list b) in
      let x' : vec n := solveEq C' b' in
      Qc2Q_list (v2l x').
  End inv_Q.

  (* Now, we can use Q scope *)
  Open Scope Q_scope.
  
  (* Example 1: evaluate inverse matrix *)
  Section ex1.
  End ex1.

  (* Example 2: solve equation *)
  Section ex2.
    (* Given an equation [C * x = b] as following: *)
(*        1 * x + 2 * y = 5 *)
(*        3 * x + 4 * y = 6 *)
    Let C := [[1;2];[3;4]].
    Let b := [5;6].
    
    (* solve equation by inverse matrix *)
    (* Compute solveEq 2 C b. *)
  End ex2.

  (* Example 2: solve equation (bigger) *)
  Section ex3.
    (* Given an equation [C * x = b]: *)
    Let C := [[1;2;3;4;5];
              [2;4;3;5;1];
              [3;1;5;2;4];
              [4;5;2;3;1];
              [5;4;1;2;3]].
    Let b := [1;2;3;5;4].
    
    (* solve equation by inverse matrix *)
    (* Compute solveEq 5 C b. *)
  End ex3.

  (* Example 4: performance test *)
  Section ex4.
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
  (* Performance of minvList in Coq: *)
(*        dim    AM-time(s)  GE-time(s) *)
(*        5      0.394       0.375 *)
(*        6      1.2         1.298 *)
(*        7      7.9         5.268 *)
    (* Time Compute minvList 7 M. *)

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
  (* Performance of minvList in Coq: *)
(*        dim    AM-dig4(s)  AM-dig2(s)  GE-dig4(s)  GE-dig2 *)
(*        5      0.394       0.11        0.375       0.12 *)
(*        6      1.2         0.42        1.298       0.37 *)
(*        7      7.9         2.87        5.268       1.335 *)
    (* Time Compute minvList 7 M1. *)
  End ex4.
End usage_GE_Q.
