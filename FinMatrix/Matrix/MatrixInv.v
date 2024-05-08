(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Inverse Matrix
  author    : ZhengPu Shi
  date      : 2023.12

  remark    :
  1. 有多种逆矩阵计算方法
     (1) minvGE: 基于高斯消元(Gauss Elimination)的逆矩阵。
         适合于数值计算，不可符号计算。
         适用于 r*c 的任意形状的矩阵，所以可以计算左逆和右逆。
         不过目前只支持了 n*n 方阵的情形。
     (2) minvAM: 基于伴随矩阵(Adjoint)的逆矩阵。
         适合于符号计算，也可数值计算(但可能效率较低)。
         仅适用于 n*n 的方阵。
  2. 在Coq中计算的不同方式及其速度比较
     (1) 直接查看结果，不保存
         Eval cbn/cbv/compute in exp. 速度慢
         Eval vm_compute/native_compute in exp. 速度快
         Compute exp.  速度快
     (2) 不查看结果，而是保存到一个标识符。
         Let a := Eval cbn/cbv/compute in exp. 速度慢
         Let a := Eval vm_compute/native_compute in exp. 速度快
     (3) 原因：
         Compute xx 是 Eval vm_compute in xx 的缩写。
         vm_compute 是基于字节码的虚拟机执行
         native_compute 默认是 vm_compute，还可以进一步定制
 *)


Require Export MatrixInvAM.
Require Export MatrixInvGE.


Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv.


(* ############################################################################ *)
(** * Usage examples for matrix inversion *)

(* ======================================================================= *)
(** usage for AM over Qc type *)
Module usage_AM_Qc.
  Module AM := MinvAM FieldElementTypeQc.
  Import AM.

  (* Example 1: evaluate inverse matrix *)
  Section ex1.
  (* [1 3 1]   [-1 -1  2]   [1 0 0]
     [2 1 1] * [ 0 -1  1] = [0 1 0]
     [2 2 1]   [ 2  4 -5]   [0 0 1] *)
    Let M : smat _ 3 := l2m 0 (Q2Qc_dlist [[1;3;1];[2;1;1];[2;2;1]]%Q).
    Let N : smat _ 3 := l2m 0 (Q2Qc_dlist [[-1;-1;2];[0;-1;1];[2;4;-5]]%Q).

    (* Compute m2l (M\-1). *)
    (* Compute m2l (N\-1). *)
  End ex1.

  (* Example 2: solve equation *)
  Section ex2.
    (* Given an equation [C * x = b] as following:
       1 * x + 2 * y = 5
       3 * x + 4 * y = 6 *)
    Let C : smat _ 2 := l2m 0 (Q2Qc_dlist [[1;2];[3;4]]%Q).
    Let b : vec 2 := l2v 0 (Q2Qc_list [5;6]%Q).
    
    (* solve equation by cramer-rule *)
    (* Compute v2l (cramerRule C b). *)
    
    (* solve equation by inverse matrix *)
    (* Compute v2l (solveEq C b). *)
  End ex2.
End usage_AM_Qc.

(* ======================================================================= *)
(** usage for GE over Qc type *)
Module usage_GE_Qc.
  Module Import GE := MinvGE FieldElementTypeQc.
  Import GE.

  (* Example 1: evaluate inverse matrix *)
  Section ex1.
  (* [1 3 1]   [-1 -1  2]   [1 0 0]
     [2 1 1] * [ 0 -1  1] = [0 1 0]
     [2 2 1]   [ 2  4 -5]   [0 0 1] *)
    Let M : smat _ 3 := l2m 0 (Q2Qc_dlist [[1;3;1];[2;1;1];[2;2;1]]%Q).
    Let N : smat _ 3 := l2m 0 (Q2Qc_dlist [[-1;-1;2];[0;-1;1];[2;4;-5]]%Q).

    (* Compute m2l (M\-1). *)
    (* Compute m2l (N\-1). *)
  End ex1.

  (* Example 2: solve equation *)
  Section ex2.
    (* Given an equation [C * x = b] as following:
       1 * x + 2 * y = 5
       3 * x + 4 * y = 6 *)
    Let C : smat _ 2 := l2m 0 (Q2Qc_dlist [[1;2];[3;4]]%Q).
    Let b : vec 2 := l2v 0 (Q2Qc_list [5;6]%Q).
    
    (* solve equation by inverse matrix *)
    (* Compute v2l (solveEq C b). *)
  End ex2.
End usage_GE_Qc.

(* ======================================================================= *)
(** usage for AM over Q type *)
Module usage_AM_Q.
  Module AM := MinvAM FieldElementTypeQc.
  Import AM.

  (* Support matrix inversion over Q type *)
  Section inv_Q.
    (** Inverse matrix over rational number *)
    Definition minv {n} (M : mat Q n n) : mat Qc n n :=
      let M : mat Qc n n := mmap Q2Qc M in
      mmap Qc2Q M.
    
    (** Inverse matrix with list over rational number *)
    Definition minvList (n : nat) (dl : dlist Q) : dlist Q :=
      Qc2Q_dlist (minvList n (Q2Qc_dlist dl)).

    (** use cramerRule to solve equation [C * x = b] with Q list type *)
    Definition cramerRule (n : nat) (C : dlist Q) (b : list Q) : list Q :=
      let C' : smat _ n := l2m 0 (Q2Qc_dlist C) in
      let b' : vec n := l2v 0 (Q2Qc_list b) in
      let x' : vec n := cramerRule C' b' in
      Qc2Q_list (v2l x').

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
  (* Example 1: evaluate inverse matrix *)
  Section ex1.
  (* [1 3 1]   [-1 -1  2]   [1 0 0]
     [2 1 1] * [ 0 -1  1] = [0 1 0]
     [2 2 1]   [ 2  4 -5]   [0 0 1] *)
    Let M := [[1;3;1];[2;1;1];[2;2;1]].
    Let N := [[-1;-1;2];[0;-1;1];[2;4;-5]].

    (* Compute minvList 3 M. *)
    (* Compute minvList 3 N. *)
  End ex1.

  (* Example 2: solve equation *)
  Section ex2.
    (* Given an equation [C * x = b] as following:
       1 * x + 2 * y = 5
       3 * x + 4 * y = 6 *)
    Let C := [[1;2];[3;4]].
    Let b := [5;6].

    (* Solve equation by cramer-rule *)
    (* Compute cramerRule 2 C b. *)
    
    (* solve equation by inverse matrix *)
    (* Compute solveEq 2 C b. *)
  End ex2.

  (* Example 3: solve equation (bigger) *)
  Section ex3.
    (* Given an equation [C * x = b]: *)
    Let C := [[1;2;3;4;5];
              [2;4;3;5;1];
              [3;1;5;2;4];
              [4;5;2;3;1];
              [5;4;1;2;3]].
    Let b := [1;2;3;5;4].

    (* Solve equation by cramer-rule *)
    (* Compute cramerRule 5 C b. *)
    
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
  (* Performance of minvList in Coq:
       dim    time(s)
       5      0.394
       6      1.2
       7      7.9 *)
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
  (* Performance of minvList in Coq:
       dim    dig4-time(s)   dig2-time(s)
       5      0.394          0.11
       6      1.2            0.42
       7      7.9            2.87 *)
    (* Time Compute minvList 7 M1. *)
  End ex4.
  
End usage_AM_Q.

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
    (* Given an equation [C * x = b] as following:
       1 * x + 2 * y = 5
       3 * x + 4 * y = 6 *)
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
  (* Performance of minvList in Coq:
       dim    AM-time(s)  GE-time(s)
       5      0.394       0.375
       6      1.2         1.298
       7      7.9         5.268 *)
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
  (* Performance of minvList in Coq:
       dim    AM-dig4(s)  AM-dig2(s)  GE-dig4(s)  GE-dig2
       5      0.394       0.11        0.375       0.12
       6      1.2         0.42        1.298       0.37
       7      7.9         2.87        5.268       1.335 *)
    (* Time Compute minvList 7 M1. *)
  End ex4.
End usage_GE_Q.
