(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : test for matrix gauss elimination
  author    : Zhengpu Shi
  date      : 2023.12

  remark    :
 *)

Require Import MatrixGauss.
Require Import QcExt RExt.


(* getPivot *)
Section test.
  Open Scope nat_scope.
  
  Let M : smat nat 3 := l2m 0 [[1;0;0];[0;1;0];[0;0;1]].
  Notation getPivot := (@getPivot nat 0).
  
  (* Compute getPivot M 3 #0. *)
  (* Compute getPivot M 3 #1. *)
  (* Compute getPivot M 3 #2. *)
  (* Compute getPivot M 2 #0. *)
  (* Compute getPivot M 2 #1. *)
  (* Compute getPivot M 2 #2. *)
  (* Compute getPivot M 1 #0. *)
  (* Compute getPivot M 1 #1. *)
  (* Compute getPivot M 1 #2. *)
  (* Compute getPivot M 0 #0. *)
  (* Compute getPivot M 0 #1. *)
  (* Compute getPivot M 0 #2. *)
End test.


(* elimDown *)
Section test.
  Import QcExt.
  Notation elimDown := (@elimDown _ Qcplus 0 Qcopp Qcmult _).
  
  Let M : smat Qc 3 := l2m 0 (dlistQ2Qc [[1;2;3];[4;5;6];[7;8;9]]%Q).
  (* Compute m2l (snd (elimDown M 2 #0)). *)
End test.


(* toREF *)
Section test.

  Import QcExt.
  Notation getPivot := (getPivot (Azero:=0)).
  Notation toREF := (@toREF _ Qcplus 0 Qcopp Qcmult Qcinv _).
  Notation elimDown := (@elimDown _ Qcplus 0 Qcopp Qcmult _).
  Notation rowOps2mat := (@rowOps2mat _ Qcplus 0 Qcmult 1 _).
  Notation mmul := (@mmul _ Qcplus 0 Qcmult).
  Infix "*" := mmul : mat_scope.

  (* 行阶梯形 *)
  (*      [  0 -2  1]     [0    1/3  0]   [1 0 -2/3] *)
  (*      [  3  0 -2]  => [-1/2   0  0] * [0 1 -1/2] *)
  (*      [ -2  3  0]     [9      4  6]   [0 0    1] *)
  Let M : smat Qc 3 := l2m 0 (dlistQ2Qc [[0;-2;1];[3;0;-2];[-2;3;0]]%Q).
  Let M1 : smat Qc 3 := l2m 0 (dlistQ2Qc [[1;0;-2/3];[0;1;-1/2];[0;0;1]]%Q).
  Let E1 : smat Qc 3 := l2m 0 (dlistQ2Qc [[0;1/3;0];[-1/2;0;0];[9;4;6]]%Q).
  
  Goal match toREF M 3 with
       | Some (l1',M1') => m2l (rowOps2mat l1') = m2l E1
                          /\ m2l M1' = m2l M1
       | _ => False
       end.
  Proof.
    cbv; split; list_eq; f_equal; apply proof_irrelevance.
  Qed.

  (* E1 will transform M to M1 *)
  Goal (E1 * M)%M = M1.
  Proof. apply m2l_inj. cbv. list_eq; f_equal. Qed.

End test.


(* elimUp *)
Section test.

  Import QcExt.
  Notation elimUp := (@elimUp _ Qcplus 0 Qcopp Qcmult _).

  Let M : smat Qc 3 := l2m 0 (dlistQ2Qc [[1;2;3];[4;5;6];[7;8;1]]%Q).
  (* Compute m2l (snd (elimUp M 2 #2)). *)
End test.


Section test.
  Import QcExt.
  Open Scope mat_scope.

  Notation smat n := (smat Qc n).
  Notation mat1 := (@mat1 _ 0 1).
  Notation mmul := (@mmul _ Qcplus 0 Qcmult).
  Infix "*" := mmul : mat_scope.
  Notation toREF := (@toREF _ Qcplus 0 Qcopp Qcmult Qcinv).
  Notation toRREF := (@toRREF _ Qcplus 0 Qcopp Qcmult).
  Notation elimUp := (@elimUp _ Qcplus 0 Qcopp Qcmult).
  Notation rowOps2mat := (@rowOps2mat _ Qcplus 0 Qcmult 1).
  Notation rowOps2matInv := (@rowOps2matInv _ Qcplus 0 Qcopp Qcmult 1 Qcinv).
  
  (*
                                  [ 0 -2  1]
                                  [ 3  0 -2]                 M0
                                  [-2  3  0]

  toREF
                  [0    1/3  0]   [ 0 -2  1]   [1 0 -2/3]
                  [-1/2   0  0] * [ 3  0 -2] = [0 1 -1/2]    T1 * M0 = M1
                  [9      4  6]   [-2  3  0]   [0 0    1]

  toRREF
    [1  0  2/3]   [0    1/3  0]   [ 0 -2  1]   [1 0 0]
    [0  1  1/2] * [-1/2   0  0] * [ 3  0 -2] = [0 1 0]       T2 * T1 * M0 = M2
    [0  0    1]   [9      4  6]   [-2  3  0]   [0 0 1]

  inversion
                        [6 3 4]   [ 0 -2  1]   [1 0 0]
                        [4 2 3] * [ 3  0 -2] = [0 1 0]       N0 * M0 = I
                        [9 4 6]   [-2  3  0]   [0 0 1]
   *)

  (* initial matrix M0 *)
  Let M0 : smat 3 := l2m 0 (dlistQ2Qc [[0;-2;1];[3;0;-2];[-2;3;0]]%Q).
  (* N0 is inverse matrix of M0 *)
  Let N0 : smat 3 := l2m 0 (dlistQ2Qc [[6;3;4];[4;2;3];[9;4;6]]%Q).

  (* verify that M0 and N0 are mutually inverse *)
  Goal M0 * N0 = mat1. Proof. meq. Qed.
  Goal N0 * M0 = mat1. Proof. meq. Qed.
  
  (* the REF of M0 is M1 *)
  Let l1 := match toREF M0 3 with Some (l1,M1) => l1 | _ => [] end.
  Let T1 : smat 3 := rowOps2mat l1.
  Let M1 : smat 3 := match toREF M0 3 with Some (l1,M1) => M1 | _ => mat1 end.
  
  (* the RREF of M1 is M2 *)
  Let l2 := fst (toRREF M1 3).
  Let T2 : smat 3 := rowOps2mat l2.
  Let M2 : smat 3 := snd (toRREF M1 3).

  (* verify M2 is identity matrix *)
  Goal M2 = mat1. Proof. meq; f_equal; apply proof_irrelevance. Qed.

  (* verify that (T2*T1) is N0 (i.e., inversion of M0) *)
  Goal T2 * T1 = N0. Proof. meq; f_equal; apply proof_irrelevance. Qed.
  
  (* We can calculate inversion directly *)
  (* Compute m2l (T2 * T1). *)

  (* 我们还能得到以下结论：
     1. 根据 T1 * M0 = M1 得到 M0 = T1\-1 * M1
     2. 根据 T2 * M1 = E  得到 M1 = T2\-1
     3. 根据 T2 * T1 * M0 = E 得到 M0 = T1\-1 * T2\-1
     注意，由于 T1 和 T2 是由初等行变换构造的，其逆矩阵 (T1\-1, T2\-1)很容易求得。*)
  Goal rowOps2matInv l1 * M1 = M0. Proof. meq; f_equal; apply proof_irrelevance. Qed.
  
  Goal rowOps2matInv l2 = M1. Proof. meq; f_equal; apply proof_irrelevance. Qed.
  
  Goal rowOps2matInv l1 * rowOps2matInv l2 = M0.
  Proof. meq; f_equal; apply proof_irrelevance. Qed.

  (* 并猜测 rowOps2matInv_app 性质 *)
  Goal rowOps2matInv (l2 ++ l1) = M0.
  Proof. meq; f_equal; apply proof_irrelevance. Qed.
  
End test.
