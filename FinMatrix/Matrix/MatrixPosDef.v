(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Positive Definite and Positive Semi-Definite
  author    : Zhengpu Shi
  date      : 2023.12

  remark    :

  来源：https://www.zhihu.com/tardis/zm/art/44860862

  1. 基本定义
  (1) 给定n*n的实对称矩阵A，若对于任意n维非零向量x，有 x\T A x > 0，
      则A是正定矩阵。
  (2) 给定n*n的实对称矩阵A，若对于任意n维向量x，有 x\T A x >= 0，
      则A是半正定矩阵。
  2. 二次函数与正定/半正定函数
  (1) 二次函数 y=ax^2，当a>0时，开头向上，此时任意x，都有y>=0；
      而且，当x<>0时，有 y>0。
  (2) 对于 y=x^T A x，可视作 y=ax^2 的多维表达式。
      若希望y>=0对任意x成立，要求A是半正定矩阵。
      若希望y>0 对任意非零0成立，要求A是正定矩阵。
  3. 直观解释
  (1) 正定矩阵A∈R^(n*n) 和非零向量x∈R^n，则 Ax∈R^n 与 x 的夹角小于π/2。
 *)

Require Import NatExt.
Require Import CoqExt.Hierarchy.
Require Import MatrixList.Matrix.
Require Import CoqExt.MyExtrOCamlR.
Require QcExt RExt.

Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv.


(* ===================================================================== *)
(** ** Positive Definite. *)

(* 单位矩阵是正定矩阵 *)
