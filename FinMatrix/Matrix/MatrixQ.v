(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on Q.
  author    : ZhengPu Shi
  date      : 2023.12
*)

Require Export QExt.
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

(** Inverse matrix over Q type *)
(* Although Q type is not supported directly for inverse algorithms (due to
   the current field structure need Leibniz equal but Q is Setoid equal),
   We can utilize the ability of Qc type. We can do it by folloing steps:
   1. use Q2Qc to package input data of Q type to Qc type
   2. solve the problem with Qc type
   3. use Qc2Q to unpackage output data of Qc type to Q type.
*)
Section inv_Q.

  Import MatrixQc.

  (** Check matrix invertibility with lists as input by GE *)
  Definition minvtblebListGE (n : nat) (dl : dlist Q) : bool :=
    minvtblebListGE n (Q2Qc_dlist dl).

  (** Inverse matrix with lists for input and output by GE *)
  Definition minvListGE (n : nat) (dl : dlist Q) : dlist Q :=
    Qc2Q_dlist (minvListGE n (Q2Qc_dlist dl)).

  (** Check matrix invertibility with lists as input by AM *)
  Definition minvtblebListAM (n : nat) (dl : dlist Q) : bool :=
    minvtblebListAM n (Q2Qc_dlist dl).

  (** Inverse matrix with lists for input and output by AM *)
  Definition minvListAM (n : nat) (dl : dlist Q) : dlist Q :=
    Qc2Q_dlist (minvListAM n (Q2Qc_dlist dl)).
  
End inv_Q.


(* ######################################################################### *)
(** * Usage demo *)
Section test.
  Open Scope vec_scope.
  
  Let u := @l2v 3 [1;2;-3].
  Let v := @f2v 3 (fun i => -1 + nat2Q i).
  
  Open Scope mat_scope.
  
  Let M1 := @l2m 3 3 [[1;-3;-2];[-2;1;-4];[-1;4;-1]].
  (* Compute m2l M1. *)
End test.
