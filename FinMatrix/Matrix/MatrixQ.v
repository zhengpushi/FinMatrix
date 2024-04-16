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


(* ######################################################################### *)
(** * Matrix theory come from common implementations *)

Module Export MatrixTheoryQ := BasicMatrixTheory ElementTypeQ.

Open Scope Q_scope.
Open Scope vec_scope.
Open Scope mat_scope.


(* ######################################################################### *)
(** * Matrix theory applied to this type *)


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
