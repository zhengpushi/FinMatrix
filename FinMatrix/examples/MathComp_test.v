(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : test MathComp library
  author    : ZhengPu Shi
  date      : 2022.06
*)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra matrix vector finalg.

(** Evaluation abilities of MathComp *)
Section evaluation.
  Open Scope nat_scope.

  Let m23 := @const_mx nat 2 3 1. (* make a 2*3 constant matrix with 1 *)
  (* get (0,0)-th element. Expected: 1, Received: over 10,000 lines expression *)
  Eval cbv in m23 (@Ordinal 2 0 is_true_true) (@Ordinal 3 0 is_true_true).
End evaluation.
