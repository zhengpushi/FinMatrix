(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Simplify the expressions about pow.
  author    : Zhengpu Shi
  date      : 2021.05

  remark    :
 *)

Require Export RExtBase RExtSqr.


Hint Rewrite
  pow1                (* 1 ^ n = 1 *)
  pow_O               (* x ^ 0 = 1 *)
  pow_1               (* x ^ 1 = x *)
  : R.


(** Convert `a ^ (n + 2)` to `(a ^ 2) * (a ^ n)` *)
Ltac simp_pow :=
  try match goal with
    | |- context[?a ^ 4] => replace (a ^ 4) with ((a ^ 2) ^ 2); [|ring]
    | |- context[?a ^ 3] => replace (a ^ 3) with ((a ^ 2) * a)%R; [|ring]
    end;
  try rewrite !Rpow2_Rsqr in *.
