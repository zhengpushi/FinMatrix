(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Simplify the expressions about exp.
  author    : ZhengPu Shi
  date      : 2021.05

  remark    :
 *)

Require Export RExtBase.


#[export] Hint Rewrite
  exp_0               (* exp 0 = 1 *)
  : R.
