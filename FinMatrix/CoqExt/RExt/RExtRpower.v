(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Simplify the expressions about Rpower.
  author    : ZhengPu Shi
  date      : 2021.05

  remark    :
  1. Definition of Rpower
     Rpower x y := exp (y * ln x)

     a^n       = a * a * ... * a    (* there are n numbers *)
     a^0       = 1 (a ≠ 0)
     a^(-n)    = 1 / a^n (a ≠ 0)
     a^(m/n)   = n√ a^m  (a > 0)
     a^(-m/n)  = 1 / n√ a^m  (a > 0)

 *)

Require Export RExtBase.


(* ======================================================================= *)
(** ** Basic automation *)

#[export] Hint Rewrite
  Rpower_O            (* Rpower x 0 = 1 *)
  Rpower_1            (* power x 1 = x *) 
  : R.

(* ======================================================================= *)
(** ** Additional properties *)

Lemma Rpower_neq0 x y : x <> 0 -> Rpower x y <> 0.
Proof.
  Abort.
