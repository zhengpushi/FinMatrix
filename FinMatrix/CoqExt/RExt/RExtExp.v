(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Simplify the expressions about exp.
  author    : Zhengpu Shi
  date      : 2021.05

  remark    :
 *)

Require Export RExtBase.


(* ======================================================================= *)
(** ** Basic automation *)

Hint Rewrite
  exp_0               (* exp 0 = 1 *)
  : R.


(* ======================================================================= *)
(** ** Additional properties *)


(* Axiom domain_of_exp : forall (a : R), (a > 0 /\ a <> 1) -> domain_of (exp a) = allR. *)
(* Fact range_of_exp (a : R) : range_of (exp a) = fun x => x > 0. Admitted. *)
