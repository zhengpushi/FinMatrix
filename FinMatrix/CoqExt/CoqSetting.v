(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Set Coq default behavior to avoid annoying problem.
  author    : Zhengpu Shi
  date      : 2023.03
  
*)

(** * Bellet behavior, caused by Mathcomp.ssreflect.ssreflect.v *)
(* Global Set Bullet Behavior "None". *)
Global Set Bullet Behavior "Strict Subproofs".
