(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Extension for sequence on R.
  author    : ZhengPu Shi
  date      : 2022.06
 *)

Require Export Sequence.
Require Export Fsequence.
Require Export RExt.

(* ======================================================================= *)
(** ** More properties of sequence on R type *)
Section seq_R.
  Import RExt.
  Open Scope R_scope.

  Notation Sum := (@seqsum _ Rplus R0).
End seq_R.

