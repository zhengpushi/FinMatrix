(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Extension for tuples
  author    : ZhengPu Shi
  date      : 2022.06
  
  remark    :
  1. T2 : A * A
     T3 : A * A * A             that is: (A * A) * A
     ...
  2. T_3_3 := T3 * T3 * T3.
*)

Open Scope type_scope.

(** * Short name for tuples type *)
Section TuplesType.

  Context {A : Type}.

  (* Definition T1 := A. *)
  Definition T2 := A * A.
  Definition T3 := T2 * A.
  Definition T4 := T3 * A.
  
  (* Definition T_1_1 := T1. *)
  Definition T_2_2 := T2 * T2.
  Definition T_3_3 := T3 * T3 * T3.

End TuplesType.