(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on Z.
  author    : ZhengPu Shi
  date      : 2023.12
 *)

Require Export ZExt.
Require Export MatrixModule.


(* ######################################################################### *)
(** * Matrix theory come from common implementations *)

Include (OrderedRingMatrixTheory OrderedRingElementTypeZ).

Open Scope Z_scope.
Open Scope vec_scope.
Open Scope mat_scope.


(* ######################################################################### *)
(** * Matrix theory applied to this type *)


(* ######################################################################### *)
(** * Usage demo *)
Section test.
  Open Scope vec_scope.
  
  Let u := @l2v 3 [1;2;-3].
  Let v := @f2v 3 (fun i => -1 + nat2Z i)%Z.
  (* Compute v2l (u + v). *)
  (* Compute v2l (- u). *)
  (* Compute v2l (u - v). *)
  (* Compute v2l (5 c* u). *)
  (* Compute <u, v>. *)
  (* Compute vsum u. *)
  (* Check vunit u. *)
  (* Check u _|_ v. *)
  
  Open Scope mat_scope.
  
  Let M := @l2m 3 3 [[1;2;3];[4;5;6];[7;8;9]].
  Let N := @l2m 3 3 [[1;2;3];[4;5;6];[7;8;10]].
  (* Compute m2l M.                 (* = [[1; 2]; [3; 4]] *) *)
  (* Compute m2l (mmap Z.opp M).    (* = [[-1; -2]; [-3; -4]] *) *)
  (* Compute m2l (@mat1 3). *)
  (* Compute m2l (M + M). *)
  (* Compute tr M. *)
  (* Compute m2l (M - M). *)
  (* Compute m2l (- M). *)
  (* Compute m2l (5 c* M). *)
  (* Compute m2l (M * M). *)
  (* Check skewP M. *)
  (* Compute mdet M. *)
  (* Compute mdet N. *)
  (* Compute mdet1 mat1. *)
  (* Compute mdet2 mat1. *)
  (* Compute mdet3 mat1. *)
  (* Compute m2l (madj M). *)
  (* Check minvtble M. *)

  Let M4 :=
        @l2m 9 9
          [[  9;     2;     7;     8;     5;     3;     8;     9;     4;     1];
           [ 10;    10;     1;     1;     4;     7;     3;     3;     9;     1];
           [  2;    10;     9;     3;     8;     7;     6;     9;     6;     6];
           [ 10;     5;    10;     1;     8;     2;     7;     3;     6;     8];
           [  7;     9;     7;     1;     2;     2;     9;    10;    10;    10];
           [  1;     2;     8;     9;     5;     5;    10;     4;     3;     2];
           [  3;     5;     8;     7;     5;    10;     6;     2;     8;     6];
           [  6;    10;     4;     4;     7;     4;     2;     3;     8;     5];
           [ 10;     8;     7;    10;     8;     6;     2;     7;     4;     1];
           [ 10;    10;     2;     1;     8;     3;     3;     5;     6;     4]].

  (* Time Eval vm_compute in mdet M4. *)
  (*      = -93336855 *)
  (*      : A *)
  (* Finished transaction in 9.056 secs (9.052u,0.004s) (successful) *)

  (* Time Eval vm_compute in mdetEx M4. *)
  (*      = -93336855 *)
  (*      : A *)
  (* Finished transaction in 8.715 secs (8.714u,0.s) (successful) *)

  Let M5 :=
        @l2m 20 20
          [[74;77;35;72;54;56;73;57;61;80;51;95;38;61;96;24;87;10;34;28];
           [10;19;33;87;91;44;91;34;11;36;84;14;84;56;84;47;46;94;59;57];
           [53;39;51;88;47;31;90;56;10;39;79;94;15;68;80;57;24;97;70;44];
           [32;13;68;11;89;60;87;21;46;50;52;44;64;50;39;52;26;32;70;21];
           [57;51;39;19;13;62;64;89;60;95;61;70;59;26;59;28;57;18;54;63];
           [63;98;97;12;70;72;54;29;35;34;22;20;57;88;98;14;96;21;47;71];
           [74;70;24;46;67;66;28;77;80;84;20;62;29;91;91;79;15;20;33;21];
           [27;56;78;47;92;51;31;44;45;93;53;13;20;80;34;21;50;62;57;93];
           [19;67;61;19;44;61;62;96;45;22;88;31;16;53;57;71;29;56;31;58];
           [62;89;46;76;50;30;90;12;95;21;53;77;17;69;44;68;80;13;89;12];
           [83;73;97;95;62;73;92;22;18;49;97;25;20;19;52;62;84;26;84;44];
           [27;61;78;52;27;51;24;18;94;17;60;20;23;48;47;48;58;30;23;28];
           [12;89;96;75;23;32;18;71;98;60;57;56;34;44;54;94;77;51;21;49];
           [17;69;22;50;53;36;57;28;60;39;11;25;96;91;76;46;22;39;55;68];
           [21;24;57;90;58;39;68;56;51;61;87;96;71;80;61;49;19;14;12;19];
           [68;56;72;29;72;47;55;46;76;49;66;71;80;98;10;64;49;22;59;36];
           [30;44;64;33;17;68;24;76;34;30;36;57;21;60;18;45;31;26;46;70];
           [44;83;34;51;80;29;67;21;46;12;50;18;86;89;91;67;23;25;29;14];
           [84;90;53;34;84;77;54;98;69;35;87;67;25;11;51;61;87;16;31;11];
           [83;47;51;57;72;45;18;33;47;68;26;62;64;67;87;26;13;94;31;39]].
  (* Time Eval vm_compute in mdet M5. *)
  
End test.
