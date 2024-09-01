(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Permutation vs. permutations (mathcomp/ssreflect/seq.v)
  author    : Zhengpu Shi
  date      : 2024.09
  
 *)

From mathcomp Require Import all_algebra seq eqtype ssrnat.
Require Import Permutation.

Check perm.

Compute permutations [::1;2;3].
(* = [[2; 1; 3]; [1; 2; 3]; [3; 1; 2]; [1; 3; 2]; [2; 3; 1]; [3; 2; 1]] *)

Compute perm [::1;2;3].
(* = [[1; 2; 3]; [2; 1; 3]; [2; 3; 1]; [1; 3; 2]; [3; 1; 2]; [3; 2; 1]] *)

(* Time Compute permutations [::1;2;3;4;5;6;7]. *)
(* = [[4; 3; 5; 2; 6; 1; 7]; [3; 4; 5; 2; 6; 1; 7]; [5; 3; 4; 2; 6; 1; 7]; *)
(*    [3; 5; 4; 2; 6; 1; 7]; [4; 5; 3; 2; 6; 1; 7]; [5; 4; 3; 2; 6; 1; 7]; *)
(*    [4; 2; 5; 3; 6; 1; 7]; [2; 4; 5; 3; 6; 1; 7]; [5; 2; 4; 3; 6; 1; 7]; *)
(* Finished transaction in 1.042 secs (1.042u,0.s) (successful) *)

(* Time Compute perm [::1;2;3;4;5;6;7]. *)
(* = [[1; 2; 3; 4; 5; 6; 7]; [2; 1; 3; 4; 5; 6; 7]; [2; 3; 1; 4; 5; 6; 7]; *)
(*    [2; 3; 4; 1; 5; 6; 7]; [2; 3; 4; 5; 1; 6; 7]; [2; 3; 4; 5; 6; 1; 7]; *)
(*    [2; 3; 4; 5; 6; 7; 1]; [1; 3; 2; 4; 5; 6; 7]; [3; 1; 2; 4; 5; 6; 7]; *)
(* Finished transaction in 1.078 secs (1.078u,0.s) (successful) *)

(* Time Compute permutations [::1;2;3;4;5;6;7;8]. *)
(* Finished transaction in 12.121 secs (10.725u,0.051s) (successful) *)

(* Time Compute perm [::1;2;3;4;5;6;7;8]. *)
(* Finished transaction in 11.947 secs (10.522u,0.084s) (successful) *)
