(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on Qc.
  author    : Zhengpu Shi
  date      : 2023.12
*)

Require Export RExt QcExt.
Require Export MatrixModule.


(* ######################################################################### *)
(** * Matrix theory come from common implementations *)

Include (NormedOrderedFieldMatrixTheory NormedOrderedFieldElementTypeQc).

Open Scope Q_scope.
Open Scope Qc_scope.
Open Scope vec_scope.
Open Scope mat_scope.


(* ######################################################################### *)
(** * Matrix theory applied to this type *)


(* ######################################################################### *)
(** * Usage demo *)

Section test.
  Open Scope vec_scope.

  Let u := @l2v 3 (listQ2Qc [1; 2; 3]%Q).
  Let v := @l2v 3 (listQ2Qc [2; 1; 0]%Q).
  (* Compute v2l (vproj u v). *)
  (* Compute v2l (vperp u v). *)
  (* Compute vlen u. *)
  
  Open Scope mat_scope.
  
  Let M := @l2m 3 3 (dlistQ2Qc [[1;-3;-2];[-2;1;-4];[-1;4;-1]]%Q).
  
  (* Compute m2l M. *)
  (* Compute m2l (M * M). *)
  (* Compute m2l ((Q2Qc 5) c* M). *)
  (* Compute m2l (minvAM M). *)
  (* Compute m2l (minvGE M). *)
  (* Compute v2l (cramerRule M u). *)
  (* Check morth M. *)
  (* Check GOnP M. *)
  (* Check mkGOn M. *)
  (* Check SOnP M. *)
  (* Check mkSOn M. *)

  (** Example 1: inverse matrix of a `3x3` matrix over Qc type *)
  Section ex1.
    (* [1 3 1]     [-1 -1  2]
       [2 1 1] <-> [ 0 -1  1]
       [2 2 1]     [ 2  4 -5] *)

    (* Input a matrix with list. Note that we need `Q2Qc` fuction for `Qc` type *)
    Let l1 := dlistQ2Qc [[1;3;1];[2;1;1];[2;2;1]]%Q.
    Let l2 := dlistQ2Qc [[-1;-1;2];[0;-1;1];[2;4;-5]]%Q.
    Let M1 : smat 3 := l2m l1.
    Let M2 : smat 3 := l2m l2.

    (* Calculate the inversibility *)
    (* Compute minvtblebListAM 3 l1. *)
    (* Compute minvtblebListGE 3 l1. *)
    (* Compute minvtblebAM M1. *)
    (* Compute minvtblebGE M1. *)

    (* Calculate the inverse matrix *)
    (* Compute minvListAM 3 l1. *)
    (* Compute minvListGE 3 l1. *)
    (* Compute m2l (minvAM M1). *)
    (* Compute m2l (minvGE M1). *)
    
    (* Note that the `canon` part is unnecessary for users, we can remove them *)
    (* Compute Qc2Q_dlist (minvListAM 3 l1). *)

    (* Proof that the inverse of M1 is M2 *)
    Goal minvAM M1 = M2.
    Proof. meq. Qed.

  (* In summary, for inverse matrix over Qc type:
     1. Pros
       * canonical form enable leibniz equality
     2. Cons
       * the input need `Q2Qc` function
       * the output has unnecessary proofs. *)
  End ex1.

  (* Example 2: solve equation *)
  Section ex2.
    (* Given an equation [A * x = b] as following:
       1 * x + 2 * y = 5
       3 * x + 4 * y = 6 *)
    Let A : smat 2 := l2m (dlistQ2Qc [[1;2];[3;4]]%Q).
    Let b : vec 2 := l2v (listQ2Qc [5;6]%Q).
    
    (* solve equation by cramer-rule *)
    (* Compute v2l (cramerRule A b). *)
    
    (* solve equation by inverse matrix *)
    (* Compute v2l (solveEqAM A b). *)
    (* Compute v2l (solveEqGE A b). *)
  End ex2.

  (* Example 3: solve quation with a random 5*5 matrix *)
  Section ex3.
    Let M2 : smat 5 :=
          l2m (dlistQ2Qc
                 [[1;2;3;4;5];
                  [2;4;3;5;1];
                  [3;1;5;2;4];
                  [4;5;2;3;1];
                  [5;4;1;2;3]]%Q).
    Let b2 : vec 5 := l2v (listQ2Qc [1;2;3;5;4]%Q).
    (* Compute v2l (cramerRule M2 b2). *)
    (* Compute v2l (solveEqAM M2 b2). *)
    (* Compute v2l (solveEqGE M2 b2). *)
  End ex3.
  
End test.
