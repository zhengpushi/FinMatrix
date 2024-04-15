(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on Qc.
  author    : ZhengPu Shi
  date      : 2023.12
*)

Require Export QcExt.
Require Export MatrixModule.


(* ######################################################################### *)
(** * Matrix theory come from common implementations *)

Module Export MatrixTheoryQc :=
  NormedOrderedFieldMatrixTheory NormedOrderedFieldElementTypeQc.

Open Scope Q_scope.
Open Scope Qc_scope.
Open Scope vec_scope.
Open Scope mat_scope.


(* ######################################################################### *)
(** * Matrix theory applied to this type *)


(* ######################################################################### *)
(** * Usage demo *)
Section test.

  Notation v2l v := (Qc2Q_list (v2l v)).
  Notation m2l M := (Qc2Q_dlist (m2l M)).
  
  Open Scope vec_scope.

  Let u := @l2v 3 (Q2Qc_list [1; 2; 3]%Q).
  Let v := @l2v 3 (Q2Qc_list [2; 1; 0]%Q).
  (* Compute v2l (vproj u v). *)
  (* Compute v2l (vperp u v). *)
  (* Compute vlen u. *)
  
  Open Scope mat_scope.
  
  Let M := @l2m 3 3 (Q2Qc_dlist [[1;-3;-2];[-2;1;-4];[-1;4;-1]]%Q).
  
  (* Compute m2l M. *)
  (* Compute m2l (M * M). *)
  (* Compute m2l ((Q2Qc 5) \.* M). *)
  (* Compute m2l (minvAM M). *)
  (* Compute m2l (minvGE M). *)
  (* Compute m2l (minv M). *)
  (* Compute v2l (cramerRule M u). *)
  (* Compute m2l (minv1 (mat1 + mat1)). *)
  (* Compute m2l (minv2 (mat1 + mat1)). *)
  (* Compute m2l (minv3 (mat1 + mat1)). *)
  (* Compute m2l (minv4 (mat1 + mat1)). *)
  (* Check morth M. *)
  (* Check GOnP M. *)
  (* Check mkGOn M. *)
  (* Check SOnP M. *)
  (* Check mkSOn M. *)
  
End test.
