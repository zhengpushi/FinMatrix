(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
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

(** Cramer rule over list of Q type *)
Definition cramerRuleListQ (n : nat) (lC : dlist Q) (lb : list Q) : list Q :=
  let lC' := dmap Q2Qc lC in
  let lb' := map Q2Qc lb in
  let lx' := cramerRuleList n lC' lb' in
  map Qc2Q lx'.

(* {cramerRuleListQ n lC lb} = cramerRuleList n {lC} {lb} *)
Lemma cramerRuleListQ_spec : forall (n : nat) (lC : dlist Q) (lb : list Q),
    map Q2Qc (cramerRuleListQ n lC lb) = cramerRuleList n (dmap Q2Qc lC) (map Q2Qc lb).
Proof.
  intros. unfold cramerRuleListQ. rewrite map_map.
  apply ListExt.map_id. intros. apply Q2Qc_Qc2Q.
Qed.

(** Solve the equation with the form of C*x=b by GE over list of Q type. *)
Definition solveEqListGEQ (n : nat) (lC : dlist Q) (lb : list Q) : list Q :=
  let lC' := dmap Q2Qc lC in
  let lb' := map Q2Qc lb in
  let lx' := solveEqListGE n lC' lb' in
  map Qc2Q lx'.

(** {solveEqListGEQ n lC lb} = solveEqListGE n {lC} {lb} *)
Lemma solveEqListGEQ_spec : forall (n : nat) (lC : dlist Q) (lb : list Q),
    map Q2Qc (solveEqListGEQ n lC lb) = solveEqListGE n (dmap Q2Qc lC) (map Q2Qc lb).
Proof.
  intros. unfold solveEqListGEQ. rewrite map_map.
  apply ListExt.map_id. intros. apply Q2Qc_Qc2Q.
Qed.

(** Solve the equation with the form of C*x=b by AM over list of Q type. *)
Definition solveEqListAMQ (n : nat) (lC : dlist Q) (lb : list Q) : list Q :=
  let lC' := dmap Q2Qc lC in
  let lb' := map Q2Qc lb in
  let lx' := solveEqListAM n lC' lb' in
  map Qc2Q lx'.

(** {solveEqListAMQ n lC lb} = solveEqListAM n {lC} {lb} *)
Lemma solveEqListAMQ_spec : forall (n : nat) (lC : dlist Q) (lb : list Q),
    map Q2Qc (solveEqListAMQ n lC lb) = solveEqListAM n (dmap Q2Qc lC) (map Q2Qc lb).
Proof.
  intros. unfold solveEqListAMQ. rewrite map_map.
  apply ListExt.map_id. intros. apply Q2Qc_Qc2Q.
Qed.

Notation solveEqListQ := solveEqListGEQ.


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

  (** Solve equation over list of Q type *)
  Open Scope Q_scope.

  Let C := [[1;2];[3;4]].
  Let b := [5;6].
  (* Compute cramerRuleListQ 2 C b. (*   = [-4; 9 # 2] : list Q *) *)
  (* Compute solveEqListGEQ 2 C b.  (*   = [-4; 9 # 2] : list Q *) *)
  (* Compute solveEqListAMQ 2 C b.  (*   = [-4; 9 # 2] : list Q *) *)
  (* Compute solveEqListQ 2 C b.  (*   = [-4; 9 # 2] : list Q *) *)
End test.
