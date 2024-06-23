(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix on nat.
  author    : Zhengpu Shi
  date      : 2023.12
 *)

Require Export NatExt.
Require Export MatrixModule.


(* ######################################################################### *)
(** * Matrix theory come from common implementations *)

Include (MonoidMatrixTheory MonoidElementTypeNat).

Open Scope nat_scope.
Open Scope vec_scope.
Open Scope mat_scope.


(* ######################################################################### *)
(** * Matrix theory applied to this type *)


(* ######################################################################### *)
(** * Usage demo *)
Section test.

  Open Scope vec_scope.
  
  Let u := @l2v 3 [1;2;3].
  (* Compute v2l u. *)
  Let v := @f2v 3 (fun i => 5 + i)%nat.
  (* Compute f2l 3 (v2f u). *)
  
  (* Compute mkvec3 4 5 6. *)
  (* Compute v2l (vrepeat 3 9). *)
  (* Compute v2l (@vzero 3). *)
  (* Compute v2l (vmap S u). *)
  (* Compute v2l (vmap2 Nat.add u v). *)
  (* Compute Vector.v2l (Vector.vmap2 pair u v). *)
  (* Compute v2l (u + v). *)
  (* Compute v2l (vconsH 5 (vrepeat 3 1)). *)
  (* Compute v2l (vconsT (vrepeat 3 1) 5). *)
  (* Check vforall u (fun a => a = 0). *)
  (* Check vexist u (fun a => a = 0). *)
  (* Check vmem u 1. *)
  (* Check vmems u v. *)
  (* Compute vfoldl u true (fun b n => andb b (n =? 0)). *)
  (* Compute vfoldr u true (fun n b => andb b (n =? 0)). *)
  
  Open Scope mat_scope.
  
  Let M := @l2m 3 3 [[1;2;3];[4;5;6];[7;8;9]].
  (* Compute m2l M. *)
  (* Compute m2l (mmap S M). *)
  (* Compute m2l (mkmat_2_2 1 2 3 4). *)
  (* Compute m2l (@mat0 2 3). *)
  (* Compute m2l (M + M). *)
  (* Compute m2l (mdiagMk (@l2v 3 [1;2;3])). *)
  (* Check mdiag M. *)
  (* Compute m2l (M\T). *)
  (* Compute m2l (mconsrH u M). *)
  (* Compute m2l (mconsrT M u). *)
  (* Compute m2l (mconscH u M). *)
  (* Compute m2l (mconscT M u). *)
  (* Compute m2l (mappr M M). *)
  (* Compute m2l (mappc M M). *)

  Example mnth_ex1 : M.11 = 1.
  Proof. auto. Qed.
  
  Variable a11 a12 a21 a22 : nat.
  Variable f : nat -> nat.
  Let M2 := @l2m 2 2 [[a11;a12];[a21;a22]].
  (* Compute m2l M2.               (* = [[a11; a12]; [a21; a22]] *) *)
  (* Compute m2l (mmap f M2).      (* = [[f a11; f a12]; [f a21; f a22]] *) *)

End test.
