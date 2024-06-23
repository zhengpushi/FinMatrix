(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on function of R to R.
  author    : Zhengpu Shi
  date      : 2023.12
 *)

Require Export RExt RFunExt.
Require Export MatrixModule.


(* ######################################################################### *)
(** * Matrix theory come from common implementations *)

Module Export MatrixTheoryRFun := RingMatrixTheory RingElementTypeRFun.

Open Scope R_scope.
Open Scope Rfun_scope.
Open Scope vec_scope.
Open Scope mat_scope.


(* ######################################################################### *)
(** * Matrix theory applied to this type *)


(** Derivative of matrix *)
(* ref: page 162, QuanQuan, 多旋翼设计与控制 *)

(** 标量(函数)对矩阵(函数)的梯度 *)
(* Variable f : R -> R. *)
(* Set Printing All. *)
(* Check f '. *)
(* Definition mderiv {r c} (a : T) (X : mat r c) := *)
  

(* ######################################################################### *)
(** * Usage demo *)

Section test.
  Let f00 : tA := fun t => 1%R.
  Let f01 : tA := fun t => 2.
  Let f10 : tA := fun t => 3.
  Let f11 : tA := fun t => 4.
  Let l1 := [[f00;f01];[f10;f11]].
  Let m1 := @l2m 2 2 l1.
  (* Compute m2l m1. *)
  (* Compute m2l (mmap Aopp m1). *)
  (* Compute m2l (m1 * m1). *)
  
End test.

Section Example4CoordinateSystem.
  Open Scope A_scope.
  Notation "1" := Aone : Rfun_scope.
  Notation "0" := Azero : Rfun_scope.
  
  Variable ψ θ ϕ : tA.
  Let cθ : tA := fun t => cos (θ t).
  Let sθ : tA := fun t => sin (θ t).
  Let cψ : tA := fun t => cos (ψ t).
  Let sψ : tA := fun t => sin (ψ t).
  Let cϕ : tA := fun t => cos (ϕ t).
  Let sϕ : tA := fun t => sin (ϕ t).
  
  Let Rx := mkmat_3_3 1 0 0 0 cϕ sϕ 0 (-sϕ) cϕ.
  Let Ry := mkmat_3_3 cθ 0 (-sθ) 0 1 0 sθ 0 cθ.
  Let Rz := mkmat_3_3 cψ sψ 0 (-sψ) cψ 0 0 0 1.
  Let Rbe :=
        mkmat_3_3
          (cθ * cψ) (cψ * sθ * sϕ - sψ * cϕ)
          (cψ * sθ * cϕ + sϕ * sψ) (cθ * sψ)
          (sψ * sθ * sϕ + cψ * cϕ)
          (sψ * sθ * cϕ - cψ * sϕ)
          (-sθ) (sϕ * cθ) (cϕ * cθ).
  Lemma Rbe_ok : (Rbe = Rz\T * Ry\T * Rx\T)%M.
  Proof. apply m2l_inj. cbv. list_eq; extensionality x; ring. Qed.
    
End Example4CoordinateSystem.
