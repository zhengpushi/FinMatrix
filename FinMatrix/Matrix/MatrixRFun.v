(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on function of R to R.
  author    : ZhengPu Shi
  date      : 2023.12
 *)

Require Export RExt.
Require Export RealFunction.
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
  Let f00 : A := fun t => 1.
  Let f01 : A := fun t => 2.
  Let f10 : A := fun t => 3.
  Let f11 : A := fun t => 4.
  Let l1 := [[f00;f01];[f10;f11]].
  Let m1 := @l2m 2 2 l1.
  (* Compute m2l m1. *)
  (* Compute m2l (mmap Aopp m1). *)
  (* Compute m2l (m1 * m1). *)
  
End test.

Section Example4CoordinateSystem.
  Open Scope fun_scope.
  Notation "1" := Aone : fun_scope.
  Notation "0" := Azero : fun_scope.
  
  Variable ψ θ ϕ : A.
  Let cθ : A := fun t => cos (θ t).
  Let sθ : A := fun t => sin (θ t).
  Let cψ : A := fun t => cos (ψ t).
  Let sψ : A := fun t => sin (ψ t).
  Let cϕ : A := fun t => cos (ϕ t).
  Let sϕ : A := fun t => sin (ϕ t).
  
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
