(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on Complex.
  author    : Zhengpu Shi
  date      : 2023.12
 *)

Require Export Complex.
Require Export MatrixModule.


(* ######################################################################### *)
(** * Matrix theory come from common implementations *)

Include (FieldMatrixTheory FieldElementTypeC).

Open Scope C_scope.
Open Scope vec_scope.
Open Scope mat_scope.


(* ######################################################################### *)
(** * Matrix theory applied to this type *)


(* ######################################################################### *)
(** * Usage demo *)

Section test.

  Open Scope vec_scope.

  Let u := @l2v 3 [1 +i 2; 3 +i 4; 5 +i 6].
  Let v := @l2v 3 [0 +i 2; 3 +i 4; 5 +i 6].

  
  Open Scope mat_scope.
  
  Let M := @l2m 2 2 [[1 +i 2; 3 +i 4];[5 +i 6; 7 +i 8]].

  (* test rewriting *)
  Example mat_C_ex1 : forall r c s (m1 m2 : mat r c) (m3 : mat c s),
      (m1 - m2) * m3 = m1 * m3 - m2 * m3.
  Proof.
    intros. rewrite mmul_msub_distr_r. auto.
  Qed.

  Example mat_C_ex2 : forall r c (m1 m2 : mat r c) x, m1 = m2 -> x s* m1 = x s* m2.
  Proof. intros. f_equal. auto. Qed.

  (* test_monoid. *)
  Example mat_C_ex3 : forall r c (m1 m2 : mat r c),
      (mat0 + m1) - (mat0 - m2) = m2 + (m1 - mat0).
  Proof. intros. pose proof (madd_AGroup r c). agroup. Qed.

End test.
