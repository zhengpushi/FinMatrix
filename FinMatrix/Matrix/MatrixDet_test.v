(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : test for matrxi determinant
  author    : Zhengpu Shi
  date      : 2023.06
 *)

Require Import MatrixDet.
Require Import ZArith Reals Lra.

(** Test of determinant on `Z` type *)
Section testZ.
  Import ZArith.
  Open Scope Z_scope.
  Let mdet {n} (M : @smat Z n) : Z := @mdet _ Z.add 0 Z.opp Z.mul 1 n M.

  (* 《高等代数》邱维声 第三版 习题2.2 *)
  Let ex_1_5 : mat Z 5 5 :=
        l2m 0 [[0;0;0;1;0];[0;0;2;0;0];[0;3;8;0;0];[4;9;0;7;0];[6;0;0;0;5]].
  Goal mdet ex_1_5 = 120. cbv. auto. Qed.

  Let ex_2_1 : mat Z 3 3 := l2m 0 [[1;4;2];[3;5;1];[2;1;6]].
  Goal mdet ex_2_1 = -49. cbv. auto. Qed.
End testZ.

(** Test of determinant on `R` type *)
Section testR.
  Import Reals.
  Open Scope R_scope.
  Notation "0" := R0.
  Notation "1" := R1.
  Let mdet {n} (M : @smat R n) : R := @mdet _ Rplus 0 Ropp Rmult 1 n M.

  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : R.

  (* Eval cbv in mdet (mkmat_1_1 a11). *)
  (* = 0 + a11 * 1 *)
  (* Eval cbv in mdet (mkmat_2_2 a11 a12 a21 a22). *)
  (* = 0 + a11 * (a22 * 1) + - (a12 * (a21 * 1)) *)
  (* Eval cbv in mdet (mkmat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33). *)
  (* = 0 + a11 * (a22 * (a33 * 1)) 
         + - (a12 * (a21 * (a33 * 1))) 
         + a12 * (a23 * (a31 * 1)) 
         + - (a11 * (a23 * (a32 * 1))) 
         + a13 * (a21 * (a32 * 1)) 
         + - (a13 * (a22 * (a31 * 1))) *)

  (* 《高等代数》邱维声 第三版 习题2.2 *)
  Let ex_2_3 : mat R 3 3 := l2m 0 [[a11;a12;a13];[0;a22;a23];[0;0;a33]].
  Goal mdet ex_2_3 = a11 * a22 * a33. cbv. lra. Qed.

  (* 2.2.2节，例题3 *)
  Example eg_2_2_2_3 : forall a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 c1 c2 d1 d2 e1 e2 : R,
      mdet (@l2m _ 0 5 5
              [[a1;a2;a3;a4;a5];
               [b1;b2;b3;b4;b5];
               [ 0; 0; 0;c1;c2];
               [ 0; 0; 0;d1;d2];
               [ 0; 0; 0;e1;e2]]) = 0.
  Proof. intros. cbv. lra. Qed.

  (* 2.2.2节，例题4 *)
  Example eg_2_2_2_4 : forall x:R,
      mdet (@l2m _ 0 4 4
              [[7*x;x;1;2*x];
               [1;x;5;-1];
               [4;3;x;1];
               [2;-1;1;x]]) = 7*x^4 - 5*x^3 - 99*x^2 + 38*x + 11.
  Proof. intros. cbv. lra. Qed.
  
End testR.

(* more examples for determinant *)
Section determinant_more.
  Context `{HARing : ARing}.
  Add Ring ring_inst : (make_ring_theory HARing).
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.

  Notation madd := (@madd _ Aadd).
  Infix "+" := madd : mat_scope.
  Notation mdet := (@mdet _ Aadd Azero Aopp Amul Aone).
  Notation "| M |" := (mdet M) : mat_scope.

  Section example1.
    (* 
       a b 0 0 ... 0 0 0 
       0 a b 0 ... 0 0 0
       0 0 a b ... 0 0 0
       ...
       0 0 0 0 ... a b 0
       0 0 0 0 ... 0 a b    = a^n + (-1)^(n+1)b^2
     *)
    
    (* Variable n : nat. *)
    Let n := 7.
    Variable a b : tA.
    Let M1 : smat tA (S n) := mdiagMk Azero (vrepeat a).
    Let M2 : smat tA (S n) := mclsr (mdiagMk Azero (vrepeat b)) #1.
    Let M := M1 + M2.
    (* Compute m2l M. *)
    
    (* a ^ n *)
    Fixpoint ApowNat (a : tA) (n : nat) : tA :=
      match n with
      | O => Aone
      | S n' => a * ApowNat a n'
      end.

    Example mdet_example1 :
    |M| = (ApowNat a (S n) + (if odd (S (S n)) then -b*b else b*b))%A.
    Proof.
      rewrite <- (mdetExCol_eq_mdet) with (j:=#0).
      unfold M,M1,M2.
      simpl.
    Abort.
  End example1.

  Section example2.
    (* Vandermonde determinant *)
  End example2.
End determinant_more.


Section test_cramerRule.
  Import QcExt.
  
  Notation cramerRule := (@cramerRule _ Qcplus 0 Qcopp Qcmult 1 Qcinv).
  Notation cramerRuleList := (@cramerRuleList _ Qcplus 0 Qcopp Qcmult 1 Qcinv).

  Let lA1 := dlistQ2Qc [[1;2];[3;4]]%Q.
  Let lb1 := listQ2Qc [5;6]%Q.
  Let A1 : smat Qc 2 := l2m 0 lA1.
  Let b1 : @vec Qc 2 := l2v 0 lb1.
  (* Compute v2l (cramerRule A1 b1). *)
  (* Compute cramerRuleList 2 lA1 lb1. *)

  Let lA2 := dlistQ2Qc
               [[1;2;3;4;5];
                [2;4;3;5;1];
                [3;1;5;2;4];
                [4;5;2;3;1];
                [5;4;1;2;3]]%Q.
  Let lb2 := listQ2Qc [1;2;3;5;4]%Q.
  (* Compute cramerRuleList 5 lA2 lb2. *)
End test_cramerRule.

