(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : decidable procedure for R type.
  author    : Zhengpu Shi
  date      : 2021.05

  remark    :
 *)

Require Export RExtBase.


(** ** Notations for comparison with decidable procedure *)
Infix "??=" := (Req_EM_T) : R_scope.

(* For all four cases of comparison, we allow all these notations, but the `Display`
   will be only two cases, in order to simplify the cases of proof *)

(* These two notations will be covered by next two notations *)
Notation "x ??>= y" := (Rle_lt_dec y x) : R_scope.
Notation "x ??> y" := (Rlt_le_dec y x) : R_scope.

(* These two notations have higher priority *)
Infix "??<=" := (Rle_lt_dec) : R_scope.
Infix "??<" := (Rlt_le_dec) : R_scope.

(** ** Verify above notations are reasonable *)

(* a = b, iff, a ??= b *)
Lemma ReqDec_spec : forall a b : R, a = b <-> if a ??= b then true else false.
Proof. intros. destruct (_??=_); split; intros; try congruence. Qed.

(* a ??>= b, iff, b ??<= a *)
Lemma RgeDec_spec : forall a b : R,
    (if a ??>= b then true else false) = (if b ??<= a then true else false).
Proof. intros. auto. Qed.

(* a ??> b, iff, b ??< a *)
Lemma RgtDec_spec : forall a b : R,
    (if a ??> b then true else false) = (if b ??< a then true else false).
Proof. intros. auto. Qed.

(* a <= b, iff, a ??<= b *)
Lemma RleDec_spec : forall a b : R, a <= b <-> if a ??<= b then true else false.
Proof. intros. destruct (_??<=_); split; intros; try congruence. lra. Qed.

(* a < b, iff, a ??< b *)
Lemma RltDec_spec : forall a b : R, a < b <-> if a ??< b then true else false.
Proof. intros. destruct (_??<_); split; intros; try congruence. lra. Qed.


(** ** Aditional properties about RxxDec *)

(* if x ??<= x then b1 else b2 = b1 *)
Lemma RleDec_refl : forall {B} (x : R) (b1 b2 : B),
    (if x ??<= x then b1 else b2) = b1.
Proof. intros. destruct (_??<= _); auto. lra. Qed.
