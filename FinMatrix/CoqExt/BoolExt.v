(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : auxiliary library for bool.
  author    : Zhengpu Shi
  date      : 2022.04
*)

Require Export Bool.
Require Export Setoid.    (* andb_true_iff need it. *)


(* ######################################################################### *)
(** * More properties for bool *)

(** andb split *)

Ltac tac_andb_true_iff :=
  intros; split; intro H;[
  repeat rewrite andb_true_iff in *;
  repeat match goal with | H : _ /\ _ |- _ => destruct H; auto 10 end|
  repeat rewrite andb_true_iff;
  repeat match goal with | H : _ /\ _ |- _ => destruct H; auto 10 end].
  
Lemma andb_true_iff3 : forall b1 b2 b3 : bool, 
  b1 && b2 && b3 = true <-> 
  b1 = true /\ b2 = true /\ b3 = true.
Proof.
  tac_andb_true_iff.
Qed.

Lemma andb_true_iff4 : forall b1 b2 b3 b4 : bool, 
  b1 && b2 && b3 && b4 = true <-> 
  b1 = true /\ b2 = true /\ b3 = true /\ b4 = true.
Proof.
  tac_andb_true_iff.
Qed.

Lemma andb_true_iff5 : forall b1 b2 b3 b4 b5 : bool, 
  b1 && b2 && b3 && b4 && b5 = true <-> 
  b1 = true /\ b2 = true /\ b3 = true /\ b4 = true /\ b5 = true.
Proof.
  tac_andb_true_iff.
Qed.

Lemma andb_true_iff6 : forall b1 b2 b3 b4 b5 b6 : bool, 
  b1 && b2 && b3 && b4 && b5 && b6 = true <-> 
  b1 = true /\ b2 = true /\ b3 = true /\ b4 = true /\ b5 = true /\ 
  b6 = true.
Proof.
  tac_andb_true_iff.
Qed.

Lemma andb_true_iff7 : forall b1 b2 b3 b4 b5 b6 b7 : bool, 
  b1 && b2 && b3 && b4 && b5 && b6 && b7 = true <-> 
  b1 = true /\ b2 = true /\ b3 = true /\ b4 = true /\ b5 = true /\ 
  b6 = true /\ b7 = true.
Proof.
  tac_andb_true_iff.
Qed.


(** andb equal inversion *)

Lemma andb_eq_inv : forall a1 a2 b1 b2 : bool,
  a1 = b1 -> a2 = b2 -> a1 && a2 = b1 && b2.
Proof.
  destruct a1,a2,b1,b2; intros; auto.
Qed.


(* 解决常见布尔逻辑的证明 *)
Ltac solve_bool :=
  let H := fresh "H" in 
  match goal with
  (* b = false |- b <> true *)
  | |- ?b = false -> ?b <> true => intros H; rewrite H; auto
  (* b <> true |- b = false *)
  | |- ?b <> true -> ?b = false => intros; apply not_true_is_false; auto
  end.


(* ######################################################################### *)
(** * bool to Prop *)

(* (** bool to Prop *) *)
(* Definition is_true (b : bool) : Prop := b = true. *)
(* Coercion is_true : bool >-> Sortclass. *)

(* (* Note that Coq.Bool.Bool.Is_true is another implementation, and I argue that it is  *)
(*    a bit complex *) *)
(* (* Print Is_true. (* Is_true = fun b : bool => if b then True else False *) *)
(*      : bool -> Prop *) *)

(* Lemma is_true_and_iff : forall b1 b2 : bool, *)
(*     is_true b1 /\ is_true b2 <-> is_true (b1 && b2). *)
(* Proof. destruct b1,b2; intros; split; intros; auto; try easy. Qed. *)

(* Lemma is_true_or_iff : forall b1 b2 : bool, *)
(*     is_true b1 \/ is_true b2 <-> is_true (b1 || b2). *)
(* Proof. *)
(*   destruct b1,b2; intros; split; intros; auto; try easy. *)
(*   simpl. unfold is_true in *. destruct H; auto. *)
(* Qed. *)

(* (** use reflect to connect bool and proposition equality *) *)
(* Example eqnP (n m : nat) : reflect (n = m) (Nat.eqb n m). *)
(* Proof. *)
(*   revert m. induction n; intros [|m]; simpl; try constructor; auto. *)
(*   destruct IHn with m; subst; constructor; auto. *)
(* Qed. *)
