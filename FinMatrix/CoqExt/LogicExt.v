(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Extension of Logic
  author    : ZhengPu Shi
  date      : 2023.02
  
*)

Require Export FunctionalExtensionality.
Require Export PropExtensionality.
Require Export Ensembles.       (* 这里有一些全称量词的性质比较有趣 *)
Require Export Classical.


(** * 标准库已有的性质 *)

(** *** 来自 Coq.Logic.FunctionalExtensionality *)

(* 依赖类型上的 eta转换 *)
(* Check eta_expansion_dep. *)
(* : forall f : forall x : ?A, ?B x, f = (fun x : ?A => f x) *)

(* 普通类型上的 eta转换 *)
(* Check eta_expansion. *)
(* : forall f : ?A -> ?B, f = (fun x : ?A => f x) *)

(* 全称量词与等于的关系 *)
(* Check forall_extensionalityP. *)
(* : (forall x : ?A, ?B x = ?C x) -> *)
(*   (forall x : ?A, ?B x) = (forall x : ?A, ?C x) *)

(* 依赖类型上的函数外延性 *)
(* Check functional_extensionality_dep. *)
(* forall (f g : forall x : A, B x), (forall x, f x = g x) -> f = g. *)

(* 普通类型上的函数外延性 *)
(* Check functional_extensionality. *)
(* forall f g : ?A -> ?B, (forall x, f x = g x) -> f = g. *)

(* 函数外延性的反方向 *)
(* Check equal_f. *)
(* : ?f = ?g -> forall x : ?A, ?f x = ?g x *)


(* 策略 extensionality *)


(** *** 来自 Coq.Logic.PropExtensionality *)

(* 命题外延性 *)
(* Axiom propositional_extensionality : forall (P Q : Prop), (P <-> Q) -> P = Q. *)


(** *** 来自 Coq.Logic.Classical_Prop *)
(*
Axiom classic : forall P:Prop, P \/ ~ P.
Lemma NNPP : forall p:Prop, ~ ~ p -> p.
Lemma Peirce : forall P:Prop, ((P -> False) -> P) -> P.
Lemma not_imply_elim : forall P Q:Prop, ~ (P -> Q) -> P.
Lemma not_imply_elim2 : forall P Q:Prop, ~ (P -> Q) -> ~ Q.
Lemma imply_to_or : forall P Q:Prop, (P -> Q) -> ~ P \/ Q.
Lemma imply_to_and : forall P Q:Prop, ~ (P -> Q) -> P /\ ~ Q.
Lemma or_to_imply : forall P Q:Prop, ~ P \/ Q -> P -> Q.
Lemma not_and_or : forall P Q:Prop, ~ (P /\ Q) -> ~ P \/ ~ Q.
Lemma or_not_and : forall P Q:Prop, ~ P \/ ~ Q -> ~ (P /\ Q).
Lemma not_or_and : forall P Q:Prop, ~ (P \/ Q) -> ~ P /\ ~ Q.
Lemma and_not_or : forall P Q:Prop, ~ P /\ ~ Q -> ~ (P \/ Q).
Lemma imply_and_or : forall P Q:Prop, (P -> Q) -> P \/ Q -> Q.
Lemma imply_and_or2 : forall P Q R:Prop, (P -> Q) -> P \/ R -> Q \/ R.
Lemma proof_irrelevance : forall (P:Prop) (p1 p2:P), p1 = p2.
 *)


(** *** 来自 Coq.Logic.EqdepFacts *)

(* 相等性证明是唯一的 *)
(* Check UIP. *)
(* : forall (U : Type) (x y : U) (p1 p2 : x = y), p1 = p2 *)

(* 相等性证明是自反的 *)
(* Check UIP_refl. *)
(* : forall (U : Type) (x : U) (p : x = x), p = eq_refl *)



(** ** 新的性质 *)


(* P \/ P = P *)
Lemma or_same : forall (P : Prop), P \/ P -> P.
Proof. intros. destruct H; auto. Qed.

(* (A -> B \/ C) <-> (A -> B) \/ (A -> C). *)
Lemma impl_or_distr : forall A B C : Prop, (A -> B \/ C) <-> (A -> B) \/ (A -> C).
Proof.
  intros; split; intros.
  - apply imply_to_or in H. destruct H.
    + left. intros. easy.
    + destruct H; auto.
  - destruct H; auto.
Qed.

(* (A -> B \/ C) = (A -> B) \/ (A -> C). *)
Lemma impl_or_distr_eq : forall A B C : Prop, (A -> B \/ C) = ((A -> B) \/ (A -> C)).
Proof. intros. apply propositional_extensionality. apply impl_or_distr. Qed.


(* 如果互相包含，则两个集合相等 *)
Lemma extensionality_ensembles : forall (U : Type) (A B : U -> Prop),
    (forall x : U, A x -> B x) /\ (forall x : U, B x -> A x) -> A = B.
Proof. intros.
  (* 集合相等的外延性公理 *) apply Extensionality_Ensembles. auto. Qed.


(** *** Good exercises for logic *)
Section exercise_forall_exist_not.

  (** Existing lemmas
ex_not_not_all: forall (U : Type) (P : U -> Prop), (exists n : U, ~ P n) -> ~ (forall n : U, P n)
not_all_ex_not: forall (U : Type) (P : U -> Prop), ~ (forall n : U, P n) -> exists n : U, ~ P n
not_all_not_ex: forall (U : Type) (P : U -> Prop), ~ (forall n : U, ~ P n) -> exists n : U, P n
  *)

  (** These lemmas needn't axiom *)

  Lemma my_all_not_not_ex : forall (U : Type) (P : U -> Prop),
      (forall n : U, ~ P n) -> ~ (exists n : U, P n).
  Proof. intros. intro. destruct H0. specialize (H x). easy. Qed.
  
  Lemma my_ex_not_not_all : forall (U : Type) (P : U -> Prop),
      (exists n : U, ~ P n) -> ~ (forall n : U, P n).
  Proof. intros. intro. destruct H. specialize (H0 x). easy. Qed.

  (** These lemmas need axiom in Classic Logic *)

  Lemma my_reverse_proof : forall P Q : Prop, (~Q -> ~P) -> (P -> Q).
  Proof. Abort.
  
  Lemma my_not_ex_not_all:
    forall (U : Type) (P : U -> Prop), ~ (exists n : U, ~ P n) -> forall n : U, P n.
  Proof. Abort.

  Lemma my_not_ex_all_not:
    forall (U : Type) (P : U -> Prop), ~ (exists n : U, P n) -> forall n : U, ~ P n.
  Proof. Abort.
  
  Lemma my_not_all_ex_not: forall (U : Type) (P : U -> Prop),
      ~ (forall n : U, P n) -> exists n : U, ~ P n.
  Proof. Abort.

  Lemma my_not_all_not_ex: forall (U : Type) (P : U -> Prop),
      ~ (forall n : U, ~ P n) -> exists n : U, P n.
  Proof. Abort.
  
End exercise_forall_exist_not.
