(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : finite set of natural numbers
  author    : Zhengpu Shi
  date      : 2023.12

  remark    :
  1. 比较自然数的判定程序
     已有的程序
     le_gt_dec     : forall n m : nat, {n <= m} + {n > m}
     lt_eq_lt_dec  : forall n m : nat, {n < m} + {n = m} + {m < n}
     新增的程序
     lt_ge_dec     : forall n m : nat, {n < m} + {n >= m}

  2. fin 的几种实现方案
     (1). 使用 unit 来表示 fin 0
        定义：
        Definition fin (n : nat) :=
        match n with O => unit | _ => {i : nat | i < n} end.
        特点：
        1. fin2nat 中，将 fin 0 处理为 0
           注意，由于这个特殊处理，往往需要处理 n = 0 和 n > 0 这两类问题。
           实际使用时，部分引理需要 0 < n 时成立。
           同时，部分引理需要 i < n 时成立。
           由于很多很自然成立的引理需要额外的前提约束，非常不直观。
           最根本原因是 fin2nat和nat2fin不是一一映射。
        2. nat2fin 不需要使用option
        3. 由于fin是依赖类型，抽取出的Ocaml代码含有 Obj.magic
     (2). fin 0 集合中没有元素
        定义：
        Definition fin (n : nat) := {i | i < n}.
        特点：
        1. fin2nat 不需要特殊处理
        2. nat2fin 使用option
           由于 option 的存在，使得表达式较为复杂。
        3. sig类型本质上不是依赖类型，抽取的Ocaml代码是正常的。
        4. 多数引理不需要额外的前提就能成立。
           比如 vnth 不会越界。
     (3). 多使用一个下标
        定义：
        Definition fin (n : nat) := {i | i <= n}
        特点：
        1. fin 0 有一个元素，fin 1 有两个元素，fin n 有 S n 个元素。
           所以该集合永远不为空。
           同时，fin2nat, nat2fin 也成为了全函数，并且代码抽取也是正常的。
        3. 已知的一些问题
           由于fin用于访问vec，所以 vec 0 也修改为含有1个元素的向量。
           所以，vec n 含有 S n 个元素。
           这就导致 vec 3 实际上是 4 个元素，很奇怪。
        4. 一个思路是，只修改 fin，而不修改 vec, seq 等模块。
           fin 0 = {0}       丢弃 {0}
           fin 1 = {0,1}     丢弃 {1}
           fin 2 = {0,1,2}   丢弃 {2}
           在与 vec 交互时，人为的丢弃最大的那个值。
 *)

Require Export PropExtensionality.
Require Export Arith Lia.
Require Export ListExt.
Require Export NatExt.
Require Import Extraction.

(* #[export] Hint Rewrite *)
(*   map_length *)
(*   seq_length *)
(*   : fin. *)


(* ######################################################################### *)
(** * _fin_ type and basic operations *)

(** ** Type of fin *)

(* Declare Scope fin_scope. *)
(* Delimit Scope fin_scope with fin. *)

Open Scope nat_scope.
(* Open Scope fin_scope. *)

(* Notation "[ | i ]" := (exist _ i _) (format "[ | i ]"). *)

(** Definition of fin type *)
(* Notation fin n := {i | i < n}. *)
(* Definition fin (n : nat) := {i | i < n}. *)
(* 借鉴ordinal，使用 Inductive 可避免因过于多态的 sig 类型而带来的不必要的复杂性 *)
Inductive fin (n : nat) := Fin (i : nat) (E : i < n).
(* 借鉴了 ordinal 的记号 *)
Notation "''I_' n" := (fin n)
                        (at level 8, n at level 2, format "''I_' n").
Arguments Fin {n}.

Lemma fin_n_gt0 :forall {n} (i : 'I_n), 0 < n.
Proof.
  intros. destruct i as [i E]. destruct n. lia. lia.
Qed.

Lemma fin0_False : 'I_0 -> False.
Proof. intros. inversion H. lia. Qed.

Lemma fin_eq_iff : forall {n} i j Ei Ej, i = j <-> @Fin n i Ei = @Fin n j Ej.
Proof.
  intros. split; intros.
  - subst. f_equal. apply proof_irrelevance.
  - inversion H. auto.
Qed.


(** ** [fin] to [nat] *)

(** Convert from [fin] to [nat] *)
Definition fin2nat {n} (f : 'I_n) := let '(Fin i _) := f in i.
Coercion fin2nat : fin >-> nat.

(** fin2nat i = fin2nat j <-> i = j *)
Lemma fin2nat_eq_iff : forall {n} (i j : 'I_n), fin2nat i = fin2nat j <-> i = j.
Proof.
  intros. destruct i,j. unfold fin2nat.
  split; intros; subst. apply fin_eq_iff; auto. apply fin_eq_iff in H. auto.
Qed.

(** fin2nat i <> fin2nat j <-> i <> j *)
Lemma fin2nat_neq_iff : forall {n} (i j : 'I_n), fin2nat i <> fin2nat j <-> i <> j.
Proof. intros. rewrite fin2nat_eq_iff. tauto. Qed.

Lemma fin2nat_lt : forall {n} (i : 'I_n), i < n.
Proof. intros. destruct i; simpl. auto. Qed.

Lemma fin2nat_lt_Sn : forall {n} (i : 'I_n), i < S n.
Proof. intros. pose proof (fin2nat_lt i). auto. Qed.

Lemma fin2nat_Fin : forall {n} i (H : i < n), fin2nat (Fin i H) = i.
Proof. auto. Qed.
Hint Resolve fin2nat_Fin : fin.

Lemma fin_fin2nat : forall {n} (i : 'I_n) (E : i < n), Fin i E = i.
Proof. intros. destruct i; simpl. apply fin_eq_iff; auto. Qed.

Hint Resolve fin_fin2nat : fin.


(* simplify "fin2nat i {=, <>, <, >, <=} fin2nat j" in context *)
Ltac fin2nat :=
  repeat
    (match goal with
     | H : fin2nat ?i = fin2nat ?j |- _ => apply fin2nat_eq_iff in H; rewrite H in *
     | H : fin2nat ?i <> fin2nat ?j |- _ => apply fin2nat_neq_iff in H
     | |- fin2nat ?i = fin2nat ?j => apply fin2nat_eq_iff
     | |- fin2nat ?i <> fin2nat ?j => apply fin2nat_neq_iff
     end).


(** ** [fin0] *)

(** A default entry of `fin` *)
Definition fin0 {n : nat} : 'I_(S n) := Fin 0 (Nat.lt_0_succ _).

(** i <> fin0 -> 0 < fin2nat i *)
Lemma fin2nat_gt0_if_neq0 : forall {n} (i : 'I_(S n)), i <> fin0 -> 0 < i.
Proof.
  intros. unfold fin2nat,fin0 in *. destruct i.
  assert (i <> 0). intro. destruct H. apply fin_eq_iff. auto. lia.
Qed.

(** 0 < fin2nat i -> i <> fin0 *)
Lemma fin2nat_gt0_imply_neq0 : forall {n} (i : 'I_(S n)), 0 < i -> i <> fin0.
Proof.
  intros. unfold fin2nat,fin0 in *. destruct i.
  intro. apply fin_eq_iff in H0. lia.
Qed.


(** ** [fin1] *)

(** 'I_1 is unique *)
Lemma fin1_uniq : forall (i : 'I_1), i = fin0.
Proof. intros. destruct i. apply fin_eq_iff. lia. Qed.


(** ** [nat] to ['I_(S n)] *)

(** Convert from nat to 'I_(S n). If `i >= S n` then {0} *)
Definition nat2finS {n} (i : nat) : 'I_(S n).
  destruct (i ??< S n)%nat as [E|E].
  - apply (Fin i E).
  - apply (Fin 0 (Nat.lt_0_succ _)).
    (* apply fin0. *)
Defined.
Notation "# i" := (nat2finS i) (at level 1, format "# i").

(* OLD definition, (directly define it, without Dec structures) *)
Definition nat2finS' {n} (i : nat) : 'I_(S n) :=
  match lt_dec i (S n) with
  | left H => Fin i H
  | _ => Fin 0 (Nat.lt_0_succ _)
  end.

Lemma nat2finS'_eq_nat2finS : forall n i, @nat2finS' n i = @nat2finS n i.
Proof.
  intros. unfold nat2finS', nat2finS.
  destruct lt_dec,(_??<_); try lia; f_equal. apply proof_irrelevance.
Qed.

Lemma nat2finS_eq : forall n i (E : i < S n), nat2finS i = Fin i E.
Proof.
  intros. unfold nat2finS. destruct (_??<_)%nat; try lia. apply fin_eq_iff; auto.
Qed.

(** nat2finS (fin2nat i) = i *)
Lemma nat2finS_fin2nat : forall n (i : 'I_(S n)), nat2finS i = i.
Proof.
  intros. destruct i; simpl. rewrite nat2finS_eq with (E:=E); auto.
Qed.
Hint Rewrite nat2finS_fin2nat : fin.

(** fin2nat (nat2finS i) = i  *)
Lemma fin2nat_nat2finS : forall n i, i < (S n) -> fin2nat (@nat2finS n i) = i.
Proof.
  intros. rewrite nat2finS_eq with (E:=H); auto.
Qed.
Hint Rewrite fin2nat_nat2finS : fin.

(** {i<n} <> nat2finS n -> fin2nat i < n *)
Lemma nat2finS_neq_imply_lt : forall {n} (i : 'I_(S n)),
    i <> nat2finS n -> i < n.
Proof.
  intros. pose proof (fin2nat_lt i).
  assert (fin2nat i <> n); try lia.
  intro. destruct H. destruct i; simpl in *. subst.
  rewrite nat2finS_eq with (E:=H0); auto. apply fin_eq_iff; auto.
Qed.

(** fin2nat i = n -> #n = i *)
Lemma fin2nat_imply_nat2finS : forall n (i : 'I_(S n)), fin2nat i = n -> #n = i.
Proof.
  intros. erewrite nat2finS_eq. destruct i. apply fin_eq_iff; auto.
  Unshelve. auto.
Qed.

(** fin2nat i <> n -> fin2nat i < n*)
Lemma fin2nat_neq_n_imply_lt : forall n (i : 'I_(S n)), fin2nat i <> n -> fin2nat i < n.
Proof. intros. pose proof (fin2nat_lt i). lia. Qed.

Lemma nat2finS_inj : forall n i j,
    i < n -> j < n -> @nat2finS n i = @nat2finS n j -> i = j.
Proof.
  intros. unfold nat2finS in *. destruct (i ??< S n), (j ??< S n); try lia.
  inv H1. auto.
Qed.


(** ** [nat] to ['I_n] *)

(** Convert from [nat] to [fin] *)
Definition nat2fin {n} (i : nat) (E : i < n) : 'I_n := Fin i E.

Lemma nat2fin_fin2nat : forall n (f : 'I_n) (E: fin2nat f < n),
    nat2fin (fin2nat f) E = f.
Proof. intros. unfold nat2fin,fin2nat. destruct f. apply fin_eq_iff; auto. Qed.
Hint Rewrite nat2fin_fin2nat : fin.

Lemma fin2nat_nat2fin : forall n i (E: i < n), (fin2nat (nat2fin i E)) = i.
Proof. intros. auto. Qed.
Hint Rewrite fin2nat_nat2fin : fin.

Lemma fin2nat_imply_nat2fin : forall {n} (i : 'I_n) j (H: j < n),
    fin2nat i = j -> nat2fin j H = i.
Proof.
  intros. unfold nat2fin, fin2nat in *. destruct i. apply fin_eq_iff; auto.
Qed.

Lemma nat2fin_imply_fin2nat : forall {n} (i : 'I_n) j (E: j < n),
    nat2fin j E = i -> fin2nat i = j.
Proof.
  intros. unfold nat2fin, fin2nat in *. destruct i. apply fin_eq_iff in H; auto.
Qed.

Lemma nat2fin_iff_fin2nat : forall {n} (i : 'I_n) j (E: j < n),
    nat2fin j E = i <-> fin2nat i = j.
Proof.
  intros; split; intros. apply nat2fin_imply_fin2nat in H; auto.
  apply fin2nat_imply_nat2fin; auto.
Qed.


(** ** Tactic for fin *)

(* simplify and solve proofs about "fin" *)
Ltac fin :=
  repeat
    (intros;
     auto with fin;
     try autorewrite with fin in *;
     try
       (let E := fresh "E" in
        match goal with
        (* (i : 'I_n) (H:n=0) |- _ ==> (i : 'I_0) |- _ *)
        | [i : fin ?n, H: ?n = 0 |- _]     => subst
        (* fin 0 |- _ ==> solve it *)
        | i : 'I_0 |- _  => exfalso; apply (fin0_False i)
        (* fin2nat (i:fin n) < n ==> solve it *)
        | [i : fin ?n |- fin2nat ?i < ?n]  => apply fin2nat_lt
        (* i : fin n |- fin2nat i < S n ==> solve it *)
        | i : fin ?n |- fin2nat ?i < S ?n =>
            pose proof (fin2nat_lt i) as E; lia; clear E
        (* i : fin n |- S (fin2nat i) < S n ==> solve it *)
        | i : fin ?n |- S (fin2nat ?i) < S ?n =>
            pose proof (fin2nat_lt i) as E; lia; clear E
        (* fin2nat i = fin2nat j, i <> j |- _ ==> solve it *)
        | H1 : fin2nat ?i = fin2nat ?j, H2 : ?i <> ?j |- _ =>
            apply fin2nat_eq_iff in H1; rewrite H1 in H2; easy
        | H1 : fin2nat ?i = fin2nat ?j, H2 : ?j <> ?i |- _ =>
            apply fin2nat_eq_iff in H1; rewrite H1 in H2; easy
        (* fin2nat i = fin2nat j |- i = j ==> solve it *)
        | H : fin2nat ?i = fin2nat ?j |- ?i = ?j => 
            apply fin2nat_eq_iff in H; rewrite H; easy
        | H : fin2nat ?i = fin2nat ?j |- ?j = ?i =>
            apply fin2nat_eq_iff in H; rewrite H; easy
        (* fin2nat i <> fin2nat j |- i <> j ==> solve it *)
        | H : fin2nat ?i <> fin2nat ?j |- ?i <> ?j => apply fin2nat_neq_iff in H; easy
        | H : fin2nat ?i <> fin2nat ?j |- ?j <> ?i => apply fin2nat_neq_iff in H; easy
        (* fin2nat i = n |- #n = i ==> solve it *)
        | H : fin2nat ?i = ?n |- nat2finS ?n = ?i =>
            apply (fin2nat_imply_nat2finS n i H)
        | H : fin2nat ?i = ?n |- ?i = nat2finS ?n =>
            symmetry; apply (fin2nat_imply_nat2finS n i H)
        (* fin2nat i <> n |- fin2nat i < n ==> solve it*)
        | [i : 'I_(S ?n), H : fin2nat ?i <> ?n |- fin2nat ?i < ?n] =>
            apply fin2nat_neq_n_imply_lt; auto
        (* destruct the pattern about "??=, ??<, ??<=" *)
        | [ H : context [(?i ??= ?j)%nat] |- _]  => destruct (i ??= j)%nat as [E|E]
        | [ |- context [(?i ??= ?j)%nat]]        => destruct (i ??= j)%nat as [E|E]
        | [ H : context [(?i ??< ?j)%nat] |- _]  => destruct (i ??< j)%nat as [E|E]
        | [ |- context [(?i ??< ?j)%nat]]        => destruct (i ??< j)%nat as [E|E]
        | [ H : context [(?i ??<= ?j)%nat] |- _] => destruct (i ??<= j)%nat as [E|E]
        | [ |- context [(?i ??<= ?j)%nat]]       => destruct (i ??<= j)%nat as [E|E]
        (* f i = f j ==> i = j *)
        | |- ?f ?i = ?f ?j => f_equal
        (* a = b *)
        | |- ?a = ?b =>
            match type of a with
            (* (i : 'I_n) = (j : 'I_n) ==> try to solve it *)
            | fin ?n => try apply fin_eq_iff
            (* Prop *)
            | ?t => match type of t with | Prop => apply proof_irrelevance end
            end
        end);
     try
       (match goal with
        (* (i : 'I_n) = (j : 'I_n) |- _ ==> subst it *)
        | H : ?i = ?j |- _ => match type of i with | fin ?n => try rewrite H in * end
        end);
     auto with fin; try reflexivity; try easy; try lia; try ring
    ).



(* ######################################################################### *)
(** * Cast between _fin_ terms *)

(** ** Cast between two [fin] type with actual equal range *)

(** Cast from ['I_n] type to ['I_m] type if [n = m] *)
Definition cast_fin {n m} (H : n = m) (i : 'I_n) : 'I_m.
  subst. apply i.
Defined.


(** ** ['I_n] to ['I_m] *)

(** Convert from ['I_n] to ['I_m] *)
Definition fin2fin n m (i : 'I_n) (E : fin2nat i < m) : 'I_m :=
  nat2fin (fin2nat i) E.

Lemma fin2nat_fin2fin : forall n m (i : 'I_n) (E : fin2nat i < m),
    fin2nat (fin2fin n m i E) = fin2nat i.
Proof. intros. unfold fin2fin,fin2nat,nat2fin. auto. Qed.
Hint Rewrite fin2nat_fin2fin : fin.

Lemma fin2fin_fin2fin :
  forall m n (i : 'I_m) (E1 : fin2nat i < n) (E2 : fin2nat (fin2fin m n i E1) < m),
    fin2fin n m (fin2fin m n i E1) E2 = i.
Proof.
  intros. unfold fin2fin,fin2nat,nat2fin. destruct i. apply fin_eq_iff; auto.
Qed.

(** ** [Fin n i] + [Fin n k] -> [Fin n (i+k)] *)

(** {i<n} + {k<n} -> (i+k<n) ? {i+k<n} : {0<n} *)
Definition fSameRangeAdd {n : nat} (i k : 'I_n) : 'I_(n).
  destruct (fin2nat i + fin2nat k ??< n)%nat as [E|E].
  - refine (nat2fin (fin2nat i + fin2nat k) E).
  - refine (nat2fin 0 _). destruct (n ??= 0)%nat.
    + subst. fin.
    + apply neq_0_lt_stt; auto.
Defined.

Lemma fin2nat_fSameRangeAdd : forall n (i k : 'I_n),
    fin2nat (fSameRangeAdd i k) =
      if (fin2nat i + fin2nat k ??< n)%nat then (fin2nat i + fin2nat k) else 0.
Proof. intros. unfold fSameRangeAdd. fin. Qed.
Hint Rewrite fin2nat_fSameRangeAdd : fin.

(** ** [Fin n i] + [Fin n k] -> [Fin n (i-k)] *)

(** {i<n} - {k<n} -> {i-k<n} *)
Definition fSameRangeSub {n : nat} (i k : 'I_n) : 'I_(n).
  refine (nat2fin (fin2nat i - fin2nat k) _).
  pose proof (fin2nat_lt i). apply Nat.le_lt_trans with (fin2nat i).
  apply Nat.le_sub_l. auto.
Defined.

Lemma fin2nat_fSameRangeSub : forall n (i k : 'I_n),
    fin2nat (fSameRangeSub i k) = fin2nat i - fin2nat k.
Proof. intros. unfold fSameRangeSub. simpl. auto. Qed.
Hint Rewrite fin2nat_fSameRangeSub : fin.

(** ** [Fin n i] -> [Fin n (S i)] *)

(** {i<n} -> (S i<n) ? {S i<n} : {i<n} *)
Definition fSameRangeSucc {n : nat} (i : 'I_n) : 'I_(n).
  destruct (S (fin2nat i) ??< n)%nat as [H|H].
  - refine (nat2fin (S (fin2nat i)) H).
  - apply i.
Defined.

Lemma fin2nat_fSameRangeSucc : forall n (i : 'I_n),
    fin2nat (fSameRangeSucc i) =
      if (S (fin2nat i) ??< n)%nat then S (fin2nat i) else fin2nat i.
Proof. intros. unfold fSameRangeSucc. fin. Qed.
Hint Rewrite fin2nat_fSameRangeSucc : fin.

(** ** [Fin n i] -> [Fin n (pred i)] *)

(** {i<n} -> (0 < i) ? {pred i<n} : {i<n} *)
Definition fSameRangePred {n : nat} (i : 'I_n) : 'I_n.
  destruct (0 ??< fin2nat i)%nat.
  - refine (nat2fin (pred (fin2nat i)) _). apply Nat.lt_lt_pred. apply fin2nat_lt.
  - apply i.
Defined.

Lemma fin2nat_fSameRangePred : forall n (i : 'I_n),
    fin2nat (fSameRangePred i) =
      if (0 ??< fin2nat i)%nat then pred (fin2nat i) else fin2nat i.
Proof. intros. unfold fSameRangePred. fin. Qed.
Hint Rewrite fin2nat_fSameRangePred : fin.

(** ** [Fin n i] -> [Fin n (loop-shift-left i with k)] *)

(** Loop shift left {i<n} with {k<n}. Eg: 0 1 2 =1=> 1 2 0  *)
Definition fSameRangeLSL {n : nat} (i k : 'I_n) : 'I_(n).
  destruct (n ??= 0)%nat.
  - subst; fin.
  - refine (nat2fin ((n + fin2nat i + fin2nat k) mod n) _).
    apply Nat.mod_upper_bound. auto.
Defined.

Lemma fin2nat_fSameRangeLSL : forall {n} (i k : 'I_n),
    fin2nat (fSameRangeLSL i k) = (n + fin2nat i + fin2nat k) mod n.
Proof. intros. unfold fSameRangeLSL. fin. Qed.

(** ** [Fin n i] -> [Fin n (loop-shift-right i with k)] *)

(** Loop shift right : {i<n} <-> {k<n}. Eg: 0 1 2 =1=> 2 0 1  *)
Definition fSameRangeLSR {n : nat} (i k : 'I_n) : 'I_(n).
  destruct (n ??= 0)%nat.
  - subst; fin.
  - refine (nat2fin ((n + fin2nat i - fin2nat k) mod n) _).
    apply Nat.mod_upper_bound. auto.
Defined.

Lemma fin2nat_fSameRangeLSR : forall {n} (i k : 'I_n),
    fin2nat (fSameRangeLSR i k) = (n + fin2nat i - fin2nat k) mod n.
Proof. intros. unfold fSameRangeLSR. fin. Qed.

(** ** [Fin n i] -> [Fin n (n - i)] *)

(** {i < n} -> {n - i < n}  *)
Definition fSameRangeRemain {n} (i : 'I_n) (E : 0 < fin2nat i) : 'I_n.
  destruct (n ??= 0)%nat.
  - subst; fin.
  - refine (nat2fin (n - fin2nat i) _).
    apply nat_sub_lt; auto. apply neq_0_lt_stt; auto.
Defined.

Lemma fin2nat_fSameRangeRemain : forall {n} (i : 'I_n) (E : 0 < fin2nat i),
    fin2nat (fSameRangeRemain i E) = n - fin2nat i.
Proof. intros. unfold fSameRangeRemain. fin. Qed.

(** ** [Fin n i] -> [Fin (S n) i] *)

(** {i<n} -> {i<S n} *)
Definition fSuccRange {n} (i : 'I_n) : 'I_(S n).
  refine (nat2finS (fin2nat i)).
Defined.

Lemma fSuccRange_inj : forall n (i j : 'I_n), fSuccRange i = fSuccRange j -> i = j.
Proof.
  intros. destruct i,j. unfold fSuccRange in H. fin.
  apply nat2finS_inj in H; auto.
Qed.
Hint Resolve fSuccRange_inj : fin.

Lemma fin2nat_fSuccRange : forall n (i : 'I_n),
    fin2nat (@fSuccRange n i) = fin2nat i.
Proof.
  intros. unfold fSuccRange. apply fin2nat_nat2finS.
  pose proof (fin2nat_lt i). lia.
Qed.
Hint Rewrite fin2nat_fSuccRange : fin.

Lemma fSuccRange_nat2fin : forall n (i : nat) (E : i < n) (E0 : i < S n),
  fSuccRange (nat2fin i E) = nat2fin i E0.
Proof. intros. unfold fSuccRange, nat2finS. simpl. fin. Qed.
Hint Rewrite fSuccRange_nat2fin : fin.

(** ** [Fin (S n) i] -> [Fin n i] *)

(** {i<S n} -> {i<n} *)
Definition fPredRange {n} (i : 'I_(S n)) (H : i < n) : 'I_n :=
  nat2fin (fin2nat i) H.

Lemma fin2nat_fPredRange : forall n (i : 'I_(S n)) (E : i < n),
    fin2nat (@fPredRange n i E) = fin2nat i.
Proof. intros. unfold fPredRange. simpl. auto. Qed.
Hint Rewrite fin2nat_fPredRange : fin.

Lemma fSuccRange_fPredRange : forall n (i : 'I_(S n)) (E : i < n),
    fSuccRange (fPredRange i E) = i.
Proof.
  intros. destruct i. unfold fSuccRange,fPredRange,nat2finS; simpl. fin.
Qed.
Hint Rewrite fSuccRange_fPredRange : fin.

Lemma fPredRange_fSuccRange : forall n (i : 'I_n) (E: fin2nat (fSuccRange i) < n),
    fPredRange (fSuccRange i) E = i.
Proof.
  intros. destruct i as [i Hi].
  unfold fSuccRange,fPredRange,nat2finS in *; simpl in *. fin.
Qed.
Hint Rewrite fPredRange_fSuccRange : fin.

(** ** [Fin n i] -> [Fin (m + n) i] *)

(** {i < n} -> {i < m + n} *)
Definition fAddRangeL {m n} (i : 'I_n) : 'I_(m + n).
  refine (nat2fin (fin2nat i) _).
  apply Nat.lt_lt_add_l. fin.
Defined.

Lemma fin2nat_fAddRangeL : forall m n (i : 'I_n),
    fin2nat (@fAddRangeL m n i) = fin2nat i.
Proof. intros. auto. Qed.
Hint Rewrite fin2nat_fAddRangeL : fin.

(** ** [Fin (m + n) i] -> [Fin n i] *)

(** {i < m + n} -> {i < n} *)
Definition fAddRangeL' {m n} (i : 'I_(m + n)) (E : fin2nat i < n) : 'I_n :=
  nat2fin (fin2nat i) E.

Lemma fin2nat_fAddRangeL' : forall {m n} (i : 'I_(m + n)) (E : fin2nat i < n),
    fin2nat (fAddRangeL' i E) = fin2nat i.
Proof. intros. auto. Qed.

Lemma fAddRangeL_fAddRangeL' : forall {m n} (i : 'I_(m+n)) (E : fin2nat i < n),
    fAddRangeL (fAddRangeL' i E) = i.
Proof.
  intros. unfold fAddRangeL, fAddRangeL'. simpl.
  destruct i as [i Hi]. apply fin_eq_iff; auto.
Qed.

(** ** [Fin m i] -> [Fin (m + n) i] *)

(** {i < m} -> {i < m + n} *)
Definition fAddRangeR {m n} (i : 'I_m) : 'I_(m + n).
  refine (nat2fin (fin2nat i) _).
  apply Nat.lt_lt_add_r. apply fin2nat_lt.
Defined.

Lemma fin2nat_fAddRangeR : forall m n (i : 'I_m),
    fin2nat (@fAddRangeR m n i) = fin2nat i.
Proof. intros. auto. Qed.
Hint Rewrite fin2nat_fAddRangeR : fin.

(** ** [Fin (m + n) i] -> [Fin m i] *)

(** {i < m + n} -> {i < m} *)
Definition fAddRangeR' {m n} (i : 'I_(m + n)) (E : fin2nat i < m) : 'I_m :=
  nat2fin (fin2nat i) E.

Lemma fin2nat_fAddRangeR' : forall {m n} (i : 'I_(m+n)) (E : fin2nat i < m),
    fin2nat (fAddRangeR' i E) = fin2nat i.
Proof. intros. auto. Qed.

Lemma fAddRangeR_fAddRangeR' : forall m n (i : 'I_(m+n)) (E : fin2nat i < m),
    fAddRangeR (fAddRangeR' i E) = i.
Proof.
  intros. unfold fAddRangeR, fAddRangeR'. simpl.
  destruct i as [i Hi]. apply fin_eq_iff; auto.
Qed.
Hint Rewrite fAddRangeR_fAddRangeR' : fin.

Lemma fAddRangeR'_fAddRangeR : forall m n (i : 'I_m) (E : fin2nat i < m),
    @fAddRangeR' m n (fAddRangeR i) E = i.
Proof.
  intros. unfold fAddRangeR, fAddRangeR'. simpl.
  rewrite nat2fin_fin2nat. auto.
Qed.
Hint Rewrite fAddRangeR'_fAddRangeR : fin.

(** ** [Fin n i] -> [Fin (m + n) (m + i)] *)

(** {i < n} -> {m + i < m + n} *)
Definition fAddRangeAddL {m n} (i : 'I_n) : 'I_(m + n).
  refine (nat2fin (m + fin2nat i) _).
  apply Nat.add_lt_mono_l. apply fin2nat_lt.
Defined.

Lemma fin2nat_fAddRangeAddL : forall m n (i : 'I_n),
    fin2nat (@fAddRangeAddL m n i) = m + fin2nat i.
Proof. intros. auto. Qed.
Hint Rewrite fin2nat_fAddRangeAddL : fin.

(** ** [Fin (m + n) (m + i)] -> [Fin n i] *)

(** {m + i < m + n} -> {i < n} *)
Definition fAddRangeAddL' {m n} (i : 'I_(m + n)) (E : m <= fin2nat i) : 'I_n.
  refine (nat2fin (fin2nat i - m) _).
  pose proof (fin2nat_lt i).
  apply le_ltAdd_imply_subLt_l; auto.
Defined.

Lemma fin2nat_fAddRangeAddL' : forall {m n} (i : 'I_(m + n)) (E : m <= fin2nat i),
    fin2nat (@fAddRangeAddL' m n i E) = fin2nat i - m.
Proof. intros. auto. Qed.

Lemma fAddRangeAddL_fAddRangeAddL' :
  forall m n (i : 'I_(m + n)) (E : m <= fin2nat i),
    fAddRangeAddL (fAddRangeAddL' i E) = i.
Proof.
  intros. unfold fAddRangeAddL, fAddRangeAddL'. simpl.
  destruct i as [i Hi]. simpl in *. apply fin_eq_iff; auto. lia.
Qed.
Hint Rewrite fAddRangeAddL_fAddRangeAddL' : fin.

Lemma fAddRangeAddL'_fAddRangeAddL :
  forall m n (i : 'I_n) (E : m <= fin2nat (fAddRangeAddL i)),
    @fAddRangeAddL' m n (fAddRangeAddL i) E = i.
Proof.
  intros. unfold fAddRangeAddL, fAddRangeAddL'. simpl.
  destruct i as [i Ei]. simpl in *. apply fin_eq_iff; auto. lia.
Qed.
Hint Rewrite fAddRangeAddL'_fAddRangeAddL : fin.
  
(** ** [Fin m i] -> [Fin (m + n) (i + n)] *)

(** {i < m} -> {i + n < m + n} *)
Definition fAddRangeAddR {m n} (i : 'I_m) : 'I_(m + n).
  refine (nat2fin (fin2nat i + n) _).
  apply Nat.add_lt_mono_r. apply fin2nat_lt.
Defined.

Lemma fin2nat_fAddRangeAddR : forall m n (i : 'I_m),
    fin2nat (@fAddRangeAddR m n i) = fin2nat i + n.
Proof. intros. auto. Qed.
Hint Rewrite fin2nat_fAddRangeAddR : fin.
  
(** ** [Fin (m + n) (i + n)] -> [Fin m i] *)

(** {i + n < m + n} -> {i < m} *)
Definition fAddRangeAddR' {m n} (i : 'I_(m + n)) (E : n <= fin2nat i) : 'I_m.
  refine (nat2fin (fin2nat i - n) _).
  pose proof (fin2nat_lt i). apply le_ltAdd_imply_subLt_r; auto.
Defined.

Lemma fin2nat_fAddRangeAddR' : forall {m n} (i : 'I_(m + n)) (E : n <= fin2nat i),
    fin2nat (@fAddRangeAddR' m n i E) = fin2nat i - n.
Proof. intros. auto. Qed.

Lemma fAddRangeAddR_fAddRangeAddR' :
  forall m n (i : 'I_(m + n)) (E : n <= fin2nat i),
    fAddRangeAddR (@fAddRangeAddR' m n i E) = i.
Proof.
  intros. unfold fAddRangeAddR, fAddRangeAddR'. simpl.
  destruct i as [i Hi]. simpl in *. apply fin_eq_iff; auto. lia.
Qed.
Hint Rewrite fAddRangeAddR_fAddRangeAddR' : fin.

Lemma fAddRangeAddR'_fAddRangeAddR :
  forall m n (i : 'I_m) (E : n <= fin2nat (fAddRangeAddR i)),
    @fAddRangeAddR' m n (fAddRangeAddR i) E = i.
Proof.
  intros. unfold fAddRangeAddR, fAddRangeAddR'. simpl.
  destruct i as [i Hi]. simpl in *. apply fin_eq_iff; auto. lia.
Qed.
Hint Rewrite fAddRangeAddR'_fAddRangeAddR : fin.

(** ** [Fin (S n) (S i)] -> [Fin n i] *)

(** {S i < S n} -> {i < n} *)
Definition fPredRangeP {n} (i : 'I_(S n)) (E : 0 < i) : 'I_n.
  refine (nat2fin (pred (fin2nat i)) _).
  destruct i; simpl in *. apply pred_lt; auto.
Defined.

Lemma fin2nat_fPredRangeP : forall n (i : 'I_(S n)) (E : 0 < fin2nat i),
    fin2nat (fPredRangeP i E) = pred (fin2nat i).
Proof. intros. unfold fPredRangeP. apply fin2nat_nat2fin. Qed.
Hint Rewrite fin2nat_fPredRangeP : fin.

(** ** [Fin n i] -> [Fin (S n) (S i)] *)

(** {i < n} -> {S i < S n} *)
Definition fSuccRangeS {n} (i : 'I_n) : 'I_(S n).
  refine (nat2fin (S (fin2nat i)) _).
  pose proof (fin2nat_lt i).
  rewrite <- Nat.succ_lt_mono; auto.
Defined.

Lemma fin2nat_fSuccRangeS : forall n (i : 'I_n),
    fin2nat (fSuccRangeS i) = S (fin2nat i).
Proof. intros. unfold fSuccRangeS. simpl. auto. Qed.
Hint Rewrite fin2nat_fSuccRangeS : fin.

Lemma fSuccRangeS_fPredRangeP : forall n (i : 'I_(S n)) (E : 0 < fin2nat i),
    fSuccRangeS (fPredRangeP i E) = i.
Proof.
  intros. destruct i. cbv. cbv in E. destruct i; try lia. apply fin_eq_iff; auto.
Qed.
Hint Rewrite fSuccRangeS_fPredRangeP : fin.

Lemma fPredRangeP_fSuccRangeS :
  forall n (i : 'I_n) (E : 0 < fin2nat (fSuccRangeS i)),
    fPredRangeP (fSuccRangeS i) E = i.
Proof.
  intros. destruct i as [i Hi]. cbv. apply fin_eq_iff; auto.
Qed.
Hint Rewrite fPredRangeP_fSuccRangeS : fin.

Lemma fin2nat_fSuccRangeS_gt0 : forall {n} (i : 'I_n),
    0 < fin2nat (fSuccRangeS i).
Proof. intros. unfold fSuccRangeS. simpl. lia. Qed.

Lemma fSuccRangeS_nat2fin : forall n (i:nat) (E : i < n) (E0 : S i < S n),
  fSuccRangeS (nat2fin i E) = nat2fin (S i) E0.
Proof. fin. Qed.
Hint Rewrite fSuccRangeS_nat2fin : fin.


(* ######################################################################### *)
(** * Sequence of fin *)

(** ** Sequence of fin *)
Section finseq.

  Definition finseq (n : nat) : list ('I_n) :=
    match n with
    | O => []
    | _ => map nat2finS (seq 0 n)
    end.

  Lemma finseq_length : forall n, length (finseq n) = n.
  Proof. destruct n; simpl; auto. rewrite map_length, seq_length. auto. Qed.
    
  Lemma finseq_eq_seq : forall n, map fin2nat (finseq n) = seq 0 n.
  Proof.
    destruct n; simpl; auto. f_equal.
    rewrite map_map. apply map_id_In. intros. rewrite fin2nat_nat2finS; auto.
    apply in_seq in H. lia.
  Qed.

  Lemma nth_finseq : forall (n : nat) i (E : i < n) i0,
      nth i (finseq n) i0 = Fin i E.
  Proof.
    intros. destruct n. lia. simpl. destruct i; simpl.
    - apply nat2finS_eq.
    - rewrite nth_map_seq; try lia.
      replace (i + 1) with (S i) by lia. apply nat2finS_eq.
  Qed.

  Lemma nth_map_finseq : forall {A} (n : nat) (f : 'I_n -> A) i (E : i < n) (a : A),
      nth i (map f (finseq n)) a = f (Fin i E).
  Proof.
    intros. rewrite nth_map with (n:=n)(Azero:=Fin i E); auto.
    rewrite nth_finseq with (E:=E). auto.
    rewrite finseq_length; auto.
  Qed.

  (* {i<n} ∈ (finseq n) *)
  Lemma In_finseq : forall {n} (i : 'I_n), In i (finseq n).
  Proof.
    intros. unfold finseq. destruct n. exfalso. apply fin0_False; auto.
    apply in_map_iff. exists (fin2nat i). split.
    - apply nat2finS_fin2nat.
    - apply in_seq. pose proof (fin2nat_lt i). lia.
  Qed.
  
End finseq.


(** ** Sequence of fin with bounds *)
Section finseqb.

  (* A list of `'I_(S n)` which its value is from `lo` to `lo + cnt -1` *)
  Definition finseqb (n : nat) (lo cnt : nat) : list 'I_(S n) :=
    map nat2finS (seq lo cnt).

  Lemma finseqb_length : forall n lo cnt, length (finseqb n lo cnt) = cnt.
  Proof. intros. unfold finseqb. rewrite map_length, seq_length. auto. Qed.

  Lemma finseqb_eq_seq : forall n lo cnt,
      lo + cnt <= S n -> map fin2nat (finseqb n lo cnt) = seq lo cnt.
  Proof.
    intros. unfold finseqb. rewrite map_map. apply map_id_In. intros.
    rewrite fin2nat_nat2finS; auto. apply in_seq in H0. lia.
  Qed.

  (* Lemma nth_finseqb : forall (n lo cnt : nat) i (H: i < n), *)
  (*     nth i (finseqb n lo cnt) fin0 = (Fin i H : 'I_n). *)
  (* Proof. *)
  (*   intros. destruct n. lia. simpl. destruct i; simpl. *)
  (*   - apply nat2finS_eq. *)
  (*   - rewrite nth_map_seq; try lia. *)
  (*     replace (i + 1) with (S i) by lia. apply nat2finS_eq. *)
  (* Qed. *)

  (* Lemma nth_map_finseqb : forall {A} (n : nat) (f : 'I_n -> A) i (H: i < n) (a : A), *)
  (*     nth i (map f (finseqb n)) a = f (Fin i H). *)
  (* Proof. *)
  (*   intros. rewrite nth_map with (n:=n)(Azero:=Fin i H : 'I_n); auto. *)
  (*   rewrite nth_finseqb with (H:=H). auto. *)
  (*   rewrite finseqb_length; auto. *)
  (* Qed. *)

  (* (* {i<n} ∈ (finseqb n) *) *)
  (* Lemma In_finseqb : forall {n} (i : 'I_n), In i (finseqb n). *)
  (* Proof. *)
  (*   intros. unfold finseqb. destruct n. exfalso. apply fin0_False; auto. *)
  (*   apply in_map_iff. exists (fin2nat i). split. *)
  (*   - apply nat2finS_fin2nat. *)
  (*   - apply in_seq. pose proof (fin2nat_lt i). lia. *)
  (* Qed. *)
  
End finseqb.
