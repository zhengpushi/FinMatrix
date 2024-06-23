(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : auxiliary library for nat.
  author    : Zhengpu Shi
  date      : 2021.05

  remark    :
  1. naming of nat variable: n, m, k, p, q, r
 *)

Require Export Init.Nat PeanoNat Arith Lia.
Require Export ElementType.

Open Scope nat_scope.

(* ######################################################################### *)
(** * Algebraic Structures *)

(** equality is equivalence relation: Equivalence (@eq nat) *)
Hint Resolve eq_equivalence : nat.

(** operations are well-defined. Eg: Proper (eq ==> eq ==> eq) add *)
Hint Resolve Nat.add_wd Nat.mul_wd : nat.

(** Decidable *)

Instance nat_eq_Dec : Dec (@eq nat).
Proof. constructor. apply Nat.eq_dec. Defined.

Instance nat_lt_Dec : Dec lt.
Proof. constructor. intros. destruct (Compare_dec.lt_dec a b); auto. Defined.

Instance nat_le_Dec : Dec le.
Proof. constructor. intros. destruct (le_lt_dec a b); auto. right. lia. Defined.

(** Associative *)

Instance natAdd_Assoc : Associative Nat.add.
Proof. constructor; intros; ring. Qed.

Instance natMul_Assoc : Associative Nat.mul.
Proof. constructor; intros; ring. Qed.

Hint Resolve natAdd_Assoc natMul_Assoc : nat.

Goal forall a b c : nat, (a + (b + c) = (a + b) + c).
Proof. intros. rewrite associative; auto. Qed.

Goal forall a b c : nat, ((a + b) + c = a + (b + c)).
Proof. apply associative. Qed.

(** Commutative *)

Instance natAdd_Comm : Commutative Nat.add.
Proof. constructor; intros; ring. Qed.

Instance natMul_Comm : Commutative Nat.mul.
Proof. constructor; intros; ring. Qed.

Hint Resolve natAdd_Comm natMul_Comm : nat.

Goal forall a b : nat, (a + b = b + a)%nat.
Proof. apply commutative. Qed.

Goal forall a b : nat, (a * b = b * a)%nat.
Proof. apply commutative. Qed.

(** Identity Left/Right *)
Instance natAdd_IdL : IdentityLeft Nat.add 0.
Proof. constructor; intros; ring. Qed.

Instance natAdd_IdR : IdentityRight Nat.add 0.
Proof. constructor; intros; ring. Qed.

Instance natMul_IdL : IdentityLeft Nat.mul 1.
Proof. constructor; intros; ring. Qed.

Instance natMul_IdR : IdentityRight Nat.mul 1.
Proof. constructor; intros; ring. Qed.

Hint Resolve
  natAdd_IdL natAdd_IdR
  natMul_IdL natMul_IdR : nat.

(** Inverse Left/Right *)

(** Distributive *)

Instance natMul_add_DistrL : DistrLeft Nat.add Nat.mul.
Proof. constructor; intros; ring. Qed.

Instance natMul_add_DistrR : DistrRight Nat.add Nat.mul.
Proof. constructor; intros; ring. Qed.

Hint Resolve natMul_add_DistrL natMul_add_DistrR : nat.

(** Semigroup *)

Instance natAdd_SGroup : SGroup Nat.add.
Proof. constructor; auto with nat. Qed.

Instance natMul_SGroup : SGroup Nat.mul.
Proof. constructor; auto with nat. Qed.

Hint Resolve
  natAdd_SGroup
  natMul_SGroup
  : nat.

(** Abelian semigroup *)

Instance natAdd_ASGroup : ASGroup Nat.add.
Proof. constructor; auto with nat. Qed.

Instance natMul_ASGroup : ASGroup Nat.mul.
Proof. constructor; auto with nat. Qed.

Hint Resolve
  natAdd_ASGroup
  natMul_ASGroup
  : nat.

Goal forall x1 x2 y1 y2 a b c : nat,
    x1 + x2 = y1 + y2 -> x1 + a + b + c + x2 = y1 + c + (b + a) + y2.
Proof. intros. pose proof natAdd_ASGroup. asgroup. Qed.

(** Monoid *)
  
Instance natAdd_Monoid : Monoid Nat.add 0.
Proof. constructor; auto with nat. Qed.
Hint Resolve natAdd_Monoid : nat.

Instance natMul_Monoid : Monoid Nat.mul 1.
Proof. constructor; auto with nat. Qed.
Hint Resolve natMul_Monoid : nat.

(** Abelian monoid *)
  
Instance natAdd_AMonoid : AMonoid Nat.add 0.
Proof. constructor; auto with nat. Qed.
Hint Resolve natAdd_AMonoid : nat.
  
Instance natMul_AMonoid : AMonoid Nat.mul 1.
Proof. constructor; auto with nat. Qed.
Hint Resolve natMul_AMonoid : nat.

(** SRing *)

Instance nat_SRing : SRing Nat.add 0 Nat.mul 1.
Proof. constructor; auto with nat. Qed.
Hint Resolve nat_SRing : nat.


(** Order *)

(** (<, <=, <?, <=?) is an Order *)
Instance nat_Order : Order lt le.
Proof.
  constructor; intros; try lia; auto with nat.
  destruct (lt_eq_lt_dec a b) as [[H|H]|H]; auto.
Qed.

Infix "??=" := (@dec _ _ nat_eq_Dec) : nat_scope.

Notation "m ??> n" := (@dec _ _ nat_lt_Dec n m) : nat_scope.
Notation "m ??>= n" := (@dec _ _ nat_le_Dec n m) : nat_scope.
Infix "??<" := (@dec _ _ nat_lt_Dec) : nat_scope.
Infix "??<=" := (@dec _ _ nat_le_Dec) : nat_scope.


(* ######################################################################### *)
(** * Instances for ElementType *)

Module ElementTypeNat <: ElementType.
  Definition tA : Type := nat.
  Definition Azero : tA := 0.
  Hint Unfold tA Azero : tA.

  Lemma AeqDec : Dec (@eq tA).
  Proof. apply nat_eq_Dec. Defined.
End ElementTypeNat.

Module OrderedElementTypeNat <: OrderedElementType.
  Include ElementTypeNat.

  Definition Alt := Nat.lt.
  Definition Ale := Nat.le.
  Hint Unfold Ale Alt : tA.

  Instance Order : Order Alt Ale.
  Proof. apply nat_Order. Qed.
End OrderedElementTypeNat.

Module MonoidElementTypeNat <: MonoidElementType.
  Include ElementTypeNat.

  Definition Aadd := Nat.add.
  Hint Unfold Aadd : tA.

  Infix "+" := Aadd : A_scope.

  Instance Aadd_AMonoid : AMonoid Aadd Azero.
  Proof. intros. repeat constructor; intros; autounfold with tA; ring. Qed.
End MonoidElementTypeNat.


(* ######################################################################### *)
(** * More properties for nat *)

(** a natural number must be odd or even *)
Lemma nat_split : forall (n : nat), exists (x : nat),
    n = 2 * x \/ n = 2 * x + 1.
Proof.
  induction n.
  - exists 0. auto.
  - destruct IHn. destruct H.
    + exists x. right. subst. lia.
    + exists (x+1). left. subst. lia.
Qed.

(** Two step induction principle for natural number *)
Theorem nat_ind2 : forall (P : nat -> Prop),
    (P 0) -> (P 1) -> (forall n, P n -> P (S (S n))) -> (forall n, P n).
Proof.
  intros. destruct (nat_split n). destruct H2; subst; induction x; auto.
  - replace (2 * S x) with (S (S (2 * x))); [apply H1; auto | lia].
  - replace (2 * S x + 1) with (S (S (2 * x + 1))); [apply H1; auto | lia].
Qed.

(** Connect induction principle between nat and list *)
Lemma ind_nat_list {tA} : forall (P : list tA -> Prop) ,
    (forall n l, length l = n -> P l) -> (forall l, P l).
Proof.
  intros. apply (H (length l)). auto.
Qed.


(* ######################################################################### *)
(** * Loop shift *)
Section loop_shift.

  (** Left loop shift *)
  Definition nat_lshl (n : nat) (i : nat) (k : nat) : nat :=
    Nat.modulo (i + k) n.

  (** Right loop shift *)
  Definition nat_lshr (n : nat) (i : nat) (k : nat) : nat :=
    Nat.modulo (i + (n - (Nat.modulo k n))) n.

  (* Compute List.map (fun i => nat_lshl 5 i 1) (List.seq 0 10). *)
  (* Compute List.map (fun i => nat_lshr 5 i 1) (List.seq 0 10). *)
  
  (** Let S is a set of natural numbers modulo n, i.e. its elements are [0,1,...,(n-1)],
    and n is equivalent to 0.
    Then right loop shift S by k got T.
    We claim that: forall i < n, (T[i] = (S[i] + k)%n /\ (S[i] = (T[i] + ?)%n) *)
  (* Theorem nat_lshl_spec0 : forall n i k, nat_lshl n i k = Nat. *)

End loop_shift.

(* ######################################################################### *)
(** * Extension for nat from (Verified Quantum Computing). *)

(* https://www.cs.umd.edu/~rrand/vqc/index.html *)

(*******************************)
(* Automation *)
(*******************************)

(** n + n = 2 * n *)
Lemma double_mult : forall (n : nat), (n + n = 2 * n).
Proof. intros. lia. Qed.

(** (2 ^ n) * 2 = 2 ^ (n + 1) *)
Lemma pow_two_succ_l : forall n, (2 ^ n) * 2 = 2 ^ (n + 1).
Proof.
  intros. rewrite Nat.mul_comm. rewrite <- Nat.pow_succ_r'. rewrite Nat.add_1_r. auto.
Qed.

(** 2 * (2 ^ n) = 2 ^ (n + 1) *)
Lemma pow_two_succ_r : forall n, 2 * (2 ^ n) = 2 ^ (n + 1).
Proof. intros. rewrite <- Nat.pow_succ_r'. rewrite Nat.add_1_r. auto. Qed.

(** 2 ^ n + 2 ^ n = 2 ^ (n + 1)  *)
Lemma double_pow : forall (n : nat), 2 ^ n + 2 ^ n = 2 ^ (n + 1). 
Proof. intros. rewrite double_mult. rewrite pow_two_succ_r. reflexivity. Qed.

(** a = b -> n = m -> a ^ n = b ^ m  *)
Lemma pow_components : forall (a b m n : nat), a = b -> n = m -> a ^ n = b ^ m.
Proof. intuition. Qed.

(** Simplify terms contain "2 ^ n" *)
Ltac pow_two :=
  repeat match goal with
    (* NB: this first thing is potentially a bad idea, do not do with 2^1 *)
    | [ |- context[ 4%nat ]]                  => replace 4%nat with (2^2)%nat 
        by reflexivity
    | [ |- context[ (0 + ?a)%nat]]            => rewrite Nat.add_0_l 
    | [ |- context[ (?a + 0)%nat]]            => rewrite Nat.add_0_r 
    | [ |- context[ (1 * ?a)%nat]]            => rewrite Nat.mul_1_l 
    | [ |- context[ (?a * 1)%nat]]            => rewrite Nat.mul_1_r 
    | [ |- context[ (2 * 2^?x)%nat]]          => rewrite <- Nat.pow_succ_r'
    | [ |- context[ (2^?x * 2)%nat]]          => rewrite pow_two_succ_l
    | [ |- context[ (2^?x + 2^?x)%nat]]       => rewrite double_pow 
    | [ |- context[ (2^?x * 2^?y)%nat]]       => rewrite <- Nat.pow_add_r 
    | [ |- context[ (?a + (?b + ?c))%nat ]]   => rewrite Nat.add_assoc 
    | [ |- (2^?x = 2^?y)%nat ]                => apply pow_components; try lia 
    end.

(** Restoring Matrix dimensions *)
Ltac is_nat_equality :=
  match goal with 
  | |- ?A = ?B => match type of A with
                | nat => idtac
                end
  end.


(* ######################################################################### *)
(** * Useful bdestruct tactic with the help of reflection *)

(** There havn't GT and GE in standard library. *)

Notation  "a >=? b" := (b <=? a) (at level 70) : nat_scope.
Notation  "a >? b"  := (b <? a) (at level 70) : nat_scope.

(** Prove inequality of nat *)
Ltac solve_nat_ineq :=
  match goal with
  (* H: _ = true *)
  | H:(?a <? ?b) = true |- ?a < ?b => apply Nat.ltb_lt; apply H
  | H:(?a <? ?b) = true |- ?b > ?a => apply Nat.ltb_lt; apply H
  | H:(?a <? ?b) = false |- ?a >= ?b => apply Nat.ltb_ge; apply H
  | H:(?a <? ?b) = false |- ?b <= ?a => apply Nat.ltb_ge; apply H
  | H:(?a <=? ?b) = false |- ?b < ?a => apply Nat.leb_gt; apply H
  end.


(** Proposition and boolean are reflected. *)

Lemma nat_eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof. intros x y. apply Nat.eqb_spec. Defined.

(* Compute Nat.eqb_spec 0 3. *)
(* Compute nat_eqb_reflect 0 3. *)

Lemma nat_ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof. intros x y. apply iff_reflect. symmetry. apply Nat.ltb_lt. Defined.

Lemma nat_leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof. intros x y. apply iff_reflect. symmetry. apply Nat.leb_le. Defined.

(* These lemmas are automatically used. *)
Hint Resolve nat_eqb_reflect nat_ltb_reflect nat_leb_reflect : bdestruct.

(** This tactic makes quick, easy-to-read work of our running example. *)
Example reflect_example2: forall a, (if a <? 5 then a else 2) < 6.
Proof.
  intros.
  (* destruct (ltb_reflect a 5). *)
  bdestruct (a <? 5).
  all: lia.
Qed.


(* ######################################################################### *)
(** * Lost or deprecated lemmas and new lemmas *)

(** n <> 0 -> 0 < n *)
Lemma neq_0_lt_stt : forall n : nat, n <> 0 -> 0 < n.
Proof. lia. Qed.

(** S n < S m -> n < m *)
(* Coq.Arith.Lt.lt_S_n is deprecated since Coq 8.16.
   1. although coqc suggest us to use Nat.succ_lt_mono,
   but that is a  a bidirectional version, not exactly same as lt_S_n.
   2. from Coq 8.16, there is a same lemma Arith_prebase.lt_S_n,
   but it not exist in Coq 8.13,8.14.
*)
Definition lt_S_n: forall n m : nat, S n < S m -> n < m.
Proof. intros. apply Nat.succ_lt_mono. auto. Qed.

(** 0 < n < S m -> pred n < m *)
Lemma pred_lt : forall n m : nat, 0 < n < S m -> pred n < m.
Proof. lia. Qed.

(** n < m -> m > n *)
Lemma lt_imply_gt : forall n m : nat, n < m -> m > n.
Proof. lia. Qed.

(** n > m -> m < n *)
Lemma gt_imply_lt : forall n m : nat, n > m -> m < n.
Proof. lia. Qed.

Lemma lt_ge_dec : forall n m : nat, {n < m} + {n >= m}.
Proof. intros. destruct (le_gt_dec m n); auto. Defined.

(** n >= m -> n <> m -> n > m *)
Lemma nat_ge_neq_imply_gt : forall n m : nat, n >= m -> n <> m -> n > m.
Proof. lia. Qed.

(** n <= m -> n <> m -> n < m *)
Lemma nat_le_neq_imply_lt : forall n m : nat, n <= m -> n <> m -> n < m.
Proof. lia. Qed.

(** n > m -> n <> 0 *)
Lemma nat_gt_imply_neq0 : forall n m : nat, n > m -> n <> 0.
Proof. lia. Qed.

(** n < m -> m <> 0 *)
Lemma nat_lt_imply_neq0 : forall n m : nat, n < m -> m <> 0.
Proof. intros. lia. Qed.

(** m <= n -> n < m + k -> n - m < k *)
Lemma le_ltAdd_imply_subLt_l : forall m k n : nat, m <= n -> n < m + k -> n - m < k.
Proof. intros. lia. Qed.

(** m <= n -> n < k + m -> n - m < k *)
Lemma le_ltAdd_imply_subLt_r : forall m k n : nat, m <= n -> n < k + m -> n - m < k.
Proof. intros. lia. Qed.

(** 0 < n -> 0 < m -> n - m < n *)
Lemma nat_sub_lt : forall n m : nat, 0 < n -> 0 < m -> n - m < n.
Proof. intros. lia. Qed.

(** n < m - k -> n + k < m *)
Lemma nat_lt_sub_imply_lt_add : forall n m k : nat, n < m - k -> n + k < m.
Proof. lia. Qed.

(** n < S m -> m < k -> n < k *)
Lemma nat_ltS_lt_lt : forall n m k : nat, n < S m -> m < k -> n < k.
Proof. lia. Qed.

(** n < m -> m < S k -> n < k *)
Lemma nat_lt_ltS_lt : forall n m k : nat, n < m -> m < S k -> n < k.
Proof. lia. Qed.

(** n < S m -> n <= m *)
Lemma nat_lt_n_Sm_le : forall n m : nat, n < S m -> n <= m.
Proof.
  intros.
  (* Coq 8.19.0 *)
  (* apply PeanoNat.lt_n_Sm_le. *)
  (* Coq 8.18.0 *)
  (* apply Arith_prebase.lt_n_Sm_le. *)
  (* Arith_prebase.lt_n_Sm_le:  *)
  lia.
Qed.


(* ######################################################################### *)
(** * Properties for div and mod *)

(* Check Nat.div_add.    (* (a + b * c) / c = a / c + b *) *)
(* Check Nat.div_add_l.  (* a * b + c) / b = a + c / b *) *)
(* Check Nat.div_small.  (* a < b -> a / b = 0 *) *)
(* Check Nat.add_mod.    (* (a + b) % n = (a % n + b % n) % n *) *)
(* Check Nat.mod_add.    (* (a + b * c) mod c = a mod c *) *)
(* Check Nat.mod_mul.    (* (a * b) % b = 0 *) *)
(* Check Nat.mod_small.  (* a < b -> a % b = 0 *) *)


(* i < n -> (m * n + i) / n = m *)
Lemma add_mul_div : forall m n i, n <> 0 -> i < n -> (m * n + i) / n = m.
Proof.
  intros. rewrite Nat.div_add_l; auto. rewrite Nat.div_small; auto.
Qed.
 
(* i < n -> (m * n + i) % n = i *)
Lemma add_mul_mod : forall m n i, n <> 0 -> i < n -> (m * n + i) mod n = i.
Proof.
  intros. rewrite Nat.Div0.add_mod; auto. rewrite Nat.Div0.mod_mul; auto.
  repeat rewrite Nat.mod_small; auto.
Qed.
