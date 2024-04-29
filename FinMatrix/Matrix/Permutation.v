(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Permutation
  author    : ZhengPu Shi
  date      : 2023.06

  motivation :
  1. 行列式原始算法：取出不同行、不同列下标的所有组合。
  2. 对于一个排列，计算其逆序数

  remark    :
  1. compute permutation of a list, such as 
     perm [a;b;c] => [[a;b;c]; [a;c;b]; [b;a;c]; [b;c;a]; [c;a;b]; [c;b;a]]
     perm [1;2;3] => [[1;2;3]; [1;3;2]; [2;1;3]; [2;3;1]; [3;1;2]; [3;2;1]]
 *)

Require Import Extraction.
Require Export ListExt NatExt Matrix.

Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv.


(** * Lemmas for other libraries *)

(** (In l d -> length l = n) -> length (concat d) = n * length d *)
Lemma in_concat_length : forall {A} (d : dlist A) n,
    (forall l, In l d -> length l = n) -> length (concat d) = n * length d.
Proof.
  induction d; intros; simpl in *; auto.
  rewrite app_length. rewrite IHd with (n:=n); auto. rewrite H; auto. lia.
Qed.

(** (S n <? S m) = (n <? m) *)
Lemma nat_S_ltb_S : forall n m : nat, ((S n <? S m) = (n <? m))%nat.
Proof. intros. bdestruct (n <? m)%nat; bdestruct (S n <? S m)%nat; auto; lia. Qed.

(** lswap (a :: l) (S i) (S j) = a :: (lswap l i j) *)
Lemma lswap_cons_S_S : forall {A Azero} (l : list A) (a : A) (i j : nat),
    i < length l -> j < length l ->
    lswap Azero (a :: l) (S i) (S j) = a :: (lswap Azero l i j).
Proof.
  intros. unfold lswap. simpl. rewrite !nat_S_ltb_S.
  bdestruct (length l >? i); bdestruct (length l >? j); auto.
Qed.

(** lswap (a :: l) 0 (S j) = nth j l :: lset l j a. *)
Lemma lswap_cons_0_S : forall {A Azero} (l : list A) (a : A) (j : nat),
    j < length l ->
    lswap Azero (a :: l) 0 (S j) = nth j l Azero :: lset l j a.
Proof.
  intros. unfold lswap. simpl.
  rewrite nat_S_ltb_S. bdestruct (length l >? j); try easy.
Qed.

(** fold_left f l (a1 + a2) = (fold_left f l a1) + a2) *)
Lemma fold_left_rebase :
  forall {A B} (f : A -> B -> A) (fa : A -> A -> A) (l : list B) (a1 a2 : A),
    (forall a1 a2 b, f (fa a1 a2) b = fa (f a1 b) a2) ->
    fold_left f l (fa a1 a2) = fa (fold_left f l a1) a2.
Proof.
  intros. revert a1 a2.
  induction l; intros; simpl in *; auto.
  rewrite <- IHl. f_equal. auto.
Qed.


(* ############################################################################ *)
(** * Permutation of a list *)

(* ======================================================================= *)
(** ** Method 1 *)
Module method1.
  
  Section def.
    Context {A} {Azero : A}.
    
    (** Get k-th element and remaining elements from a list *)
    Fixpoint pick (l : list A) (k : nat) : A * list A :=
      match k with
      | 0 => (hd Azero l, tl l)
      | S k' =>
          match l with
          | [] => (Azero, [])
          | x :: l' =>
              let (a,l0) := pick l' k' in
              (a, ([x] ++ l0)%list)
          end
      end.
    
    (** Get permutation of a list from its top n elements *)
    Fixpoint permAux (n : nat) (l : list A) : list (list A) :=
      match n with
      | 0 => [[]]
      | S n' =>
          concat
            (map
               (fun k =>
                  let '(x, lx) := k in
                  map (cons x) (permAux n' lx))
               (map (fun i => pick l i) (seq 0 n)))
      end.

    (** Get permutation of a list *)
    Definition perm (l : list A) : list (list A) := permAux (length l) l.
  End def.
  
  (* Compute perm [1;2;3]. *)

End method1.


(* ======================================================================= *)
(** ** Method 2 *)
Module method2.
  Open Scope list_scope.
  
  Section def.
    Context {A} {Azero : A}.
    
    (** Convert a list to list of (one element * remaining elements) *)
    Fixpoint pick {A} (l : list A) (remaining : list A) : list (A * list A) :=
      match l with
      | [] => []
      | hl :: tl =>
          (hl, remaining ++ tl) :: (pick tl (remaining ++ [hl]))
      end.

    (** Get permutation of a list from its top n elements *)
    Fixpoint permAux {A} (n : nat) (l : list A) : list (list A) :=
      match n with
      | 0 => [[]]
      | S n' =>
          concat
            (map
               (fun k =>
                  let '(x, lx) := k in
                  map (cons x) (permAux n' lx))
               (pick l []))
      end.
    
    (** Get permutation of a list *)
    Definition perm (l : list A) : list (list A) := permAux (length l) l.
  End def.

  (* Compute perm2 [1;2;3]. *)
  
End method2.


(* ======================================================================= *)
(** ** Method 3 *)
Module Export method3.

  Section def.
    Context {A : Type}.

    (* 将 a 插入 l 的每个位置 *)
    Fixpoint permOne (a : A) (l : list A) : list (list A) :=
      match l with
      | [] => [[a]]
      | hl :: tl => (a :: l) :: (map (cons hl) (permOne a tl))
      end.

    (** Permutation of a list *)
    Fixpoint perm (l : list A) : list (list A) :=
      match l with
      | [] => [[]]
      | hl :: tl => concat (map (permOne hl) (perm tl))
      end.
  End def.

  (* Compute permOne 1 [2;3]. *)
  (* = [[1; 2; 3]; [2; 1; 3]; [2; 3; 1]] : dlist nat *)

  (* Compute perm [1;2;3]. *)
  (* = [[1; 2; 3]; [2; 1; 3]; [2; 3; 1]; [1; 3; 2]; [3; 1; 2]; [3; 2; 1]] : dlist nat *)


  Section props.
    Context {A : Type}.
    Context {AeqDec : Dec (@eq A)}.

    (** |permOne (a::l)| = S |l| *)
    Lemma permOne_length : forall a (l : list A), length (permOne a l) = S (length l).
    Proof. induction l; simpl; auto. rewrite map_length. auto. Qed.

    (** permOne a l <> [] *)
    Lemma permOne_not_nil : forall a (l : list A), permOne a l <> [].
    Proof. induction l; simpl; try easy. Qed.

    (** perm l <> [] *)
    Lemma perm_not_nil : forall (l : list A), perm l <> [].
    Proof.
      induction l; simpl; try easy.
      destruct (perm l) eqn:E; simpl; try easy.
      destruct (permOne a l0) eqn:E1; try easy.
      apply permOne_not_nil in E1; auto.
    Qed.
    
    (** hd (perm l) = l *)
    Lemma hd_perm : forall (l : list A), hd [] (perm l) = l.
    Proof.
      induction l; auto. simpl.
      destruct (perm l) as [|l0 dl] eqn:H1.
      - apply perm_not_nil in H1. easy.
      - simpl in *. subst. destruct l; simpl in *; auto.
    Qed.

    (** x \in (permOne a l) -> length x = S (length l) *)
    Lemma in_permOne_length : forall (l : list A) (a : A) (x : list A),
        In x (permOne a l) -> length x = S (length l).
    Proof.
      induction l; intros; simpl in *.
      - destruct H; try easy. subst; auto.
      - destruct H; subst; auto.
        apply in_map_iff in H. destruct H as [x0 [H H1]]. subst.
        apply IHl in H1. simpl. auto.
    Qed.

    (** x \in (perm l) -> length x = length l *)
    Lemma in_perm_length : forall (l x : list A),
        In x (perm l) -> length x = length l.
    Proof.
      induction l; intros; simpl in *.
      - destruct H; try easy. subst. auto.
      - apply in_concat in H. destruct H as [dl [H1 H2]].
        apply in_map_iff in H1. destruct H1 as [l0 [H3 H4]].
        subst. apply IHl in H4. rewrite <- H4.
        apply in_permOne_length in H2; auto.
    Qed.

    (** |perm (a::l)| = |(a::l)| * |perm l| *)
    Lemma perm_cons_length : forall (l : list A) (a : A),
        length (perm (a :: l)) = (S (length l)) * (length (perm l)).
    Proof.
      destruct l; intros; auto.
      unfold perm; fold (perm (a :: l)).
      rewrite in_concat_length with (n:=S (length (a::l))).
      - rewrite map_length. auto.
      - intros. remember (a :: l) as d.
        apply in_map_iff in H. destruct H as [x [H H1]].
        apply in_perm_length in H1. rewrite <- H. rewrite permOne_length. auto.
    Qed.
    
    (** |perm l| = |l|! *)
    Lemma length_perm : forall (l : list A), length (perm l) = fact (length l).
    Proof.
      induction l. auto.
      rewrite perm_cons_length.
      simpl. rewrite IHl. auto.
    Qed.

    (** In l0 (permOne a l) -> (forall x, In x l0 -> x = a \/ In x l) *)
    Lemma in_permOne : forall (l : list A) (a : A) (l0 : list A),
        In l0 (permOne a l) -> (forall x, In x l0 -> x = a \/ In x l).
    Proof.
      induction l; intros; simpl in *.
      - destruct H; try easy. subst; simpl in *. destruct H0; auto.
      - destruct H; subst; simpl in *.
        + destruct H0; auto.
        + apply in_map_iff in H. destruct H as [l1 [H1 H2]]. subst. simpl in *.
          destruct H0; auto. apply IHl with (x:=x) in H2; auto. tauto.
    Qed.

    (** In l0 (perm l) -> (forall x, In x l0 -> In x l) *)
    Lemma in_perm : forall (l : list A) (l0 : list A),
        In l0 (perm l) -> (forall x, In x l0 -> In x l).
    Proof.
      induction l; intros; simpl in *.
      - destruct H; try easy. subst; auto.
      - destruct (Aeqdec a x); auto. right.
        apply in_concat in H. destruct H as [d [H H1]].
        apply in_map_iff in H. destruct H as [l1 [H2 H3]].
        rewrite <- H2 in H1.
        apply IHl with (l0:=l1); auto.
        apply in_permOne with (x:=x) in H1; auto. destruct H1; auto.
        subst; easy.
    Qed.
  End props.

  (* well-formed permutation *)
  Section wf_perm.
    Context {A : Type}.
    Context {AeqDec : Dec (@eq A)}.

    (* A list is a permutation (no duplicate) *)
    Definition wf_perm (l : list A) : Prop := NoDup l.
  End wf_perm.

  (* 索引下标构成的排列 *)
  Section perm_index.
    Open Scope nat_scope.
    Notation perm := (@perm nat).
    
    (** In a (perm (seq 0 n)) -> i < n -> nth i a < n *)
    Lemma perm_index_lt : forall n i a, In a (perm (seq 0 n)) -> i < n -> nth i a 0 < n.
    Proof.
      intros. apply in_perm with (x:=nth i a 0) in H.
      - apply in_seq in H. lia.
      - apply nth_In. apply in_perm_length in H. rewrite seq_length in H. lia.
    Qed.

  End perm_index.

End method3.


(* ======================================================================= *)
(** ** reverse-order-number (RON) of a list, 逆序数 *)
Section ronum.
  Context {A} {Altb : A -> A -> bool}.
  Infix "<?" := Altb.

  (** The RON of one element respect to a list *)
  Definition ronum1 (a : A) (l : list A) : nat :=
    fold_left (fun (n : nat) (b : A) => n + (if b <? a then 1 else 0)) l 0.

  (** The RON of a list *)
  Fixpoint ronum (l : list A) : nat :=
    match l with
    | [] => 0
    | x :: l' => ronum1 x l' + ronum l'
    end.

  Context {Azero : A}.
  Notation lswap := (lswap Azero).

  (** ronum1 b (a :: l) = (if b <? a then 1 else 0) + ronum1 b l *)
  Lemma ronum1_cons : forall (l : list A) a b,
      ronum1 b (a :: l) = (if a <? b then 1 else 0) + ronum1 b l.
  Proof.
    intros. unfold ronum1. simpl.
    remember (fun (n : nat) (b0 : A) => n + (if b0 <? b then 1 else 0)) as f.
    remember (if a <? b then 1 else 0) as n.
    replace n with (0 + n) by lia.
    rewrite fold_left_rebase; try lia.
    intros. rewrite Heqf. fin.
  Qed.

  (** forall i, nth i l Azero <? a = true -> ronum1 a l > 0 *)
  Lemma ronum1_gt0 : forall (l : list A) (i : nat) (a : A),
      i < length l -> nth i l Azero <? a = true -> ronum1 a l > 0.
  Proof.
    induction l; intros; simpl in *. lia. destruct i.
    - rewrite ronum1_cons. rewrite H0. lia.
    - rewrite ronum1_cons.
      apply lt_S_n in H. specialize (IHl i a0 H H0). lia.
  Qed.
  
  (** ronum1 b [a1;a2;...;a;...;an] + (ai<?b ?? 1 : 0)
     = ronum1 b [a1;a2;...;ai;...;an] + (a<?b ?? 1 : 0) *)
  Lemma ronum1_lset_invariant : forall (l : list A) (i : nat) (a b : A),
      i < length l ->
      ronum1 b (lset l i a) + (if nth i l Azero <? b then 1 else 0) = 
        ronum1 b l + (if a <? b then 1 else 0).
  Proof.
    induction l; intros; simpl in *. lia. destruct i.
    - unfold ronum1. simpl.
      remember (fun (n : nat) (b0 : A) => n + (if b0 <? b then 1 else 0)) as f.
      remember (if a0 <? b then 1 else 0) as n.
      remember (if a <? b then 1 else 0) as m.
      replace n with (0 + n) by lia.
      replace m with (0 + m) at 2 by lia.
      rewrite !fold_left_rebase; try lia; intros.
      all: rewrite Heqf; lia.
    - rewrite !ronum1_cons. rewrite <- !Nat.add_assoc. rewrite IHl; auto. lia.
  Qed.

  (** ronum1 b [a1;a2;...;a;...;an] = ronum1 b [a1;a2;...;ai;...;an] + 
      (a<?b ?? 1 : 0) - (ai<?b ?? 1 : 0) *)
  Lemma ronum1_lset : forall (l : list A) (i : nat) (a b : A),
      i < length l ->
      ronum1 b (lset l i a) =
        ronum1 b l + (if a <? b then 1 else 0) -
        (if nth i l Azero <? b then 1 else 0).
  Proof. intros. pose proof (ronum1_lset_invariant l i a b H). lia. Qed.

  (** ronum1 a (lswap l i j) = ronum1 a l *)
  Lemma ronum1_lswap : forall (l : list A) (a : A) (i j : nat),
      i < length l -> j < length l -> i < j ->
      ronum1 a (lswap l i j) = ronum1 a l.
  Proof.
    induction l; intros; simpl in *. lia.
    destruct i, j; simpl in *; try easy.
    - rewrite lswap_cons_0_S; try lia. rewrite !ronum1_cons.
      pose proof (ronum1_lset_invariant l j a a0). lia.
    - apply lt_S_n in H,H0,H1.
      rewrite lswap_cons_S_S; auto.
      rewrite !ronum1_cons. rewrite IHl; auto.
  Qed.
  
  (** ronum (lswap l i j) = ronum l + S (2 * j - S i)) *)
  Lemma ronum_lswap : forall (l : list A) (i j : nat),
      i < length l -> j < length l -> i < j ->
      ronum (lswap l i j) = ronum l + S (2 * (j - S i)).
  Proof.
    induction l; intros; simpl in *. lia.
    destruct i, j; try lia; simpl in *.
    2:{
      apply lt_S_n in H,H0,H1.
      rewrite lswap_cons_S_S; auto. simpl. rewrite IHl; auto.
      pose proof (nat_add_ASGroup).
      asgroup. (* Tips, example for usage of asgroup *)
      rewrite ronum1_lswap; auto. }
    - clear IHl.
      rewrite lswap_cons_0_S; try lia. simpl.
      rewrite ronum1_lset; try lia.
      
    Admitted.
    
End ronum.

Section test.
  Let ronum1 := @ronum1 nat Nat.leb.
  Let ronum := @ronum nat Nat.leb.
  (* Compute ronum1 3 [1;2;4]. (* = 2 *) *)
  (* Compute ronum [2;1;4;3]. (* = 2 *) *)
  (* Compute ronum [2;3;4;1]. (* = 3 *) *)

  (* Given a list [3;5], and swap the 1-th and 2-th elements get [5;3],
     then, ronum1 will unchanged, at three cases. *)
  (* Compute ronum1 2 [3;5].       (* 0 *) *)
  (* Compute ronum1 2 [5;3].       (* 0 *) *)
  (* Compute ronum1 4 [3;5].       (* 1 *) *)
  (* Compute ronum1 4 [5;3].       (* 1 *) *)
  (* Compute ronum1 6 [3;5].       (* 0 *) *)
  (* Compute ronum1 6 [5;3].       (* 2 *) *)
End test.

(* ======================================================================= *)
(** ** Parity of a permutation, 排列的奇偶性 *)
Section parity.
  Context {A} {Altb : A -> A -> bool}.

  (** The RON of a permutation is odd *)
  Definition oddPerm (l : list A) : bool := odd (ronum (Altb:=Altb) l).

End parity.


(* ======================================================================= *)
(** ** Exchange of a permutation 排列的对换 *)
Section permExchg.
  Context {A} {Altb : A -> A -> bool} (Azero : A).

  Notation ronum := (ronum (Altb:=Altb)).
  Notation oddPerm := (oddPerm (Altb:=Altb)).
  Notation lswap := (lswap Azero).
  
  (** Swap two elements will change the parity of a permutation *)
  Theorem swap_perm_parity : forall (l : list A) (i0 i1 : nat),
      NoDup l ->
      i0 < length l -> i1 < length l -> i0 < i1 ->
      oddPerm (lswap l i0 i1) = negb (oddPerm l).
  Proof.
    intros.
    unfold oddPerm. rewrite ronum_lswap; auto.
    rewrite Nat.add_succ_r. rewrite Nat.odd_succ. rewrite Nat.negb_odd.
    rewrite Nat.even_add_mul_2. auto.
  Qed.
  
End permExchg.

