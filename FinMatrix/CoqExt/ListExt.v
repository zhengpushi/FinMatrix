(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Extension for list
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. reference "A Gentle Introduction to Type Classes and Relations in Coq"
  2. main contribution
     list
        operations and propertities of list
     dlist
        operations and propertities of list
     
  
  history   :
  1. 2021.12, by ZhengPu Shi.
     first version

  2. 2022.05, by ZhengPu Shi.
     split big file into small modules

  3. 2022.10, by ZhengPu Shi
     Setoid version

  4. 2023.11, by ZhengPu Shi
     Leibniz Equality version
 *)

Require Export List SetoidList. Export ListNotations.
Require Import StrExt.
Require Export NatExt.
Require Export Hierarchy.

Open Scope nat_scope.
Open Scope list.

Generalizable Variables tA tB tC Aadd Azero Aopp Amul Aone Ainv.

Notation dlist tA := (list (list tA)).

Hint Resolve
  repeat_length seq_length map_length
  : mat.


(* ##################################################################### *)
(** * list *)

(* ===================================================================== *)
(** ** Properties of cons *)
Section cons.
  Context {tA : Type}.
  
  (** Equality of cons, iff both parts are equal *)
  Lemma cons_eq_iff : forall (a1 a2 : tA) (l1 l2 : list tA),
      a1 :: l1 = a2 :: l2 <-> a1 = a2 /\ l1 = l2.
  Proof.
    intros. split; intros H; inversion H; subst; auto.
  Qed.

  (** Inequality of cons, iff at least one parts are not equal *)
  Lemma cons_neq_iff : forall (a1 a2 : tA) (l1 l2 : list tA),
      a1 :: l1 <> a2 :: l2 <-> (a1 <> a2) \/ (l1 <> l2).
  Proof.
    intros. split; intro H.
    - rewrite cons_eq_iff in H.
      apply not_and_or in H; auto.
    - intro. inversion H0. subst. destruct H; auto.
  Qed.

End cons.


(* ===================================================================== *)
(** ** Properties of hd and tl *)
Section hd_tl.
  Context {tA} {Azero : tA}.
  
  (** length of tl. (pred version) *)
  Lemma tl_length : forall (l : list tA), length (tl l) = pred (length l).
  Proof. induction l; auto. Qed.

  Lemma hd_eq_nth_0 : forall (l : list tA), hd Azero l = nth 0 l Azero.
  Proof. intros. destruct l; simpl; auto. Qed.

End hd_tl.

(* ===================================================================== *)
(** ** Properties of nth *)
Section nth.
  
  Context {tA : Type} (Azero : tA).

  (** nth [] a = a *)
  Lemma nth_nil : forall (a : tA) (i : nat), nth i [] a = a.
  Proof.
    intros. destruct i; simpl; easy.
  Qed.

  (** If element-wise equal, then two lists are equal *)
  Lemma list_eq_ext : forall (n : nat) (l1 l2 : list tA),
      (forall i, i < n -> nth i l1 Azero = nth i l2 Azero) ->
      length l1 = n -> length l2 = n ->
      l1 = l2.
  Proof.
    intros n l1. revert n. induction l1; intros; simpl in *; subst.
    - apply length_zero_iff_nil in H1. auto.
    - destruct l2; simpl in *; try easy. f_equal.
      + specialize (H 0); simpl in *. apply H; lia.
      + apply (IHl1 (length l2)); try lia. intros.
        specialize (H (S i)); simpl in *. apply H; lia.
  Qed.
  
  (* (** Two list equal iff all nth visit equal *) *)
  (* Lemma list_eq_imply : forall (l1 l2 : list tA), *)
  (*     l1 = l2 -> (forall i, i < length l1 -> nth i l1 Azero = nth i l2 Azero). *)
  (* Proof. intros; subst; auto. Qed. *)
  
  (* Lemma list_eq_iff_nth : *)
  (*   forall n (l1 l2 : list tA) (H1 : length l1 = n) (H2 : length l2 = n), *)
  (*     l1 = l2 <-> (forall (i : nat), i < n -> nth i l1 Azero = nth i l2 Azero). *)
  (* Proof. *)
  (*   intros n l1. revert n. induction l1; intros; simpl in *; subst. *)
  (*   - split; intros; try easy. apply List.length_zero_iff_nil in H2. easy. *)
  (*   - split; intros; try easy. *)
  (*     + destruct l2; try easy. *)
  (*       inversion H. subst. destruct i; simpl; auto. *)
  (*     + destruct l2; simpl in *; try easy. f_equal. *)
  (*       * specialize (H 0). simpl in H. apply H. lia. *)
  (*       * rewrite (IHl1 (length l1)); auto. intros. *)
  (*         specialize (H (S i)); simpl in H. apply H. lia. *)
  (* Qed. *)

  (* (repeat a n)[i] = a *)
  Lemma nth_repeat_same : forall (n i : nat) (a def : tA),
      i < n -> nth i (repeat a n) def = a.
  Proof. induction n; intros. lia. destruct i; simpl; auto. apply IHn. lia. Qed.

End nth.


(* ===================================================================== *)
(** ** nthFull : nth element with index-in-the-bound *)
Section nthFull.
  Context {tA : Type}.

  (* Get element of a list.
     This is very similiar with `nth`, but needn't a default value *)
  Definition nthFull (l : list tA) (i : nat) (H : i < length l) : tA.
  Proof.
    destruct l.
    - simpl in H. apply Nat.nlt_0_r in H. contradiction.
    - exact (nth i (t :: l) t).
  Defined.

  Lemma nthFull_eq_nth : forall (Azero : tA) (l : list tA) (i : nat) (H : i < length l),
      nthFull l i H = nth i l Azero.
  Proof.
    destruct l; intros; simpl in *. lia. destruct i; auto.
    apply nth_indep. lia.
  Qed.
  
End nthFull.


(* ===================================================================== *)
(** ** Properties of fold_left *)
Section fold_left.

  Context `{HAMonoid:AMonoid}.
  Infix "+" := Aadd.
  
  Lemma fold_left_rebase_l : forall (l : list tA) a b,
      fold_left Aadd l (a + b) = (fold_left Aadd l a) + b.
  Proof.
    induction l; intros; simpl; auto.
    replace (a0 + b + a) with (a0 + a + b). apply IHl. agroup.
  Qed.

  Lemma fold_left_rebase_r : forall (l : list tA) a b,
      fold_left Aadd l (a + b) = (fold_left Aadd l b) + a.
  Proof.
    intros. rewrite (commutative a b). rewrite fold_left_rebase_l. auto.
  Qed.

  (** (a+0+0+0+... = a *)
  Lemma fold_left_lzero : forall n a,
      fold_left Aadd (repeat Azero n) a = a.
  Proof.
    induction n; intros; simpl; auto.
    rewrite fold_left_rebase_r. rewrite IHn. amonoid.
  Qed.

  (** Σ(ai+bi) = Σ(ai) + Σ(bi) *)
  Lemma fold_left_add : forall (l l1 l2:list tA) n,
      length l = n -> length l1 = n -> length l2 = n ->
      (forall i, i < n -> nth i l Azero = nth i l1 Azero + nth i l2 Azero) ->
      fold_left Aadd l Azero = (fold_left Aadd l1 Azero) + (fold_left Aadd l2 Azero).
  Proof.
    induction l; destruct l1,l2; intros; simpl in *; try lia.
    - agroup.
    - destruct n. lia.
      inversion H; clear H. inversion H0; clear H0. inversion H1; clear H1.
      rewrite !fold_left_rebase_l.
      rewrite (IHl l1 l2 n); auto.
      + agroup.
        specialize (H2 0). simpl in H2. rewrite H2; auto. lia.
      + intros. specialize (H2 (S i)). simpl in H2. apply H2. lia.
  Qed.

  Context `{HGroup:Group tA Aadd Azero Aopp}.
  
  (** (-a1)+(-a2)+... = -(a1+a2+...) *)
  Lemma fold_left_opp : forall (l1 l2:list tA) n,
      length l1 = n -> length l2 = n ->
      (forall i, i < n -> nth i l1 Azero = Aopp (nth i l2 Azero)) ->
      fold_left Aadd l1 Azero = Aopp (fold_left Aadd l2 Azero).
  Proof.
    induction l1,l2; intros; simpl in *; try lia.
    - rewrite group_opp_0; auto.
    - destruct n. lia.
      inversion H; clear H. inversion H0; clear H0.
      rewrite !fold_left_rebase_l.
      rewrite (IHl1 l2 n); auto.
      + agroup. specialize (H1 0); simpl in H1. rewrite H1; auto; try lia.
      + intros. specialize (H1 (S i)). simpl in H1. apply H1. lia.
  Qed.

  Context `{HARing:ARing tA Aadd Azero Aopp Amul Aone}.
  Add Ring ring_inst : (make_ring_theory HARing).
  Infix "*" := Amul.

  (** k*a1+k*a2+... = k * (a1+a2+...) *)
  Lemma fold_left_cmul : forall (l1 l2:list tA) n a,
      length l1 = n -> length l2 = n ->
      (forall i, i < n -> nth i l1 Azero = a * (nth i l2 Azero)) ->
      fold_left Aadd l1 Azero = a * (fold_left Aadd l2 Azero).
  Proof.
    induction l1,l2; intros; simpl in *; try lia.
    - rewrite ring_mul_0_r; auto.
    - destruct n. lia.
      inversion H; clear H. inversion H0; clear H0.
      rewrite !fold_left_rebase_l.
      rewrite (IHl1 l2 n a0); auto.
      + rewrite distrLeft. agroup.
        specialize (H1 0). simpl in H1. rewrite H1; auto. lia.
      + intros. specialize (H1 (S i)). simpl in H1. apply H1. lia.
  Qed.

End fold_left.


(* ===================================================================== *)
(** ** Properties of fold_right *)
Section fold_right.

  Context `{HAMonoid:AMonoid}.
  Infix "+" := Aadd.
  
  Lemma fold_right_rebase_l : forall (l : list tA) a b,
      fold_right Aadd (a + b) l = b + (fold_right Aadd a l).
  Proof.
    induction l; intros; simpl; auto. agroup. rewrite IHl. agroup.
  Qed.

  Lemma fold_right_rebase_r : forall (l : list tA) a b,
      fold_right Aadd (a + b) l = a + (fold_right Aadd b l).
  Proof.
    intros. rewrite (commutative a b). rewrite fold_right_rebase_l. auto.
  Qed.

  (** (a+0+0+0+... = a *)
  Lemma fold_right_lzero : forall n a,
      fold_right Aadd a (repeat Azero n) = a.
  Proof. induction n; intros; simpl; auto. rewrite IHn. agroup. Qed.
  
  (** Σ(ai+bi) = Σ(ai) + Σ(bi) *)
  Lemma fold_right_add : forall (l l1 l2:list tA) n,
      length l = n -> length l1 = n -> length l2 = n ->
      (forall i, i < n -> nth i l Azero = nth i l1 Azero + nth i l2 Azero) ->
      fold_right Aadd Azero l = (fold_right Aadd Azero l1) +
                                  (fold_right Aadd Azero l2).
  Proof.
    induction l; destruct l1,l2; intros; simpl in *; try lia. agroup.
    destruct n. lia. rewrite (IHl l1 l2 n); auto.
    - specialize (H2 0); simpl in H2. rewrite H2; try lia. agroup.
    - intros. specialize (H2 (S i)); simpl in H2. rewrite H2; auto. lia.
  Qed.

  Context `{HGroup:Group tA Aadd Azero Aopp}.

  (** (-a1)+(-a2)+... = -(a1+a2+...) *)
  Lemma fold_right_opp : forall (l1 l2:list tA) n,
      length l1 = n -> length l2 = n ->
      (forall i, i < n -> nth i l1 Azero = Aopp (nth i l2 Azero)) ->
      fold_right Aadd Azero l1 = Aopp (fold_right Aadd Azero l2).
  Proof.
    induction l1,l2; intros; simpl in *; try lia.
    - rewrite group_opp_0; auto.
    - destruct n. lia. rewrite (IHl1 l2 n); auto.
      + specialize (H1 0); simpl in H1.
        rewrite H1; try lia. rewrite group_opp_distr. agroup.
      + intros. specialize (H1 (S i)); simpl in H1. rewrite H1; auto. lia.
  Qed.

  Context `{HARing:ARing tA Aadd Azero Aopp Amul Aone}.
  Infix "*" := Amul.

  (** k*a1+k*a2+... = k * (a1+a2+...) *)
  Lemma fold_right_cmul : forall (l1 l2:list tA) n a,
      length l1 = n -> length l2 = n ->
      (forall i, i < n -> nth i l1 Azero = a * (nth i l2 Azero)) ->
      fold_right Aadd Azero l1 = a * (fold_right Aadd Azero l2).
  Proof.
    induction l1,l2; intros; simpl in *; try lia.
    - rewrite ring_mul_0_r; auto.
    - destruct n. lia. rewrite (IHl1 l2 n a0); auto.
      + rewrite (distrLeft a0). agroup.
        specialize (H1 0); simpl in H1; rewrite H1; auto. lia.
      + intros. specialize (H1 (S i)); simpl in H1. apply H1. lia.
  Qed.

End fold_right.


(* ===================================================================== *)
(** ** Print a list *)
Section lst_prt.
  Context {tA : Type}.
  Definition lst_prt (l : list tA) (p : tA -> string) : string :=
    fold_left (fun s x => append s (p x)) l "".
End lst_prt.

(* Compute lst_prt [1;2;3] (fun n => str_alignl (nat2str n) 5). *)
(* Compute lst_prt [1;2;3] (fun n => str_alignr (nat2str n) 5). *)


(* ===================================================================== *)
(** ** Set element of a list *)
Section chg.

  Context {tA : Type}.

  (** *** Set element with a constant value *)
  Fixpoint lset (l : list tA) (i : nat) (x : tA) : list tA :=
    match l, i with
    | [], _ => []
    | a :: l, 0 => x :: l
    | a :: l, S i => a :: (lset l i x)
    end.

  (** Length property *)
  Lemma lset_length : forall (l : list tA) ni n x, 
      length l = n ->
      length (lset l ni x) = n.
  Proof.
    intros l; induction l; auto. induction ni; auto; simpl; intros.
    destruct n; auto. easy.
  Qed.

  (** *** Set element with a generation function *)

  (** Inner version. i0 is given position, i is changing every loop *)
  Fixpoint lsetf_aux (l : list tA) (i0 i : nat) (f : nat -> tA) 
    : list tA :=
    match l, i with
    | [], _ => []
    | a :: l, 0 => f i0 :: l
    | a :: l, S i => a :: (lsetf_aux l i0 i f)
    end.

  (** User version that hide i0 parameter *)
  Definition lsetf (l : list tA) (i : nat) (f : nat -> tA) : list tA :=
    lsetf_aux l i i f.
  
  (** Length property *)
  Lemma lsetf_aux_length : forall (l : list tA) ni n ni0 f, 
      length l = n ->
      length (lsetf_aux l ni0 ni f) = n.
  Proof.
    intros l; induction l; auto. destruct ni; auto; simpl; intros.
    destruct n; auto. easy.
  Qed.

  Lemma lsetf_length : forall (l : list tA) n ni f, 
      length l = n ->
      length (lsetf l ni f) = n.
  Proof.
    intros. apply lsetf_aux_length; auto.
  Qed.

End chg.

(* Let f_gen := fun (i : nat) => (i + 5). *)
(* Compute lsetf [1;2;3] 0 f_gen. *)
(* Compute lsetf [1;2;3] 1 f_gen. *)


(* ===================================================================== *)
(** ** Swap two elements *)
Section lswap.
  Context {tA} (Azero : tA).
  
  (** Swap two elements of a list *)
  Definition lswap (l : list tA) (i1 i2 : nat) : list tA :=
    let r := length l in
    if (i1 <? r) && (i2 <? r)
    then 
      let e1 := nth i1 l Azero in
      let e2 := nth i2 l Azero in
      lset (lset l i1 e2) i2 e1
    else l.

  Lemma lswap_length : forall l i1 i2, length (lswap l i1 i2) = length l.
  Proof.
    intros. unfold lswap.
    destruct (i1 <? length l) eqn:E1, (i2 <? length l) eqn:E2; simpl; auto.
    rewrite lset_length with (n:=length l); auto.
    rewrite lset_length with (n:=length l); auto.
  Qed.

End lswap.


(* ===================================================================== *)
(** ** Properties of length *)
Section length.

  Context {tA : Type}.

  (** Redefine 'length_zero_iff_nil', original is opaque, make it transparent t *)
  Lemma length_zero_iff_nil : forall (l : list tA), length l = 0 <-> l = [].
  Proof.
    intros. destruct l; intros; split; intros; auto; try easy.
  Defined.

  (** decompose a list which length is 1 *)
  Lemma list_length1 : forall (l : list tA),
      length l = 1 -> {x | l = [x]}.
  Proof. 
    destruct l; intros. inversion H. inversion H.
    apply length_zero_iff_nil in H1. subst. exists t. easy.
  Defined.

  (** a list has only one element equal to [hd _ l] *)
  Lemma list_length1_eq_hd : forall (x : tA) (l:list tA), 
      length l = 1 -> l = [hd x l].
  Proof.
    intros x l. destruct l.
    - intros. simpl in *. lia.
    - intros. simpl in *. f_equal.
      apply eq_add_S in H. apply List.length_zero_iff_nil in H. subst. easy.
  Qed.

  (** decompose a list which length is S n *)
  Lemma list_length_Sn : forall (l : list tA) n,
      length l = S n -> {x & { t | l = x :: t}}.
  Proof.
    destruct l; intros. inversion H. exists t. exists l. easy.
  Qed.

  (** decompose a list which length is S (S n) *)
  Lemma list_length_SSn : forall (l : list tA) n,
      length l = S (S n) -> {x & { y & { t | l = x :: y :: t}}}.
  Proof.
    destruct l; intros. inversion H.
    exists t. destruct l. inversion H.
    exists t0. exists l. auto.
  Qed.

  (** Split list which length is 1 *)
  Lemma list_length1_neq : forall (l : list tA) (a b : tA), 
      (length (a :: l) = 1 /\ (a :: l <> [b]) -> (a <> b) /\ l = []).
  Proof.
    intros; destruct l. destruct H.
    - split; auto. intro; subst; easy.
    - destruct H. simpl in H. easy.
  Qed.

End length.

Section Test.
  Context {tA} (a : tA).
  Let l := [a].
  Definition h : length l = 1. auto. Defined.
  (* Compute proj1_sig (list_length_1 l h). *)
End Test.


(* ===================================================================== *)
(** ** List to elements *)

(* 自动处理前提中含有 length 以及目标中 cons 的简单情形，以自动化 list2elems 的证明 *)
Ltac solve_list2elems :=
  match goal with
  (* 若有 0 = S _，直接得证 *)
  | H: 0 = S _ |- _ => discriminate
  (* 若有 length l = 0，则替换为 [] *)
  | H: length ?l = 0 |- _ => apply length_zero_iff_nil in H; rewrite H in *; clear H
  (* 若有 S (length l) = 1，则改写为 length l = 0 *)
  | H: S (length ?l) = S ?n |- _ => assert (length l = n); [lia |]; clear H
  (* 若有 a :: l1 = b :: l2，则必然是头尾分别相等 *)
  | |- cons _ _ = cons _ _ => f_equal
  end.

Section list2elems.
  Context {tA} {Azero : tA}.
  Notation "l ! i" := (nth i l Azero) (at level 2).

  (** a list of length 1 *)
  Lemma list2elems_1 : forall (l : list tA), length l = 1 -> l = [l!0].
  Proof.
    intros; destruct l; simpl in *; repeat solve_list2elems.
  Qed.

  (** a list of length 2 *)
  Lemma list2elems_2 : forall (l : list tA), length l = 2 -> l = [l!0; l!1].
  Proof.
    intros; destruct l; simpl in *; repeat solve_list2elems.
    apply list2elems_1; auto.
  Qed.

  (** a list of length 3 *)
  Lemma list2elems_3 : forall (l : list tA), length l = 3 -> l = [l!0; l!1; l!2].
  Proof. 
    intros; destruct l; simpl in *; repeat solve_list2elems.
    apply list2elems_2; auto.
  Qed.

  (** a list of length 4 *)
  Lemma list2elems_4 : forall (l : list tA), length l = 4 -> l = [l!0; l!1; l!2; l!3].
  Proof. 
    intros; destruct l; simpl in *; repeat solve_list2elems.
    apply list2elems_3; auto.
  Qed.

End list2elems.


(* ===================================================================== *)
(** ** Customized list induction *)
Section ind.

  Context {tA : Type}.

  (** Connect induction principle between nat and list *)
  Lemma ind_nat_list : forall (P : list tA -> Prop) ,
      (forall n l, length l = n -> P l) -> (forall l, P l).
  Proof.
    intros. apply (H (length l)). auto.
  Qed.

  (** Two step induction principle for list *)
  Theorem list_ind2 : forall (P : list tA -> Prop),
      (P []) -> 
      (forall a, P [a]) -> 
      (forall l a b, P l -> P (a :: b :: l)) ->
      (forall l, P l).
  Proof.
    intros P H0 H1 H2. apply ind_nat_list. induction n using nat_ind2. 
    - intros. apply length_zero_iff_nil in H; subst; auto.
    - intros. apply list_length1 in H. destruct H. subst; auto.
    - destruct l; auto. destruct l; auto.
      intros. apply H2. apply IHn. simpl in H. lia.
  Qed.

End ind.


(* ===================================================================== *)
(** ** list repeat properties *)
Section repeat.
  Context {tA : Type}.

  (** repeat S n times equal to another form *)
  Lemma list_repeat_Sn (Azero : tA) : forall n, repeat Azero (S n) = Azero :: repeat Azero n.
  Proof. intros. simpl. easy. Qed.

End repeat.


(* ===================================================================== *)
(** ** Zero list *)
Section lzero.
  Context {tA : Type}.
  
  (** tA friendly name for zero list *)
  Definition lzero (Azero : tA) n := repeat Azero n.

  (** lzero's length law *)
  Lemma lzero_length (Azero : tA) : forall n, length (lzero Azero n) = n.
  Proof. intros. apply repeat_length. Qed.

  (** append two zero list to a zero list satisfy length relation *)
  Lemma lzero_app (Azero : tA) : forall n1 n2,
      lzero Azero n1 ++ lzero Azero n2 = lzero Azero (n1 + n2).
  Proof. unfold lzero. intros. rewrite repeat_app. easy. Qed.

End lzero.

Hint Resolve lzero_length : mat.
  
(* ===================================================================== *)
(** ** Properties of map *)

(** map for two types *)
Section map_A_B.
  Context {tA tB} (Azero : tA) (Bzero : tB) (f : tA -> tB).
  
  (** map and repeat is communtative *)
  Lemma map_repeat : forall (a : tA) n, map f (repeat a n) = repeat (f a) n.
  Proof.
    induction n; simpl; auto. f_equal; auto.
  Qed.

  (** (map f l)[i] = f (l[i]) *)
  Lemma nth_map : forall n i (l : list tA),
      length l = n -> i < n ->
      nth i (map f l) Bzero = f (nth i l Azero).
  Proof.
    intros n i l. revert n i.
    induction l; intros; simpl in *. lia. destruct n. lia.
    destruct i; auto. apply IHl with (n:=n); auto. lia.
  Qed.

  (** map is injective, if `f` is injective on the given list *)
  Lemma map_inj : forall (l1 l2 : list tA),
      (forall a b : tA, In a l1 -> In b l2 -> f a = f b -> a = b) ->
      map f l1 = map f l2 ->
      l1 = l2.
  Proof.
    induction l1; destruct l2; intros; simpl in *; try easy.
    inversion H0. f_equal; auto.
  Qed.

  (** map is surjective, if `f` is surjective on the given list *)
  Lemma map_surj : forall (lb : list tB),
    (forall b : tB, In b lb -> exists (a : tA), f a = b) ->
    exists (la : list tA), length la = length lb /\ map f la = lb.
  Proof.
    intros lb H. induction lb as [|b lb]; intros.
    - exists []. auto.
    - destruct (H b) as [a]. constructor; auto. destruct IHlb as [la].
      + intros. apply H. simpl; auto.
      + exists (a :: la). simpl. destruct H1. rewrite H0,H1,H2. auto.
  Qed.

  (* If any element `a` in list `l` satisfy `P (f a)`, then `Forall P (map f l)` hold *)
  Lemma Forall_map_forall : forall (P : tB -> Prop) (l : list tA),
      (forall (a : tA), In a l -> P (f a)) -> Forall P (map f l).
  Proof.
    intros. induction l; simpl; auto. constructor.
    apply H. simpl; auto. apply IHl. intros. apply H. simpl; auto.
  Qed.

End map_A_B.


(** map for one type *)
Section map_A.
  Context {tA} (Azero : tA) (f : tA -> tA).

  (** Extented map_id lemma, which needn't the function is a exactly format of
     "forall x, x" *)
  Lemma map_id : forall (l : list tA) (H: forall a, f a = a), map f l = l.
  Proof.
    induction l; intros; simpl. easy. f_equal; auto.
  Qed.
  
  (** Extented map_id (In version) *)
  Lemma map_id_In : forall (l : list tA), (forall a : tA, In a l -> f a = a) -> map f l = l.
  Proof.
    induction l; intros; simpl. auto. f_equal.
    - apply H. simpl; auto.
    - apply IHl. intros. apply H. simpl; auto.
  Qed.

  (** f x = zero -> map f = lzero *)
  Lemma map_eq_zero : forall (l : list tA) n,
      (forall x : tA, (f x = Azero)) -> length l = n -> map f l = lzero Azero n.
  Proof.
    induction l; intros; simpl in *. subst. simpl. easy.
    destruct n. easy. inv H0. simpl. f_equal; auto.
  Qed.
  
  (** Mapping is fixpoint, iff f is id *)
  Lemma map_fixpoint_imply_id : forall (l : list tA), 
      map f l = l -> (forall x, In x l -> (f x = x)).
  Proof.
    induction l; intros; simpl in *. easy. inversion H.
    destruct H0. subst; auto. apply IHl; auto.
  Qed.

  (** Simplify of nth+map+seq *)
  Lemma nth_map_seq : forall (g : nat -> tA) n m i,
      i < m -> (nth i (map g (seq n m)) Azero = g (i + n)).
  Proof.
    (* Tips: we need to induction on two variables to complete the proof *)
    intros. revert m i g H. induction n.
    - induction m; simpl; intros. lia. destruct i; try easy.
      rewrite <- seq_shift. rewrite map_map. rewrite IHm; auto. lia.
    - intros. rewrite <- seq_shift. rewrite List.map_map. rewrite IHn; auto.
  Qed.

  (** Simplify of map+nth+seq *)
  (* Note: the lower index of seq is 0, it could extend to any nat number later *)
  Lemma map_nth_seq  : forall n (l : list tA) Azero,
      length l = n -> map (fun i => nth i l Azero) (seq 0 n) = l.
  Proof.
    induction n.
    - intros. simpl. apply length_zero_iff_nil in H; subst. easy.
    - intros. simpl. destruct l.
      + simpl in *; lia.
      + f_equal. inversion H.
        rewrite <- seq_shift.
        rewrite map_map; auto. simpl.
        rewrite H1. rewrite IHn; easy.
  Qed.

  (** Equality of map+seq, iff corresponding elements are equal *)
  Lemma map_seq_eq : forall n (f g : nat -> tA),
      map f (seq 0 n) = map g (seq 0 n) <-> (forall i, i < n -> (f i = g i)).
  Proof.
    intros; split; intros.
    - rewrite map_ext_in_iff in H. apply H. apply in_seq. lia.
    - apply map_ext_in_iff. intros. apply H. apply in_seq in H0. lia.
  Qed.

End map_A.


(* ===================================================================== *)
(** ** map two lists to a list *)
Section map2.
  Context {tA tB tC} (Azero : tA) (Bzero : tB) (Czero : tC) (f : tA -> tB -> tC).
  
  (** map operation to two list *)
  Fixpoint map2 (l1 : list tA) (l2 : list tB) : list tC :=
    match l1, l2 with
    | x1 :: t1, x2 :: t2 => (f x1 x2) :: (map2 t1 t2)
    | _, _ => []
    end.
  
  (** length of map2 *)
  Lemma map2_length : forall (l1 : list tA) (l2 : list tB) n,
      length l1 = n -> length l2 = n -> length (map2 l1 l2) = n.
  Proof. 
    induction l1,l2; simpl; auto. intros. destruct n; simpl; auto. easy.
  Qed.
  
  (** map2 to two lists could be separated by two segments with same length *)
  Lemma map2_app : forall (la1 la2 : list tA) (lb1 lb2 : list tB),
      length la1 = length lb1 -> length la2 = length lb2 ->
      map2 (la1 ++ la2) (lb1 ++ lb2) = (map2 la1 lb1) ++ (map2 la2 lb2).
  Proof.
    induction la1, lb1; intros; simpl; auto; simpl in H; try easy.
    f_equal. auto.
  Qed.
  
  (** map2 [] l = [] *)
  Lemma map2_nil_l : forall l, map2 [] l = [].
  Proof. destruct l; easy. Qed.

  (** map2 l [] = [] *)
  Lemma map2_nil_r : forall l, map2 l [] = [].
  Proof. destruct l; easy. Qed.

  (** nth (map2 f l1 l2) i = f (nth l1 i) (nth l2 i) *)
  Lemma nth_map2 : forall n i (l1 : list tA) (l2 : list tB),
      length l1 = n -> length l2 = n -> i < n ->
      (nth i (map2 l1 l2) Czero = f (nth i l1 Azero) (nth i l2 Bzero)).
  Proof.
    intros n i l1. revert n i.
    induction l1,l2; intros; simpl in *; destruct i; try lia; auto.
    destruct n. lia. apply IHl1 with (n:=n); lia.
  Qed.
  
End map2.

Hint Resolve map2_length : mat.


(* ===================================================================== *)
(** ** map2 on dlist *)
Section map2_dlist.
  Context {tA tB tC : Type} (f : tA -> tB -> tC).
  
  (** tail of map2 to dlist, equal to map2 to tail part of original dlists *)
  Lemma tail_map2_dlist : forall dl1 dl2,
      tl (map2 (map2 f) dl1 dl2) =
        map2 (map2 f) (tl dl1) (tl dl2).
  Proof.
    destruct dl1, dl2; simpl; try easy. rewrite map2_nil_r. easy.
  Qed.

End map2_dlist.


(* ===================================================================== *)
(** ** map2 properties with same base type *)
Section map2_sametype.
  Context `{HMonoid : Monoid}.
  Infix "+" := Aadd.
  
  (** (l1 . l2) . l3 = l1 . (l2 . l3) *)
  Lemma map2_assoc : forall (l1 l2 l3 : list tA),
      map2 Aadd (map2 Aadd l1 l2) l3 = map2 Aadd l1 (map2 Aadd l2 l3).
  Proof.
    induction l1; destruct l2,l3; simpl; try easy. f_equal; monoid.
  Qed.

  (* (** nth (map2 f l1 l2) i = f (nth l1 i) (nth l2 i) *) *)
  (* Lemma nth_map2_sameType : forall (l1 l2 : list tA) n i a, *)
  (*     length l1 = n -> length l2 = n -> i < n -> *)
  (*     (nth i (map2 Aadd l1 l2) a = Aadd (nth i l1 a) (nth i l2 a)). *)
  (* Proof. *)
  (*   induction l1,l2; intros; simpl in *; destruct i; try lia; auto. *)
  (*   destruct n. lia. apply IHl1 with (n:=n); lia. *)
  (* Qed. *)

  (* (** nth (map2 f l1 l2) i = f (nth l1 i) (nth l2 i) *) *)
  (* Lemma nth_map2_sameType' : forall (l1 l2 : list tA) i, *)
  (*     length l1 = length l2 -> *)
  (*     (nth i (map2 Aadd l1 l2) Azero = Aadd (nth i l1 Azero) (nth i l2 Azero)). *)
  (* Proof. *)
  (*   induction l1,l2; intros; simpl in *; destruct i; monoid; try lia. *)
  (* Qed. *)

  (** map2 lzero l = l *)
  Lemma map2_zero_l : forall l, map2 Aadd (lzero Azero (length l)) l = l.
  Proof.
    induction l; intros; simpl. easy. rewrite IHl. monoid.
  Qed.

  (** map2 l lzero = l *)
  Lemma map2_zero_r : forall l, map2 Aadd l (lzero Azero (length l)) = l.
  Proof.
    induction l; intros; simpl. easy. rewrite IHl. monoid.
  Qed.

  (** l1 . l2 = l2 . l1 *)
  Context `{HAMonoid : AMonoid _ Aadd Azero}.
  Lemma map2_comm : forall (l1 l2 : list tA), map2 Aadd l1 l2 = map2 Aadd l2 l1.
  Proof.
    induction l1; destruct l2; simpl; try easy. agroup.
  Qed.
  
  (** *** The properties below, need a group structure *)

  Context `{G:Group tA Aadd Azero Aopp}.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + (-b)).
  
  (** map2 over map is homorphism *)
  (* In fact, I don't know how to naming this property yet. *)
  Lemma map2_map_hom :
    forall l1 l2 (H : forall a b : tA, (Aopp (Aadd a b) = Aadd (Aopp a) (Aopp b))),
      map2 Aadd (map Aopp l1) (map Aopp l2) = map Aopp (map2 Aadd l1 l2).
  Proof.
    intros. revert l2.
    induction l1; destruct l2; simpl; try easy.
    f_equal; auto.
  Qed.

  (* l1 - l2 = - (l2 - l1) *)
  Lemma map2_sub_comm : forall (l1 l2 : list tA),
      map2 Asub l1 l2 = map Aopp (map2 Asub l2 l1).
  Proof.
    induction l1; destruct l2; intros; simpl in *; auto.
    f_equal; auto. rewrite group_opp_distr. rewrite group_opp_opp. easy.
  Qed.

  (** (l1 - l2) - l3 = (l1 - l3) - l2 *)
  Lemma map2_sub_perm : forall (l1 l2 l3 : list tA),
      map2 Asub (map2 Asub l1 l2) l3 = map2 Asub (map2 Asub l1 l3) l2.
  Proof.
    induction l1,l2,l3; simpl; auto. f_equal; auto. agroup.
  Qed.
  
  (** (l1 - l2) - l3 = l1 - (l2 + l3) *)
  Lemma map2_sub_assoc : forall (l1 l2 l3 : list tA),
      map2 Asub (map2 Asub l1 l2) l3 = map2 Asub l1 (map2 Aadd l2 l3).
  Proof.
    induction l1,l2,l3; simpl; auto. f_equal; auto. agroup.
  Qed.

  (** 0 - l = - l *)
  Lemma map2_sub_zero_l : forall l n, 
      length l = n -> map2 Asub (lzero Azero n) l = map Aopp l.
  Proof.
    induction l; simpl; intros. apply map2_nil_r.
    induction n ; simpl. lia. f_equal; auto. agroup.
  Qed.
  
  (** l - 0 = l *)
  Lemma map2_sub_zero_r : forall l n, 
      length l = n -> map2 Asub l (lzero Azero n) = l.
  Proof.
    induction l; simpl; intros; auto. destruct n; simpl. lia.
    f_equal; agroup.
  Qed.
  
  (** l - l = 0 *)
  Lemma map2_sub_self : forall l n, 
      length l = n -> map2 Asub l l = (lzero Azero n).
  Proof.
    induction l; simpl; intros; subst; try easy. simpl lzero. f_equal; agroup.
  Qed.

End map2_sametype.

(** map2 with map of two components *)
Section map2_map_map.

  Context {tA tB : Type}.

  Lemma map2_map_map :
    forall (f1 f2 g : tA -> tB) (h : tB -> tB -> tB)
      (H : forall x, (h (f1 x) (f2 x) = g x))
      (l : list tA),
      map2 h (map f1 l) (map f2 l) = map g l.
  Proof.
    induction l; simpl; auto. f_equal; auto.
  Qed.

End map2_map_map.


(* ===================================================================== *)
(** ** concatenation of list *)
Section concat.

  (** fold_left of list nat and add operation with different initial value *)
  Lemma fold_left_nat_initial : forall (l : list nat) n,
      fold_left add l n = fold_left add l 0 + n.
  Proof.
    induction l; intros; auto.
    simpl. rewrite IHl. rewrite (IHl a). lia.
  Qed.

  (** Length of concat operation *)
  Lemma concat_length : forall {tA} (l : dlist tA),
      length (concat l) = fold_left add (map (@length tA) l) 0.
  Proof.
    intros tA l.
    induction l; simpl; auto.
    rewrite app_length. rewrite IHl. rewrite (fold_left_nat_initial _ (length a)).
    lia.
  Qed.

End concat.


(* ===================================================================== *)
(** ** Convert between list and natural-number-index-function *)
Section f2l_l2f.
  Context {tA} (Azero : tA).

  Definition f2l (n : nat) (f : nat -> tA) : list tA :=
    map f (seq 0 n).

  Lemma f2l_length : forall n f, length (f2l n f) = n.
  Proof.
    intros. unfold f2l. rewrite map_length. apply seq_length.
  Qed.

  (** (f2l f)[i] = f i *)
  Lemma nth_f2l : forall {n} f a i, i < n -> nth i (f2l n f) a = f i.
  Proof. intros. unfold f2l. rewrite nth_map_seq; auto. Qed.

  Lemma f2l_inj : forall n (f1 f2 : nat -> tA),
      f2l n f1 = f2l n f2 -> (forall i, i < n -> f1 i = f2 i).
  Proof.
    intros. unfold f2l in *. apply ext_in_map with (a:=i) in H; auto.
    apply in_seq; auto. lia.
  Qed.

  
  Definition l2f (n : nat) (l : list tA) : nat -> tA :=
    fun i => nth i l Azero.

  Lemma l2f_inj : forall n (l1 l2 : list tA),
      (forall i, i < n -> (l2f n l1) i  = (l2f n l2 i)) ->
      length l1 = n -> length l2 = n -> l1 = l2.
  Proof. intros. unfold l2f in *. apply list_eq_ext in H; auto. Qed.
  
  Lemma f2l_l2f : forall l {n}, length l = n -> f2l n (l2f n l) = l.
  Proof.
    intros. apply (list_eq_ext Azero n); auto.
    - intros. rewrite nth_f2l; auto.
    - apply f2l_length.
  Qed.

  Lemma l2f_f2l : forall f n i, i < n -> l2f n (f2l n f) i = f i.
  Proof. intros. unfold l2f. rewrite nth_f2l; auto. Qed.

  Lemma f2l_surj : forall n (l : list tA), length l = n -> exists (f : nat -> tA), f2l n f = l.
  Proof. intros. exists (l2f n l). apply f2l_l2f; auto. Qed.

  Lemma l2f_surj : forall n (f : nat -> tA),
    exists (l : list tA), (forall i, i < n -> (l2f n l) i = f i).
  Proof. intros. exists (f2l n f). intros. apply l2f_f2l; auto. Qed.

End f2l_l2f.

Section test.
  (** [1;2;3] *)
  Let f := fun i => i + 1.
  Let l := f2l 3 f.
  (* Compute l. *)

  Let g := l2f 0 3 l.
  (* Compute (g 0, g 1, g 2). *)
End test.  


(* ===================================================================== *)
(** ** Addition, Opposition and Subtraction of list *)
Section ladd_opp_sub.

  Context `{AG:AGroup tA Aadd Azero Aopp}.
  Notation Asub := (fun a b => Aadd a (Aopp b)).

  (** l1 + l2 *)
  Definition ladd (l1 l2 : list tA) : list tA := map2 Aadd l1 l2.
  Infix "+" := ladd : list_scope.

  (** invariant for length of ladd *)
  Lemma ladd_length : forall l1 l2 n,
      length l1 = n -> length l2 = n -> length (l1 + l2) = n.
  Proof.
    intros. apply map2_length; auto.
  Qed.
  
  (** l1 + l2 = l2 + l1 *)
  Lemma ladd_comm : forall l1 l2, l1 + l2 = l2 + l1.
  Proof.
    apply map2_comm; auto.
  Qed.
  
  (** [] + l = [] *)
  Lemma ladd_nil_l : forall l, ladd l [] = [].
  Proof.
    induction l; try easy.
  Qed.
  
  (** l + [] = [] *)
  Lemma ladd_nil_r : forall l, ladd [] l = [].
  Proof.
    try easy.
  Qed.
  
  (** 0 + l = l *)
  Lemma ladd_zero_l : forall l n, 
      length l = n -> ladd (lzero Azero n) l = l.
  Proof.
    induction l; simpl; intros. apply map2_nil_r.
    induction n ; simpl. inversion H.
    f_equal; auto. agroup.
  Qed.
  
  (** l + 0 = l *)
  Lemma ladd_zero_r : forall l n, length l = n -> ladd l (lzero Azero n) = l.
  Proof.
    intros. unfold ladd. rewrite map2_comm; auto.
    apply ladd_zero_l; auto.
  Qed.
  
  (** - l *)
  Definition lopp (l : list tA) : list tA := map Aopp l.
  
  (** l1 - l2 *)
  Definition lsub (l1 l2 : list tA) : list tA := map2 Asub l1 l2.

  (** l1 - l2 = - (l2 - l1) *)
  Lemma lsub_comm : forall (l1 l2 : list tA), lsub l1 l2 = lopp (lsub l2 l1).
  Proof. intros. apply map2_sub_comm. Qed.
  
  (** (l1 - l2) - l3 = (l1 - l3) - l2 *)
  Lemma lsub_perm : forall (l1 l2 l3 : list tA),
      lsub (lsub l1 l2) l3 = lsub (lsub l1 l3) l2.
  Proof.
    apply map2_sub_perm; apply AG.
  Qed.
  
  (** (l1 - l2) - l3 = l1 - (l2 + l3) *)
  Lemma lsub_assoc : forall (l1 l2 l3 : list tA),
      lsub (lsub l1 l2) l3 = lsub l1 (ladd l2 l3).
  Proof. apply map2_sub_assoc. Qed.
  
  (** 0 - l = - l *)
  Lemma lsub_zero_l : forall l n, length l = n -> lsub (lzero Azero n) l = lopp l.
  Proof.
    apply map2_sub_zero_l; apply AG.
  Qed.
  
  (** l - 0 = l *)
  Lemma lsub_zero_r : forall l n, length l = n -> lsub l (lzero Azero n) = l.
  Proof.
    apply map2_sub_zero_r; apply AG.
  Qed.
  
  (** l - l = 0 *)
  Lemma lsub_self : forall l n, length l = n -> lsub l l = (lzero Azero n).
  Proof.
    apply map2_sub_self; apply AG.
  Qed.
  
End ladd_opp_sub.


(* ===================================================================== *)
(** ** constant multiplication of list *)
Section lcmul_lmulc.
  Context `{HARing:ARing}.
  Add Ring ring_inst : (make_ring_theory HARing).

  Infix "*" := Amul.

  (** a * l *)
  Definition lcmul (a : tA) (l : list tA) : list tA := map (fun x => a * x) l.
  
  (** l * a *)
  Definition lmulc (l : list tA) (a : tA) : list tA := map (fun x => x * a) l.
  
  (** cmul keep its length *)
  Lemma lcmul_length : forall a l n, length l = n -> length (lcmul a l) = n.
  Proof. intros. unfold lcmul. rewrite map_length; auto. Qed.
  
  (** a * l = l * a *)
  Lemma lmulc_lcmul : forall a l, lmulc l a = lcmul a l.
  Proof. induction l; simpl; try easy. f_equal; auto. apply commutative. Qed.
  
  (** a * [] = [] *)
  Lemma lcmul_nil : forall a, lcmul a [] = [].
  Proof. intros. easy. Qed.
  
  (** [] * a = [] *)
  Lemma lmulc_nil : forall a, lmulc [] a = [].
  Proof. intros. easy. Qed.
  
  Context `{HField:Field tA Aadd Azero Aopp Amul Aone Ainv}.
  Add Field field_inst : (make_field_theory HField).

  Context {AeqDec : Dec (@eq tA)}.
  
  (** mul k x = x -> k = 1 \/ x = 0 *)
  Lemma fcmul_fixpoint_imply_k1_or_zero :
    forall (k x : tA), (k * x = x) -> (k = Aone) \/ (x = Azero).
  Proof.
    intros. destruct (Aeqdec x Azero); auto. left.
    apply symmetry in H. rewrite <- (@identityLeft _ Amul Aone) in H at 1.
    - apply field_mul_cancel_r in H; auto.
    - apply monoidIdL.
  Qed.
  
  (** mul x k = x -> k = 1 \/ x = 0 *)
  Lemma fmulc_fixpoint_imply_k1_or_zero :
    forall (k x : tA), (x * k = x) -> (k = Aone) \/ (x = Azero).
  Proof.
    intros. rewrite commutative in H.
    apply fcmul_fixpoint_imply_k1_or_zero; auto.
  Qed.

  (** k * l = l -> k = 1 \/ l = 0 *)
  Lemma lcmul_fixpoint_imply_k1_or_lzero : 
    forall (l : list tA) {n} (Hl : length l = n) (k : tA),
      lcmul k l = l -> ((k = Aone) \/ l = lzero Azero n).
  Proof.
    induction l; intros. subst; auto.
    destruct n. easy. simpl in *. inversion H. inversion Hl. subst.
    apply fcmul_fixpoint_imply_k1_or_zero in H1.
    destruct (Aeqdec k Aone); auto. destruct H1; auto.
    right. f_equal.
    - rewrite H0. ring.
    - rewrite H2.
      specialize (IHl (length l) eq_refl k H2). destruct IHl; auto. easy.
  Qed.
  
  (** lmulc is fixpoint, iff k1 or lzero *)
  Lemma lmulc_fixpoint_imply_k1_or_lzero : 
    forall (l : list tA) {n} (Hl : length l = n) (k : tA),
      lmulc l k = l -> ((k = Aone) \/ l = lzero Azero n).
  Proof.
    intros.
    apply lcmul_fixpoint_imply_k1_or_lzero; auto.
    rewrite <- lmulc_lcmul. easy.
  Qed.

  (** k * l = 0 -> k = 0 \/ l = 0 *)
  Lemma lcmul_eq0_imply_k0_or_lzero : 
    forall (l : list tA) {n} (Hl : length l = n) (k : tA),
      lcmul k l = lzero Azero n -> ((k = Azero) \/ l = lzero Azero n).
  Proof.
    induction l; intros. subst; auto.
    destruct n. easy. simpl in *.
    inversion H. inversion Hl.
    specialize (IHl (length l) eq_refl k). rewrite H1,<-H3 in H2.
    specialize (IHl H2).
    destruct IHl; auto.
    - subst. left. ring.
    - apply field_mul_eq0_iff in H1; auto. destruct H1.
      + left. subst. ring.
      + right. subst. f_equal; try ring.
        rewrite <- H0 in H2. auto.
  Qed.
  
End lcmul_lmulc.


(* ===================================================================== *)
(** ** product of two lists *)
Section ldot.
  
  Context `{HARing:ARing}.
  Add Ring ring_inst : (make_ring_theory HARing).

  Infix "+" := Aadd.
  Infix "*" := Amul.
  
  (** dot product, marked as l1 . l2 *)
  Definition ldot (l1 l2 : list tA) : tA :=
    fold_right Aadd Azero (map2 Amul l1 l2).

  (** l1 . l2 = l2 . l1 *)
  Lemma ldot_comm : forall (l1 l2 : list tA), ldot l1 l2 = ldot l2 l1.
  Proof.
    intros. unfold ldot. pose proof (aringMulAMonoid). rewrite map2_comm. auto.
  Qed.
  
  (** [] . l = 0 *)
  Lemma ldot_nil_l : forall (l : list tA), ldot nil l = Azero.
  Proof. intros. destruct l; simpl; try easy. Qed.
  
  (** l . [] = 0 *)
  Lemma ldot_nil_r : forall (l : list tA), ldot l nil = Azero.
  Proof. intros. destruct l; simpl; try easy. Qed.

  (** ldot cons *)
  Lemma ldot_cons : forall l1 l2 x1 x2,
      ldot (x1 :: l1) (x2 :: l2) = (x1 * x2) + (ldot l1 l2).
  Proof. induction l1,l2; simpl; intros; try easy. Qed.
  
  (** lzero . l = 0 *)
  Lemma ldot_zero_l : forall l n, ldot (lzero Azero n) l = Azero.
  Proof.
    induction l,n; simpl; intros; try easy. rewrite ldot_cons.
    rewrite IHl. ring.
  Qed.
  
  (** l . lzero = 0 *)
  Lemma ldot_zero_r : forall l n, ldot l (lzero Azero n) = Azero.
  Proof. intros. rewrite ldot_comm. apply ldot_zero_l. Qed.
  
  (** ldot left distributive over ladd.
    l1 . (l2 + l3) = l1.l2 + l1.l3 *)
  Lemma ldot_ladd_distr_l : forall l1 l2 l3 r,
      length l1 = r -> length l2 = r -> length l3 = r ->
      ldot l1 (@ladd _ Aadd l2 l3) = (ldot l1 l2) + (ldot l1 l3).
  Proof.
    induction l1,l2,l3; simpl; intros; subst; try (cbv;ring); try discriminate.
    rewrite ?ldot_cons. inversion H1. inversion H0.
    rewrite IHl1 with (r:=length l1); auto. ring.
  Qed.
  
  (** ldot right distributive over ladd.
    (l1 + l2) . l3 = l1.l3 + l2.l3 *)
  Lemma ldot_ladd_distr_r : forall l1 l2 l3 r,
      length l1 = r -> length l2 = r -> length l3 = r ->
      ldot (@ladd _ Aadd l1 l2) l3 = (ldot l1 l3) + (ldot l2 l3).
  Proof.
    induction l1,l2,l3; simpl; intros; subst; try (cbv;ring); try discriminate.
    rewrite ?ldot_cons. inversion H1. inversion H0.
    rewrite IHl1 with (r:=length l1); auto. ring.
  Qed.
  
  (** ldot left distributive over lcmul and mul.
      (x * l1) . l2 = x * (l1 . l2) *)
  Lemma ldot_lcmul_distr_l : forall l1 l2 x,
      ldot (@lcmul _ Amul x l1) l2 = x * (ldot l1 l2).
  Proof.
    induction l1,l2; simpl; intros; try (cbv; ring).
    rewrite ?ldot_cons. rewrite IHl1. ring.
  Qed.

  (** ldot right distributive over lcmul and mul.
      l1 . (x * l2) = x * (l1 . l2) *)
  Lemma ldot_lcmul_distr_r : forall l1 l2 x,
      ldot l1 (@lcmul _ Amul x l2) = x * (ldot l1 l2).
  Proof.
    induction l1,l2; simpl; intros; try (cbv; ring).
    rewrite ?ldot_cons. rewrite IHl1. ring.
  Qed.

  (** ldot left distributve over map.
      dot (map f l1) l2 = f (dot l1 l2) *)
  Lemma ldot_map_distr_l :
    forall l1 l2 r (f : tA -> tA)
      (f_zero : f Azero = Azero)
      (f_add : forall a b, f (a + b) = f a + f b)
      (f_mul_l : forall a b, f a * b = f (a * b)),
      length l1 = r -> length l2 = r ->
      ldot (map f l1) l2 = f (ldot l1 l2).
  Proof.
    induction l1,l2; simpl in *; intros; subst.
    - cbv; auto.
    - cbv; auto.
    - cbv; auto.
    - rewrite ?ldot_cons.
      rewrite IHl1 with (r:=length l1); auto.
      rewrite f_add, f_mul_l. auto.
  Qed.

  (** ldot right distributve over map.
      dot l1 (map f l2) = f (dot l1 l2) *)
  Lemma ldot_map_distr_r :
    forall l1 l2 r (f : tA -> tA)
      (f_zero : f Azero = Azero)
      (f_add : forall a b, f (a + b) = f a + f b)
      (f_mul_r : forall a b, a * f b = f (a * b)),
      length l1 = r -> length l2 = r ->
      ldot l1 (map f l2) = f (ldot l1 l2).
  Proof.
    induction l1,l2; simpl in *; intros; subst.
    - cbv; auto.
    - cbv; auto.
    - cbv; auto.
    - rewrite ?ldot_cons. rewrite IHl1 with (r:=length l1); auto.
      rewrite f_add, f_mul_r. auto.
  Qed.

  (** ldot left distributve over map2.
      dot l1 (map2 l2 l3) = dot l1 l2 + dot l1 l3 *)
  Lemma ldot_map2_distr_l : forall l1 l2 l3 r,
      length l1 = r -> length l2 = r -> length l3 = r ->
      ldot l1 (map2 Aadd l2 l3) = (ldot l1 l2) + (ldot l1 l3).
  Proof.
    induction l1,l2,l3; simpl in *; intros; subst;
      try (cbv; ring); try discriminate.
    rewrite ?ldot_cons. rewrite IHl1 with l2 l3 (length l1); auto; ring.
  Qed.
  
  (** ldot right distributve over map2.
      dot (map2 l1 l2) l3 = dot l1 l3 + dot l2 l3 *)
  Lemma ldot_map2_distr_r : forall l1 l2 l3 r,
      length l1 = r -> length l2 = r -> length l3 = r ->
      ldot (map2 Aadd l1 l2) l3 = (ldot l1 l3) + (ldot l2 l3).
  Proof.
    induction l1,l2,l3; simpl in *; intros; subst; try (cbv; ring); try easy.
    rewrite ?ldot_cons.
    rewrite (IHl1 l2 l3 (length l1)); auto. ring.
  Qed.

End ldot.


(* ===================================================================== *)
(** ** Generate special list for MatrixUnit *)
Section GenerateSpecialList.

  Context `{AR:ARing}.
  Infix "+" := Aadd.
  Infix "*" := Amul.
  
  (** create a list for matrix unit, which length is n and almost all elements 
    are Azero excepts i-th is Aone. *)
  Fixpoint lunit (n i : nat) : list tA :=
    match n, i with
    | 0, _ => []
    | S n, 0 => Aone :: (repeat Azero n)
    | S n, S i => Azero :: (lunit n i)
    end.

  (* Compute lunit 0 2. (* [] *) *)
  (* Compute lunit 3 0. (* [1;0;0] *) *)
  (* Compute lunit 3 1. (* [0;1;0] *) *)
  (* Compute lunit 3 2. (* [0;0;1] *) *)
  (* Compute lunit 3 3. (* [0;0;0] *) *)

  Lemma lunit_length : forall n i, length (lunit n i) = n.
  Proof.
    induction n; auto. destruct i; simpl; auto. rewrite repeat_length. auto.
  Qed.
  
  (** lunit(n,i) [i] = Aone, when i < n *)
  Lemma lunit_Aone : forall n i, i < n -> nth i (lunit n i) Azero = Aone.
  Proof.
    induction n; try easy. destruct i; simpl; try easy.
    intros; apply IHn.
    (* since Coq_8.16.0, Arith.Lt was deprecated *)
    (* apply Lt.lt_S_n; auto. *)
    apply Nat.succ_lt_mono. auto.
  Qed.
  
  (** lunit(n,i) [j] = Azero, when i < n /\ j <> i *)
  Fact lunit_spec1 : forall n i j,
      i < n -> j <> i -> nth j (lunit n i) Azero = Azero.
  Proof.
    induction n; try easy. intros. destruct i,j; simpl; try easy.
    - apply nth_repeat.
    - apply IHn; lia.
  Qed.
  
  (** lunit(n,i) [j] = Azero, j <> i *)
  Lemma lunit_Azero : forall n i j, j <> i -> nth j (lunit n i) Azero = Azero.
  Proof.
    induction n; try easy; simpl; intros.
    - destruct j; easy.
    - destruct i,j; simpl; try easy. apply nth_repeat. apply IHn. auto.
  Qed.
  
End GenerateSpecialList.

Hint Resolve lunit_length : mat.


(* ===================================================================== *)
(** ** Convert list to fixed-length list *)
Section listN.

  Context `{M:Monoid}.
  
  Fixpoint listN (l : list tA) (n : nat) : list tA :=
    match n with
    | 0 => []
    | S n' => (hd Azero l) :: (listN (tl l) n')
    end.
  
  Lemma listN_length : forall (l : list tA) (n : nat), length (listN l n) = n.
  Proof. intros l n. revert l. induction n; intros; simpl; auto. Qed.
  
  Lemma listN_eq : forall (l : list tA), listN l (length l) = l.
  Proof. induction l; simpl; auto. f_equal; auto. Qed.

End listN.


(* ===================================================================== *)
(** ** Find non-zero element from a list *)
Section listFirstNonZero.
  Context {tA} (Azero : tA) (Aeqb : tA -> tA -> bool).
  
  (* Find the index of first non-zero element, if nothing return none. *)
  Definition listFirstNonZero (l : list tA) : option nat :=
    let fix F (l : list tA) (i : nat) : option nat :=
      match l with
      | [] => None
      | hl :: tl =>
          if Aeqb hl Azero
          then F tl (S i)
          else Some i
      end in
    F l 0.

End listFirstNonZero.

Section test.
  (* Compute listFirstNonZero 0 Nat.eqb [0;0;1;2;3]. *)
End test.


(* ===================================================================== *)
(** ** Sub list *)
Section sublist.
  Context {tA} (Azero : tA).

  Definition sublist {tA} (l : list tA) (lo n : nat) : list tA :=
    firstn n (skipn lo l).

  Lemma sublist_overflow : forall (l : list tA) lo n,
      length l <= lo -> sublist l lo n = [].
  Proof.
    intros. unfold sublist. rewrite skipn_all2; try lia. apply firstn_nil.
  Qed.
  
  Lemma sublist_Sn : forall (l : list tA) lo n,
      sublist l lo (S n) =
        if length l <=? lo
        then []
        else (nth lo l Azero) :: sublist l (S lo) n.
  Proof.
    intros. unfold sublist. simpl.
    revert lo. induction l; destruct lo; simpl; auto.
  Qed.

  Lemma sublist_cons : forall (a : tA) (l : list tA) lo n,
      sublist (a :: l) lo (S n) =
        if lo =? 0
        then a :: sublist l 0 n
        else sublist l (pred lo) (S n).
  Proof. intros. unfold sublist. simpl. destruct lo; simpl; auto. Qed.
  
End sublist.

Section test.
  (* Compute sublist [1;2;3;4;5] 1 3. *)
End test.





(* ##################################################################### *)
(* ##################################################################### *)
(* ##################################################################### *)


(* ##################################################################### *)
(** * dlist (list of list) *)


(* ===================================================================== *)
(** ** width of a dlist (dlist tA) *)
Section width.
  
  Context {tA : Type}.

  (** tA proposition that every list of a dlist has same length *)
  Definition width {tA : Type} (dl : dlist tA) (n : nat) : Prop :=
    Forall (fun l => length l = n) dl.

  (** width property should be kept by its child structure *)
  Lemma cons_width_iff : forall (l : list tA) dl n,
      width (l :: dl) n <-> length l = n /\ width dl n.
  Proof.
    intros. split; intros; inversion H; auto.
    constructor; auto.
  Qed.

  (** width property should be kept by every child element *)
  Lemma width_imply_in_length : forall (l : list tA) dl n, 
      width dl n -> In l dl -> length l = n.
  Proof.
    intros. induction dl. inv H0.
    apply cons_width_iff in H; destruct H. apply in_inv in H0. destruct H0.
    + subst. auto.
    + apply IHdl; auto.
  Qed.

  (** app operation won't change width property *)
  Lemma app_width : forall (dl1 : dlist tA) dl2 n, 
      width (dl1 ++ dl2) n <-> width dl1 n /\ width dl2 n.
  Proof.
    unfold width in *.
    induction dl1; intros; split; intros; simpl in *; inv H; auto.
    - apply IHdl1 in H3 as []. split; auto.
    - inv H0. constructor; auto. apply IHdl1. auto.
  Qed.

  (** rev operation won't change width property *)
  Lemma rev_width : forall (dl : dlist tA) n, width (rev dl) n -> width dl n.
  Proof.
    unfold width in *.
    induction dl; simpl; intros; auto.
    apply app_width in H. destruct H. inv H0. constructor; auto.
  Qed.

  (** repeat generated dlist will keep width property same as seed element *)
  Lemma repeat_width : forall (l : list tA) n k,
      length l = k -> width (repeat l n) k.
  Proof.
    unfold width. induction n; intros; simpl; auto.
  Qed.

  (** i-th row has same length *)
  Lemma dlist_nth_length : forall i c (dl : dlist tA) l,
      i < length dl -> width dl c -> length (nth i dl l) = c.
  Proof.
    unfold width. intros i c dl. revert i c.
    induction dl; intros; simpl in *. lia.
    inv H0. destruct i; auto. apply IHdl; auto. lia.
  Qed.

  (** i-th row has zero length if index overflow *)
  Lemma dlist_nth_length_overflow : forall i (dl : dlist tA) l,
      i >= length dl -> length (nth i dl l) = length l.
  Proof.
    intros i dl. revert i.
    induction dl; intros; simpl in *.
    - destruct i; auto.
    - destruct i. lia. assert (i >= length dl). lia. apply IHdl; auto.
  Qed.
  
  (** map width law *)
  Lemma width_map : forall (f: nat -> list tA) (rowIdxs:list nat) c,
      (forall i, length (f i) = c) -> width (map f rowIdxs) c.
  Proof.
    unfold width. intros f idxs. induction idxs; simpl; auto.
  Qed.

End width.


(* ===================================================================== *)
(** ** nnth : that is nth of nth of dlist *)
Section dlnth.
  Context {tA} {Azero : tA}.

  (* Notation "dl ! i ! j" := (nth j (nth i dl []) Azero). *)

End dlnth.


(* ===================================================================== *)
(** ** dlist to elements *)

Section dl2elems.
  Context {tA} {Azero : tA}.
  
  Notation "dl ! i ! j" := (nth j (nth i dl []) Azero) (at level 2, i,j at next level).

  (* 自动处理前提中含有 width 的简单情形，以自动化 dl2elems 的证明 *)
  Ltac solve_dl2elems :=
    try match goal with
    (* 若有 width (l::d) n，转换为 length l = n; width d n *)
    | H: width (?l :: ?d) ?n |- _ =>
        assert (length l = n); [inversion H; auto|];
        assert (width d n); [inversion H; auto|]; clear H
    (* 若有 [a] = [b]，转换为 a = b *)
    | |- cons ?a nil = cons ?b nil => f_equal
    end;
  (* 自动处理 list2elems 情形 *)
    try solve_list2elems
  .

  (* 1x1 matrix *)
  Lemma dl2elems_1_1 : forall (d : dlist tA),
      length d = 1 -> width d 1 -> d = [[d!0!0]].
  Proof.
    intros. repeat (destruct d; simpl in *; repeat (solve_dl2elems);
                    try apply list2elems_1; auto).
  Qed.
  
  (* 2x2 matrix *)
  Lemma dl2elems_2_2 : forall (d : dlist tA),
      length d = 2 -> width d 2 -> d = [[d!0!0; d!0!1]; [d!1!0; d!1!1]].
  Proof.
    intros. repeat (destruct d; simpl in *; repeat (solve_dl2elems);
                    try apply list2elems_2; auto).
  Qed.

  (* 3x3 matrix *)
  Lemma dl2elems_3_3 : forall (d : dlist tA),
      length d = 3 -> width d 3 ->
      d = [[d!0!0; d!0!1; d!0!2];
           [d!1!0; d!1!1; d!1!2];
           [d!2!0; d!2!1; d!2!2]].
  Proof.
    intros. repeat (destruct d; simpl in *; repeat (solve_dl2elems);
                    try apply list2elems_3; auto).
  Qed.

  (* 4x3 matrix (This demo shows that a rectangle matrix is supported also) *)
  Lemma dl2elems_4_3 : forall (d : dlist tA),
      length d = 4 -> width d 3 ->
      d = [[d!0!0; d!0!1; d!0!2];
           [d!1!0; d!1!1; d!1!2];
           [d!2!0; d!2!1; d!2!2];
           [d!3!0; d!3!1; d!3!2]].
  Proof.
    intros. repeat (destruct d; simpl in *; repeat (solve_dl2elems);
                    try apply list2elems_3; auto).
  Qed.

  (* 4x4 matrix *)
  Lemma dl2elems_4_4 : forall (d : dlist tA),
      length d = 4 -> width d 4 ->
      d = [[d!0!0; d!0!1; d!0!2; d!0!3];
           [d!1!0; d!1!1; d!1!2; d!1!3];
           [d!2!0; d!2!1; d!2!2; d!2!3];
           [d!3!0; d!3!1; d!3!2; d!3!3]].
  Proof.
    intros. repeat (destruct d; simpl in *; repeat (solve_dl2elems);
                    try apply list2elems_4; auto).
  Qed.

End dl2elems.


(* ===================================================================== *)
(** ** Properties of dlist *)
Section props_dlist.
  Context {tA : Type} {Azero : tA}.
  (* Open Scope nat. *)

  (** Two dlist equal iff all nth nth visit equal *)
  Lemma dlist_eq_iff_nth_nth :
    forall r c (dl1 dl2 : dlist tA)
      (H1 : length dl1 = r) (H2 : length dl2 = r)
      (H3 : width dl1 c) (H4 : width dl2 c),
      dl1 = dl2 <->
        (forall (i j : nat), i < r -> j < c -> 
                      (nth j (nth i dl1 []) Azero =
                         nth j (nth i dl2 []) Azero)).
  Proof.
    intros; split; intros. 
    - rewrite H. easy.
    - apply (list_eq_ext [] r); auto; intros.
      apply (list_eq_ext Azero c); auto; intros.
      apply dlist_nth_length; auto;lia.
      apply dlist_nth_length; auto;lia.
  Qed.

  (** dlist_eq is decidable *)
  Context {AeqDec : Dec (@eq tA)}.
  Lemma dlist_eq_dec : forall (dl1 dl2 : dlist tA), {dl1 = dl2} + {dl1 <> dl2}.
  Proof. apply list_eq_dec. apply list_eq_dec. apply Aeqdec. Qed.

End props_dlist.


(* ===================================================================== *)
(** ** Print a dlist *)
Section dlprt.
  Context {tA : Type}.

  Definition dlst_prt (dl : dlist tA) (p : tA -> string) : string :=
    let f := (fun s l => String.append s (String.append (lst_prt l p) strNewline)) in
    fold_left f dl "".
End dlprt.

(* Compute dlst_prt [[1;2;3];[4;5;6]] (fun n => str_alignl (nat2str n) 5). *)
(* Compute dlst_prt [[1;2;3];[4;5;6]] (fun n => str_alignr (nat2str n) 5). *)


(* ===================================================================== *)
(** ** a dlist with same element nil *)
Section dnil.
  
  Context `{M:Monoid}.
  Open Scope nat.
  
  (** a dlist that every list is nil, named as dnil *)
  Fixpoint dnil n : dlist tA :=
    match n with
    | O => nil
    | S n' => nil :: (dnil n')
    end.

  (** dnil's length law *)
  Lemma dnil_length : forall n, length (dnil n) = n.
  Proof.
    induction n; simpl; auto.
  Qed.

  (** dnil's width law *)
  Lemma dnil_width : forall n, width (dnil n) 0.
  Proof.
    unfold width; induction n; simpl; auto.
  Qed.
  
  (** dnil equal to append two child dnil *)
  Lemma dnil_app : forall n1 n2, 
      dnil (n1 + n2) = dnil n1 ++ dnil n2.
  Proof.
    induction n1,n2; simpl; try easy.
    - rewrite app_nil_r. rewrite Nat.add_0_r. easy.
    - rewrite IHn1. simpl. easy.
  Qed.

  (** width dl is zero imply it is a dnil *)
  Lemma dlist_w0_eq_dnil : forall (dl : dlist tA), 
      width dl 0 -> dl = dnil (length dl).
  Proof.
    unfold width; induction dl; simpl; auto.
    intros. inv H. f_equal; auto. 
    apply length_zero_iff_nil; auto.
  Qed.

  (** rev a dnil is itself *)
  Lemma dnil_rev : forall n, rev (dnil n) = dnil n.
  Proof.
    induction n; simpl; auto. rewrite IHn. clear IHn.
    induction n; simpl; auto. f_equal. auto.
  Qed.

End dnil.


(* ===================================================================== *)
(** ** map2 for dlist *)
Section dlist_map2.
  
  Context {tA tB tC : Type}.
  (* Open Scope nat. *)

  (** map2 dnil dl = dnil *)
  Lemma map2_dnil_l : forall (dl : @dlist tB) (f : tA -> tB -> tC) n, 
      length dl = n -> map2 (map2 f) (dnil n) dl = dnil n.
  Proof.
    intros. revert dl H. induction n; intros; simpl; try easy.
    destruct dl. inversion H. inversion H. rewrite H1. f_equal. auto.
  Qed.

  (** map2 dl dnil = dnil *)
  Lemma map2_dnil_r : forall (dl:dlist tA) (f : tA -> tB -> tC) n, 
      length dl = n -> map2 (map2 f) dl (dnil n) = dnil n.
  Proof.
    intros. revert dl H. induction n; intros; simpl; try easy.
    - rewrite map2_nil_r. easy.
    - destruct dl. easy. simpl. rewrite IHn; auto. rewrite map2_nil_r. easy.
  Qed.

  (** (map2 (map2 f) d1 d2)[i,j] = f (d1[i,j]) (d2[i,j]) *)
  Lemma nth_nth_map2_map2_rw : forall (f : tA -> tA -> tA) (d1 d2 : dlist tA) r c i j l a,
      length d1 = r -> width d1 c -> length d2 = r -> width d2 c ->
      i < r -> j < c ->
      nth j (nth i (map2 (map2 f) d1 d2) l) a =
        f (nth j (nth i d1 l) a) (nth j (nth i d2 l) a).
  Proof.
    clear. intros.
    erewrite nth_map2 with (n:=r); auto.
    erewrite nth_map2 with (n:=c); auto.
    apply dlist_nth_length; auto; lia.
    apply dlist_nth_length; auto; lia.
  Qed.

  (** (map (map f) d)[i,j] = f (d[i,j]) *)
  Lemma nth_nth_map_map : forall (d : dlist tA) (f : tA -> tA) r c i j l a,
      length d = r -> width d c ->
      i < r -> j < c ->
      nth j (nth i (map (map f) d) l) a = f (nth j (nth i d l) a).
  Proof.
    intros d f r. revert d f. induction r.
    - intros. lia.
    - intros. destruct d as [|dh dt]; simpl in *. lia.
      inversion H. inversion H0. destruct i.
      + apply nth_map with (n:=c); auto.
      + apply IHr with (c:=c); auto. inv H0; auto. lia.
  Qed.
  
End dlist_map2.


(* ===================================================================== *)
(** ** Convert between dlist and function *)
Section f2dl_dl2f.
  Context {tA : Type} (Azero : tA).

  Definition f2dl (r c : nat) (f : nat -> nat -> tA) : dlist tA :=
    map (fun i => f2l c (f i)) (seq 0 r).

  Definition dl2f (r c : nat) (dl : dlist tA) : nat -> nat -> tA :=
    fun i j => nth j (nth i dl []) Azero.

  Lemma f2dl_length : forall r c f, length (f2dl r c f) = r.
  Proof.
    intros. unfold f2dl. rewrite map_length. apply seq_length.
  Qed.

  Lemma f2dl_width : forall r c f, width (f2dl r c f) c.
  Proof.
    unfold f2dl,width.
    induction r; intros; simpl; try constructor.
    - apply f2l_length.
    - rewrite <- seq_shift. rewrite List.map_map.
      apply IHr.
  Qed.

  (** (f2dl f)[i,j] = f i j *)
  Lemma nth_f2dl : forall {r c} f l a i j,
      i < r -> j < c -> nth j (nth i (f2dl r c f) l) a = f i j.
  Proof.
    intros. unfold f2dl. rewrite nth_map_seq; auto. rewrite nth_f2l; auto.
  Qed.

End f2dl_dl2f.

Section test.
  (** [[1;2;3];[4;5;6];[7;8;9]] *)
  Let f := fun i j => i * 3 + j + 1.
  Let dl := f2dl 3 3 f.
  (* Compute dl. *)

  Let g := dl2f 0 3 3 dl.
  (* Compute (g 0 0, g 0 1, g 0 2, g 1 0, g 1 1, g 1 2, g 2 0, g 2 1, g 2 2). *)
End test.  


(* ===================================================================== *)
(** ** Convert between row and col. eg, [1;2;3] <-> [[1];[2];[3]] *)
Section convert_row_and_col.

  Context `{M:Monoid}.
  
  (** Convert a list to a dlist, it looks like converting a row to a column. *)
  Fixpoint row2col (l : list tA) : dlist tA :=
    match l with
    | [] => []
    | x :: tl => [x] :: (row2col tl)
    end.
  
  (** row2col length law *)
  Lemma row2col_length : forall l, length (row2col l) = length l.
  Proof. induction l; simpl; intros; auto. Qed.
  
  (** row2col width law *)
  Lemma row2col_width : forall l, width (row2col l) 1.
  Proof. unfold width; induction l; simpl; intros; auto. Qed.

  Lemma nth_row2col : forall l i,
      i < length l ->
      nth i (row2col l) [] = [nth i l Azero].
  Proof.
    induction l.
    - intros. simpl in *. lia.
    - intros. simpl in *. destruct i; try easy.
      apply IHl. auto with arith.
  Qed.
  
  (** Convert a dlist to a list which contain head element, it looks like 
    converting a column to a row. *)
  Fixpoint col2row (dl : dlist tA) : list tA :=
    match dl with
    | [] => []
    | l :: tl => (hd Azero l) :: (col2row tl)
    end.
  
  (** Convert a dlist to list then convert it to a dlist, equal to original dlist. *)
  Lemma row2col_col2row : forall (dl : dlist tA),
      width dl 1 -> row2col (col2row dl) = dl.
  Proof.
    unfold width; induction dl; simpl; auto; intros. inv H.
    f_equal; auto.
    destruct a; simpl in *; try easy. inv H2.
    apply length_zero_iff_nil in H0. subst. easy.
  Qed.
  
  (** Convert a list to dlist then convert it to a list, equal to original 
    list. *)
  Lemma col2row_row2col : forall (l : list tA), 
      col2row (row2col l) = l.
  Proof.
    induction l; simpl; auto; intros. rewrite IHl. easy.
  Qed.
  
End convert_row_and_col.


(* ===================================================================== *)
(** ** head column of a dlist *)
Section hdc.
  Context {tA : Type} (Azero : tA).
  
  (** Get head column of a dlist *)
  Fixpoint hdc (dl : dlist tA) : list tA :=
    match dl with
    | [] => []
    | l :: tl => (hd Azero l) :: (hdc tl)
    end.
  
  (** hdc length law *)
  Lemma hdc_length : forall dl, length (hdc dl) = length dl.
  Proof. induction dl; simpl; auto. Qed.
  
End hdc.


(* ===================================================================== *)
(** ** tail columns of a dlist *)
Section tlc.
  
  Context {tA : Type}.
  
  (** Get tail columns of a dlist *)
  Fixpoint tlc (dl : dlist tA) : dlist tA :=
    match dl with
    | [] => []
    | l :: tl => (tail l) :: (tlc tl)
    end.
  
  (** tlc length law *)
  Lemma tlc_length : forall dl, length (tlc dl) = length dl.
  Proof. induction dl; simpl; auto. Qed.
  
  (** tlc width law when width equal to 0 *)
  Lemma tlc_width0 : forall dl, width dl 0 -> width (tlc dl) 0.
  Proof.
    unfold width; induction dl; simpl; auto. intros. inv H; constructor; auto.
    apply length_zero_iff_nil in H2. subst. auto.
  Qed.
  
  (** tlc width law when width not equal to 0 *)
  Lemma tlc_widthS : forall dl c, width dl (S c) -> width (tlc dl) c.
  Proof.
    unfold width; induction dl; simpl; auto.
    intros. inv H; constructor; auto.
    destruct a; auto. easy.
  Qed.
  
End tlc.


(* ===================================================================== *)
(** ** construct a dlist with a list and a dlist by column *)
Section consc.
  Context {tA : Type} {Azero : tA}.
  
  (** Construct a dlist by column with a list and a dlist *)
  Fixpoint consc (l : list tA) (dl : dlist tA) : dlist tA :=
    match l, dl with
    | xl :: tl, xdl :: tdl => (xl :: xdl) :: (consc tl tdl)
    | _, _ => []
    end.
  
  (** consc is injective *)
  Lemma consc_inj : forall (l1 l2 : list tA) (dl1 dl2 : dlist tA) n,
      length l1 = n -> length l2 = n -> length dl1 = n -> length dl2 = n ->
      consc l1 dl1 = consc l2 dl2 -> (l1 = l2) /\ dl1 = dl2.
  Proof.
    induction l1.
    - intros. simpl in *. subst. apply length_zero_iff_nil in H0,H1,H2.
      subst. easy.
    - intros. destruct l2,dl1,dl2; simpl in *; subst; try easy.
      inv H0. inv H1. inv H2.
      inv H3. eapply IHl1 in H6; auto. inv H6. auto.
  Qed.
  
  (** consc length law *)
  Lemma consc_length : forall l dl r,
      length l = r -> length dl = r ->
      length (consc l dl) = r.
  Proof.
    induction l,dl; simpl; intros; auto. destruct r. inversion H. f_equal.
    inversion H. inversion H0. subst. apply IHl; auto.
  Qed.
  
  (** consc width law *)
  Lemma consc_width : forall l dl c,
      length l = length dl -> width dl c ->
      width (consc l dl) (S c).
  Proof.
    unfold width; induction l,dl; simpl; intros; auto.
    inv H. inv H0. constructor; auto.
  Qed.

  (** width dl c -> length ((l @@ dl)[i]) = c + 1 *)
  Lemma nth_consc_length : forall (l : list tA) dl l0 i r c,
      length l = r -> length dl = r -> width dl c -> i < r ->
      length (nth i (consc l dl) l0) = S c.
  Proof.
    intros l dl l0 i r. revert l dl l0 i. induction r; intros. lia.
    destruct l, dl; simpl in *; try lia. inversion H1. destruct i. 
    - simpl; auto.
    - apply IHr; auto. lia.
  Qed.
  
  (** consc with hdc and tlc of a dnil generate lzero *)
  Lemma consc_hdc_tlc_width0 : forall dl r, 
      length dl = r -> width dl 0 -> 
      consc (hdc Azero dl) (tlc dl) = row2col (repeat Azero r).
  Proof.
    unfold width; induction dl; simpl; intros; subst; try easy.
    inv H0. apply length_zero_iff_nil in H2. subst. simpl. f_equal.
    apply IHdl; auto.
  Qed.
  
  (** consc with hdc and tlc of a dlist generate itself *)
  Lemma consc_hdc_tlc_widthS : forall dl c, 
      width dl (S c) ->
      consc (hdc Azero dl) (tlc dl) = dl.
  Proof.
    unfold width; induction dl; simpl; intros; auto. inv H.
    f_equal; auto.
    - destruct a; simpl in *. easy. easy.
    - apply IHdl with (c:=c). auto.
  Qed.

  (** consc decompose.
    x1::l1 ++ l2::dl2 = (x::l2) :: (l1 ++ dl2)  *)
  Lemma consc_decompose : forall x1 l1 l2 dl2,
      consc (x1::l1) (l2::dl2) = (x1::l2) :: (consc l1 dl2).
  Proof.
    intros. simpl. easy.
  Qed.
  
  (** repeat (x :: l) decomposition *)
  Lemma repeat_consc : forall l x n,
      repeat (x :: l) n = consc (repeat x n) (repeat l n).
  Proof.
    induction n; simpl; auto. rewrite IHn. easy.
  Qed.

  (** Simplify consc and nthj0 *)
  Lemma consc_nthj0 : forall l dl l0 a r i,
      length l = r -> length dl = r -> i < r ->
      nth 0 (nth i (consc l dl) l0) a = nth i l a.
  Proof.
    induction l,dl; intros; simpl in *; try lia.
    destruct i; simpl; auto. eapply IHl; auto; try lia.
  Qed.
  
  (** Simplify consc and nthSj *)
  Lemma consc_nthSj : forall l dl l0 a r c i j,
      length l = r -> length dl = r -> i < r -> j < c ->
      nth (S j) (nth i (consc l dl) l0) a = nth j (nth i dl l0) a.
  Proof.
    induction l,dl; intros; simpl in *; try lia.
    destruct i; simpl; auto. eapply IHl; auto; try lia.
  Qed.

  (** If width dl is 0, then consc l dl = row2col l *)
  Lemma consc_dl_w0 : forall (l:list tA) (dl:dlist tA),
      length l = length dl ->
      width dl 0 -> consc l dl = row2col l.
  Proof.
    induction l; intros; simpl in *. auto.
    destruct dl; simpl in *. lia. inversion H. inversion H0.
    rewrite IHl; auto. f_equal.
    apply length_zero_iff_nil in H4. subst. auto.
  Qed.

End consc.


(* ===================================================================== *)
(** ** nth column of a dlist *)
Section nthc.
  Context {tA : Type} {Azero : tA}.
  
  (** Get nth column of a dlist. *)
  Fixpoint nthc (dl : dlist tA) (j : nat) : list tA :=
    match dl with
    | [] => []
    | l :: tl => (nth j l Azero) :: (nthc tl j)
    end.
  
  Fixpoint nthc_error (dl : dlist tA) (j : nat) : option (list tA) :=
    match dl with
    | [] => Some []
    | l :: tl =>
        match nth_error l j, nthc_error tl j with
        | Some a, Some l' => Some (a :: l')
        | _, _ => None
        end
    end.
  
  (** nthc length law *)
  Lemma nthc_length : forall dl j, length (nthc dl j) = length dl.
  Proof.
    induction dl; simpl; auto.
  Qed.

  (* nthc_error when overflow *)
  Lemma nthc_error_overflow_case1 : forall dl c j,
      length dl > 0 -> width dl c -> j >= c -> nthc_error dl j = None.
  Proof.
    unfold width. induction dl; intros; simpl.
  Abort.
  
  Lemma nthc_error_overflow_case2 : forall dl c j,
      ~width dl c -> nthc_error dl j = None.
  Proof.
    unfold width.
    induction dl; intros; simpl.
    - destruct H. constructor.
    - rewrite Forall_cons_iff in H. apply not_and_or in H. destruct H.
      Abort.
    
  (* nthc_error is equal to nthc *)
  Lemma nthc_error_valid : forall dl c j,
      width dl c -> j < c ->
      Some (nthc dl j) = nthc_error dl j.
  Proof.
    induction dl; intros; simpl; auto.
    Abort.

  (** nthc_error length law *)
  Lemma nthc_error_length : forall dl c j,
      width dl c -> j < c ->
      exists l, nthc_error dl j = Some l /\ length l = length dl.
  Proof.
    induction dl; intros; simpl.
    - exists []. auto.
    - Abort.

End nthc.

Arguments nthc {tA}.


(* ===================================================================== *)
(** ** Append two objects of dlist type to one object of dlist *)
Section dlist_app.
  
  Context {tA : Type}.
  
  (** dlist append by row *)
  Definition dlappr := app.
  
  (** dlist apend by column *)
  Fixpoint dlappc (dl1 dl2 : dlist tA) : dlist tA :=
    match dl1, dl2 with
    | l1 :: tl1, l2 :: tl2 => (app l1 l2) :: (dlappc tl1 tl2)
    | _, _ => []
    end.

  (** Length of dlappc is same as input *)
  Lemma dlappc_length : forall (dl1 dl2 : dlist tA) r,
      length dl1 = r -> length dl2 = r -> length (dlappc dl1 dl2) = r.
  Proof.
    induction dl1, dl2; intros; simpl in *; auto.
    destruct r. lia. f_equal. apply IHdl1. lia. lia.
  Qed.

  (** Width of dlappc is the sum of each columns *)
  Lemma dlappc_width : forall (dl1 dl2 : dlist tA) c1 c2,
      width dl1 c1 -> width dl2 c2 -> width (dlappc dl1 dl2) (c1 + c2).
  Proof.
    induction dl1, dl2; intros; simpl in *; auto.
    constructor. constructor. constructor.
    unfold width in *.
    constructor.
    - inv H. inv H0. apply app_length.
    - apply IHdl1. inv H; auto. inv H0; auto.
  Qed.

End dlist_app.

Notation "l @@ r" := (dlappc l r) (at level 40) : list_scope.


(* ===================================================================== *)
(** ** Zero dlist *)
Section dlzero.
  Context {tA : Type} {Azero : tA}.
  
  (** dlist constructed by repeated lzero, named as dlzero *)
  Definition dlzero r c := repeat (lzero Azero c) r.

  (** dlzero rewrite *)
  Lemma dlzero_rw : forall r c, repeat (lzero Azero c) r = dlzero r c.
  Proof.
    easy.
  Qed.
  
  (** dlzero with S r rows could be splited to two parts *)
  Lemma dlzero_Sr : forall {r c}, dlzero (S r) c = (lzero Azero c) :: (dlzero r c).
  Proof.
    intros. simpl. cbn. easy.
  Qed.
  
  (** dlzero with 0 rows equal to dnil *)
  Lemma dlzero_dnil : forall {c}, dlzero c 0 = dnil c.
  Proof.
    induction c; simpl; try easy. rewrite <- IHc. easy.
  Qed.
  
  (** dlzero heigth law *)
  Lemma dlzero_length : forall {r c}, length (dlzero r c) = r.
  Proof.
    intros. apply repeat_length.
  Qed.
  
  (** dlzero width law *)
  Lemma dlzero_width : forall {r c}, width (dlzero r c) c.
  Proof.
    unfold width, dlzero; induction r; intros; simpl; auto. constructor; auto.
    apply lzero_length.
  Qed.

  (** dlzero[i] = lzero *)
  Lemma nth_dlzero : forall r c i,
      i < r -> nth i (dlzero r c) [] = lzero Azero c.
  Proof. intros. unfold dlzero. rewrite nth_repeat_same; auto. Qed.
  
  (** dlzero with 0 rows equal to dnil *)
  Lemma dlzero_w0_eq_dnil : forall r, (dlzero r 0) = dnil r.
  Proof. 
    induction r; try easy. unfold dlzero in *. simpl in *. rewrite IHr. easy.
  Qed.
  
  (** append two dlzeros by row equal to whole *)
  Lemma dlzero_app_row : forall r1 r2 c,
      dlzero r1 c ++ dlzero r2 c = dlzero (r1 + r2) c.
  Proof.
    unfold dlzero. intros. rewrite repeat_app. easy.
  Qed.
  
  (** append two dlzeros by column equal to whole *)
  Lemma dlzero_app_col : forall r c1 c2,
      (dlzero r c1) @@ (dlzero r c2) = dlzero r (c1 + c2).
  Proof.
    induction r; intros; simpl; try easy. unfold dlzero,lzero in *.
    rewrite IHr. simpl. rewrite repeat_app. easy.
  Qed.

End dlzero.

Arguments dlzero {tA}.


(* ===================================================================== *)
(** ** transpose a dlist *)
Section dltrans.
  Context {tA : Type} {Azero : tA}.
  
  (** Transposition of a dlist *)
  (* Idea: fetch row as column one bye one, generate a dlist with c rows if 
      given c is <= column of input dlist.

      Note that, we give c to support dlist_0_c situation.
      eg: 
      [] 3 => [[];[];[]]
      [[];[];[]] 0 => []
   *)
  Fixpoint dltrans (dl : dlist tA) (c : nat) : dlist tA :=
    match dl with
    | [] => @dnil tA c
    | l :: tl => consc l (dltrans tl c)
    end.

  (** dltrans length law *)
  Lemma dltrans_length : forall dl c, 
      width dl c ->
      length (dltrans dl c) = c.
  Proof.
    induction dl; intros; simpl; auto.
    - rewrite dnil_length. auto.
    - inversion H. rewrite consc_length with (r:=c); auto.
  Qed.
  
  (** dltrans width law *)
  Lemma dltrans_width : forall dl r c, 
      length dl = r -> width dl c -> width (dltrans dl c) r.
  Proof.
    unfold width; induction dl; intros; simpl in *; auto.
    - induction c; simpl in *; auto.
    - rewrite <- H. inv H0. apply consc_width.
      + rewrite dltrans_length; auto.
      + apply IHdl; auto. 
  Qed.
  
  (** dltrans dnil = [] *)
  Lemma dltrans_nil : forall n, dltrans (dnil n) 0 = [].
  Proof.
    intros. destruct n; simpl. reflexivity. easy.
  Qed.
  
  (** dltrans consr = consc dltrans *)
  Lemma dltrans_consr : forall dl l c,
      dltrans (l :: dl) c = consc l (dltrans dl c).
  Proof.
    intros. simpl. easy.
  Qed.
  
  (** dltrans consc = consr dltrans *)
  Lemma dltrans_consc : forall dl l r c,
      length l = r -> length dl = r -> width dl c ->
      dltrans (consc l dl) (S c) = l :: (dltrans dl c).
  Proof.
    unfold width; induction dl; simpl; intros; subst.
    - destruct l; simpl; try easy.
    - destruct l. easy.
      inv H0. inv H1.
      specialize (IHdl l (length l) (length a) eq_refl H2 H4).
      simpl.
      destruct (dltrans (consc l dl) (S (length a))). easy. inv IHdl. auto.
  Qed.
  
  (** dltrans twice return back *)
  Lemma dltrans_dltrans : forall dl r c,
      length dl = r -> width dl c ->
      dltrans (dltrans dl c) r = dl.
  Proof.
    induction dl; intros; simpl in *.
    - subst. destruct c; simpl; auto.
    - destruct r. easy. inv H. inv H0.
      unfold width in *.
      rewrite dltrans_consc with (r:=length a);
        auto using dltrans_length, dltrans_width.
      f_equal; auto.
  Qed.
  
  (** dltrans dlzero<r,c> = dlzero<c,r> *)
  Lemma dltrans_zero : forall r c,
      dltrans (dlzero Azero r c ) c = dlzero Azero c r.
  Proof.
    induction r; intros; simpl; auto. rewrite dlzero_dnil; easy.
    unfold dlzero in *; simpl in *. rewrite IHr.
    rewrite repeat_consc. easy.
  Qed.

  (** (dltrans dl)[i,j] = dl[j,i] *)
  Lemma dltrans_ij : forall (dl:dlist tA) r c a i j,
      length dl = r -> width dl c ->
      i < r -> j < c ->
      nth i (nth j (dltrans dl c) []) a = nth j (nth i dl []) a.
  Proof.
    induction dl; intros; simpl in *.
    - subst. lia.
    - destruct r. lia. inversion H. inversion H0.
      destruct i.
      + erewrite consc_nthj0; auto. rewrite dltrans_length; auto. lia.
      + erewrite consc_nthSj; auto. eapply IHdl; auto. lia.
        rewrite dltrans_length; auto. lia.
  Qed.
  
  (** (dltrans dl)[i,i] = dl[i,i] *)
  Lemma dltrans_ii : forall (dl:dlist tA) n a i,
      length dl = n -> width dl n ->
      nth i (nth i (dltrans dl n) []) a = nth i (nth i dl []) a.
  Proof.
    intros.
    destruct (i <? n) eqn:i_lt_n.
    - apply Nat.ltb_lt in i_lt_n. erewrite dltrans_ij; auto. lia.
    - apply Nat.ltb_ge in i_lt_n.
      repeat rewrite !nth_overflow; auto; simpl; try lia.
      rewrite dltrans_length; auto.
  Qed.
  
  (** (fun i => (dltrans dl)[i,i]) = (fun i => dl[i,i]) *)
  Lemma dltrans_ii_fun : forall (dl:dlist tA) n a,
      length dl = n -> width dl n ->
      (fun i : nat => nth i (nth i (dltrans dl n) []) a) = (fun i => nth i (nth i dl []) a).
  Proof.
    intros. apply functional_extensionality.
    intros. apply dltrans_ii; auto.
  Qed.
  
End dltrans.

Global Hint Resolve
  dltrans_length
  dltrans_width : mat.


(* ===================================================================== *)
(** ** dlist unit, like a identity matrix *)
Section dlunit.
  Context {tA : Type} {Azero Aone : tA}.
  
  (** Build a identity matrix with dlist. *)
  (* there are 4 parts of a dlunit [n x n]: 
      left top element [1 x 1], 
      right top list [1 x (n-1)], 
      left bottom list [(n-1) x 1],
      right bottom square is another small dlunit [(n-1) x (n-1)] *)
  Fixpoint dlunit (n : nat) : dlist tA :=
    match n with
    | O => []
    | S n0 => (Aone :: (repeat Azero n0)) :: (consc (repeat Azero n0) (dlunit n0))
    end.
  
  (** dlunit length law *)
  Lemma dlunit_length : forall {n}, length (dlunit n) = n.
  Proof.
    induction n; simpl; auto. f_equal.
    rewrite consc_length with (r:=n); auto. apply repeat_length.
  Qed.
  
  (** dlunit width law *)
  Lemma dlunit_width : forall {n}, width (dlunit n) n.
  Proof.
    unfold width; induction n; simpl; auto. constructor.
    - simpl. f_equal. apply repeat_length.
    - apply consc_width; auto. rewrite repeat_length, dlunit_length; auto.
  Qed.

  Hint Resolve dlunit_length dlunit_width : mat.
  
  (** length(dlunit[i]) = n  *)
  Lemma nth_dlunit_length : forall n i l,
      i < n -> length (nth i (dlunit n) l) = n.
  Proof.
    induction n; intros. lia. simpl. destruct i.
    - simpl. rewrite repeat_length. auto.
    - rewrite nth_consc_length with (r:=n)(c:=n); auto with mat. lia.
  Qed.

  (** (dlunit)[i,i] = 1 *)
  Lemma dlunit_ii : forall n i l a, i < n -> nth i (nth i (dlunit n) l) a = Aone.
  Proof.
    induction n; intros. lia. destruct i; simpl. auto.
    rewrite consc_nthSj with (r:=n) (c:=n); try lia; auto with mat.
    apply IHn. lia.
  Qed.
    
  (** i<>j -> (dlunit)[i,j] = 0 *)
  Lemma dlunit_ij : forall n i j l a,
      i < n -> j < n -> i <> j -> nth j (nth i (dlunit n) l) a = Azero.
  Proof.
    induction n; intros. lia. destruct i,j; simpl; auto; try lia.
    - apply nth_repeat_same. lia.
    - rewrite consc_nthj0 with (r:=n); auto with mat; try lia.
      apply nth_repeat_same; lia.
    - rewrite consc_nthSj with (r:=n)(c:=n); auto with mat; try lia.
      apply IHn; lia.
  Qed.
  
  (** transpose dlunit keep unchanged *)
  Lemma dltrans_dlunit : forall {n}, 
      let u := dlunit n in
      dltrans u n = u.
  Proof.
    simpl. induction n; simpl; try easy.
    assert ((dltrans (consc (repeat Azero n) (dlunit n)) (S n)) =
              (repeat Azero n) :: (dltrans (dlunit n) n)).
    { apply dltrans_consc with (r:=n).
      apply repeat_length. apply dlunit_length. apply dlunit_width. }
    destruct (dltrans (consc (repeat Azero n) (dlunit n)) (S n)). easy.
    inv H. f_equal. f_equal. auto.
  Qed.

End dlunit.

Arguments dlunit {tA}.

Hint Resolve
  dlunit_length dlunit_width
  : mat.



(* ===================================================================== *)
(** ** map of dlist with f : tA -> tB *)
Section dmap_A_B.
  Context {tA tB : Type} (f : tA -> tB).
  
  (** map operation to dlist *)
  Definition dmap dl := map (map f) dl.

  (** dmap length law *)
  Lemma dmap_length : forall dl, length (dmap dl) = length dl.
  Proof.
    induction dl; simpl; auto.
  Qed.
  
  (** dmap width law *)
  Lemma dmap_width : forall dl n, 
      width dl n <-> width (dmap dl) n.
  Proof.
    unfold width; induction dl; intros; split; intros; simpl in *; try easy.
    - inv H. constructor. apply map_length. apply IHdl. auto.
    - inv H. constructor. rewrite map_length. auto.
      apply IHdl. auto.
  Qed.
  
  (** dmap effect equal to map to first head and dmap to tail rows *) 
  Lemma dmap_cons : forall l dl, dmap (l :: dl) = (map f l) :: (dmap dl).
  Proof.
    intros. simpl. easy.
  Qed.
  
  (** dmap distributive law by append *)
  Lemma dmap_app : forall dl1 dl2,
      dmap (dl1 ++ dl2) = (dmap dl1) ++ (dmap dl2).
  Proof.
    induction dl1; destruct dl2; simpl in *; rewrite ?app_nil_r; try easy.
    rewrite IHdl1. easy.
  Qed.
  
  (** dmap dnil = dnil *)
  Lemma dmap_dnil : forall n, dmap (dnil n) = dnil n.
  Proof.
    induction n; simpl; try easy. rewrite IHn. easy.
  Qed.

  (** (map f l) @@ (dmap f dl) = dmap f (l @@ dl)  *)
  Lemma consc_map_dmap : forall l dl,
      consc (map f l) (dmap dl) = dmap (consc l dl).
  Proof.
    induction l; intros; simpl. auto.
    destruct dl; simpl. auto.
    rewrite IHl. auto.
  Qed.
  
  (** dltrans and dmap *)
  Lemma dltrans_dmap : forall dl c,
      width dl c ->
      dltrans (dmap dl) c = dmap (dltrans dl c).
  Proof.
    induction dl; intros; simpl in *. rewrite dmap_dnil; auto. inversion H.
    rewrite IHdl; auto. apply consc_map_dmap.
  Qed.
  
End dmap_A_B.

Hint Unfold dmap : mat.


(* ===================================================================== *)
(** ** Extra properties of dmap *)
Section dmap_A_B_C.
  Context {tA tB tC : Type}.

  (** dmap extensional law  *)
  Lemma dmap_ext : forall dl (f g : tA -> tB) (H : forall a, f a = g a),
      dmap f dl = dmap g dl.
  Proof.
    intros. unfold dmap.
    apply map_ext. intros. induction a; simpl; auto. f_equal; auto.
  Qed.

  (** dmap f (dmap g dl) = dmap (f . g) dl  *)
  Lemma dmap_dmap : forall dl (f : tA -> tB) (g : tB -> tC),
      dmap g (dmap f dl) = dmap (fun x => g (f x)) dl.
  Proof. induction dl; intros; simpl. auto. f_equal; auto. apply map_map. Qed.
  
End dmap_A_B_C.


(* ===================================================================== *)
(** ** map of dlist with f : tA -> tA *)
Section dmap_A_A.
  Context {tA : Type} {Azero : tA}.

  (** dmap (fun x => Azero) dl = dlzero Azero r c *)

  Lemma dmap_eq_zero : forall {r c} dl,
      length dl = r -> width dl c ->
      dmap (fun (x : tA) => Azero) dl = dlzero Azero r c.
  Proof.
    intros. unfold dmap,dlzero.
    
    (* Note that, use "map_eq_zero" cannot prove this lemma.
       Although this method looks very simple. *)
    (* apply map_eq_zero; auto. intros. apply map_eq_zero; try easy. *)
    
    revert r c H H0.
    induction dl; intros; simpl in *.
    - subst. easy.
    - destruct r; try easy. inv H. inv H0. simpl. f_equal.
      + apply map_eq_zero; auto.
      + apply IHdl; auto.
  Qed.

End dmap_A_A.


(* ===================================================================== *)
(** ** map2 of dlist *)
Section dmap2.
  Context {tA tB tC : Type} (f : tA -> tB -> tC).
  
  (** map operation to two dlists *)
  Definition dmap2 dl1 dl2 := map2 (map2 f) dl1 dl2.
  
  (** dmap2 length law *)
  Lemma dmap2_length : forall dl1 dl2,
      length dl1 = length dl2 -> length (dmap2 dl1 dl2) = length dl1.
  Proof.
    induction dl1,dl2; simpl; auto.
  Qed.
  
  (** dmap2 width law *)
  Lemma dmap2_width : forall dl1 dl2 n,
      width dl1 n -> width dl2 n -> width (dmap2 dl1 dl2) n.
  Proof. 
    unfold width; induction dl1; intros; simpl in *; auto.
    destruct dl2; auto. inv H. inv H0. constructor.
    apply map2_length; auto. apply IHdl1; auto.
  Qed.
  
  (** dmap2 and consr *)
  Lemma dmap2_consr : forall dl1 dl2 l1 l2,
      dmap2 (l1 :: dl1) (l2 :: dl2) =
        (map2 f l1 l2) :: (dmap2 dl1 dl2).
  Proof.
    intros. simpl. easy.
  Qed.
  
  (** dmap2 and consc *)
  Lemma dmap2_consc : forall l1 dl1 l2 dl2 c,
      length l1 = length dl1 ->
      length l2 = length dl2 ->
      width dl1 c ->
      width dl2 c ->
      dmap2 (consc l1 dl1) (consc l2 dl2) =
        consc (map2 f l1 l2) (dmap2 dl1 dl2).
  Proof.
    unfold width; induction l1,dl1,l2,dl2; simpl; intros; try easy.
    (* destruct r,t; try easy. *)
    inv H. inv H0. inv H1. inv H2. inv H3. inv H4.
    f_equal; try easy. apply IHl1 with (c:=length l); auto.
  Qed.
  
  (** dmap2 and add *)
  Lemma dmap2_app : forall dla1 dla2 dlb1 dlb2,
      length dla1 = length dlb1 ->
      length dla2 = length dlb2 ->
      dmap2 (dla1 ++ dla2) (dlb1 ++ dlb2) =
        (dmap2 dla1 dlb1) ++ (dmap2 dla2 dlb2).
  Proof.
    intros. unfold dmap2. apply map2_app; auto.
  Qed.
  
  (** dmap2 dnil dl = dnil *)
  Lemma dmap2_dnil_l : forall dl n,
      length dl = n ->
      dmap2 (dnil n) dl = dnil n.
  Proof.
    intros. unfold dmap2. rewrite map2_dnil_l; easy.
  Qed.

  (** dmap2 dl dnil = dnil *)
  Lemma dmap2_dnil_r : forall dl n,
      length dl = n ->
      dmap2 dl (dnil n) = dnil n.
  Proof.
    intros. unfold dmap2. rewrite map2_dnil_r; easy.
  Qed.

  Lemma dmap2_tail : forall dl1 dl2,
      length dl1 = length dl2 ->
      tl (dmap2 dl1 dl2) = dmap2 (tl dl1) (tl dl2).
  Proof.
    intros. unfold dmap2. apply tail_map2_dlist.
  Qed.

  (** dltrans and dmap2 *)
  Lemma dltrans_dmap2 : forall dl1 dl2 c,
      length dl1 = length dl2 ->
      width dl1 c -> width dl2 c ->
      dltrans (dmap2 dl1 dl2) c =
        dmap2 (dltrans dl1 c) (dltrans dl2 c).
  Proof.
    unfold width; induction dl1; intros; simpl in *; subst.
    rewrite dmap2_dnil_l; auto using dltrans_length.
    destruct dl2; simpl.
    - inv H.
    - inv H. inv H0. inv H1. rewrite IHdl1; auto.
      erewrite dmap2_consc; auto using dltrans_width, dltrans_length; try easy.
      rewrite dltrans_length; auto.
      rewrite dltrans_length; auto.
  Qed.
  
End dmap2.


(* ===================================================================== *)
(** ** dmap2 with same base type *)
Section dmap2_sametype.
  Context `{HMonoid : Monoid}.
  Infix "+" := Aadd.

  (** (dl1 . dl2) . dl3 = dl1 . (dl2 . dl3) *)
  Lemma dmap2_assoc : forall (dl1 dl2 dl3 : dlist tA),
      dmap2 Aadd (dmap2 Aadd dl1 dl2) dl3 =
        dmap2 Aadd dl1 (dmap2 Aadd dl2 dl3).
  Proof.
    induction dl1,dl2,dl3; simpl; auto. f_equal; auto. apply map2_assoc.
  Qed.
  
  (** dmap2 with dmap of two components *)
  Lemma dmap2_dmap_dmap : forall (f1 f2 g : tA -> tA) (h : tA -> tA -> tA) 
                            (H : forall x, g x = h (f1 x) (f2 x)) l,
      dmap2 h (dmap f1 l) (dmap f2 l) = dmap g l.
  Proof.
    induction l; simpl; auto. rewrite IHl. f_equal; try easy.
    apply map2_map_map. easy.
  Qed.

  (** dmap2 over dmap is homorphism *)
  Lemma dmap2_dmap_hom : forall (Aopp : tA -> tA)
                           (H : forall a b : tA, (Aopp (a + b) = (Aopp a) + (Aopp b)))
                           d1 d2,
      dmap2 Aadd (dmap Aopp d1) (dmap Aopp d2) = dmap Aopp (dmap2 Aadd d1 d2).
  Proof.
    intros. revert d2.
    induction d1,d2; simpl; try easy. rewrite IHd1. rewrite map2_map_hom. easy.
    easy.
  Qed.

  Context {HAMonoid : AMonoid Aadd Azero}.
  
  (** dl1 . dl2 = dl2 . dl1 *)
  Lemma dmap2_comm : forall (dl1 dl2 : dlist tA),
      dmap2 Aadd dl1 dl2 = dmap2 Aadd dl2 dl1.
  Proof.
    induction dl1,dl2; simpl; auto. f_equal; auto. apply map2_comm.
  Qed.
  
End dmap2_sametype.


(* ===================================================================== *)
(** ** Square Zero dlist *)
Section sdlzero.
  Context {tA : Type} (Azero : tA).

  (** Square dlist with element zero *)
  Definition sdlzero n := repeat (repeat Azero n) n.
  
  (** dim(sdl0) = rows(dl0) = cols(dl0) -> sdl0 = dl0 *)
  Lemma sdlzero_eq_dlzero_r : forall r c,
      r = c -> sdlzero r = dlzero Azero r c.
  Proof.
    intros. subst. unfold sdlzero, dlzero. easy.
  Qed.
  
  (** dim(sdl0) = rows(dl0) = cols(dl0) -> sdl0 = dl0 *)
  Lemma sdlzero_eq_dlzero_c : forall r c,
      r = c -> sdlzero c = dlzero Azero r c.
  Proof.
    intros. subst. unfold sdlzero, dlzero. easy.
  Qed.
  
  (** length(sdl0) = dim(sdl0) *)
  Lemma sdlzero_length : forall n, length (sdlzero n) = n.
  Proof.
    intros. apply repeat_length.
  Qed.
  
  (** width(sdl0) = dim(sdl0) *)
  Lemma sdlzero_width : forall n, width (sdlzero n) n.
  Proof.
    intros. unfold sdlzero. induction n. simpl. constructor.
    apply repeat_width. apply repeat_length.
  Qed.
  
End sdlzero.


(* ===================================================================== *)
(** ** dmap2 is considered as dladd *)
Section dladd.

  Context `{AG:AGroup}.
  Infix "+" := Aadd.
  
  (** dl + 0 = dl *)
  Lemma dladd_zero_l : forall dl r c, 
      length dl = r -> width dl c ->
      dmap2 Aadd (dlzero Azero r c) dl = dl.
  Proof.
    unfold width, dlzero in *.
    induction dl; simpl; intros.
    - unfold dmap2. apply map2_nil_r.
    - destruct r. easy. inv H. inv H0.
      simpl. f_equal; auto.
      rewrite map2_zero_l. auto.
  Qed.
  
  (** 0 + dl = dl *)
  Lemma dladd_zero_r : forall dl r c, 
      length dl = r -> width dl c ->
      dmap2 Aadd dl (dlzero Azero r c) = dl.
  Proof.
    intros. rewrite dmap2_comm; auto. apply dladd_zero_l; auto.
  Qed.

End dladd.


(* ===================================================================== *)
(** ** dmap2 is considered as dlsub *)
Section dlsub.

  Context `{AG:AGroup}.
  Infix "+" := Aadd.
  Notation "- a" := (Aopp a).
  Infix "-" := (fun a b => a + (-b)).
  
  (** dl1 - dl2 = - (dl2 - dl1) *)
  Lemma dlsub_comm : forall dl1 dl2 c,
      let Asub := fun a b => a + (-b) in
      length dl1 = length dl2 ->
      width dl1 c -> width dl2 c ->
      dmap2 Asub dl1 dl2 = dmap Aopp (dmap2 Asub dl2 dl1).
  Proof.
    induction dl1,dl2; simpl; intros; auto. f_equal.
    - rewrite map2_sub_comm. auto.
    - inv H. inv H0. inv H1.
      apply IHdl1 with (c:=length a); auto.
  Qed.
  
  (** (dl1 - dl2) - dl3 = dl1 - (dl2 + dl3) *)
  Lemma dlsub_assoc : forall dl1 dl2 dl3 c, 
      let Asub := fun a b => a + (-b) in
      length dl1 = length dl2 -> length dl2 = length dl3 ->
      width dl1 c -> width dl2 c ->
      dmap2 Asub (dmap2 Asub dl1 dl2) dl3 =
        dmap2 Asub dl1 (dmap2 Aadd dl2 dl3).
  Proof.
    induction dl1,dl2,dl3; simpl; intros; auto. f_equal.
    - apply map2_sub_assoc.
    - inv H. inv H0. unfold width in *. inv H1. inv H2.
      apply IHdl1 with (c:=length a); auto.
  Qed.
  
  (** 0 - dl = - dl *)
  Lemma dlsub_zero_l : forall dl r c, 
      let Asub := fun a b => a + (-b) in
      length dl = r -> width dl c ->
      dmap2 Asub (dlzero Azero r c) dl =
        dmap Aopp dl.
  Proof.
    induction dl; simpl; intros.
    - unfold dmap2. apply map2_nil_r.
    - induction r. easy. inv H. inv H0. simpl.
      unfold dlzero in *. f_equal; auto.
      apply lsub_zero_l; auto.
  Qed.
  
  (** dl - 0 = dl *)
  Lemma dlsub_zero_r : forall dl r c, 
      let Asub := fun a b => a + (-b) in
      length dl = r -> width dl c ->
      dmap2 Asub dl (dlzero Azero r c) = dl.
  Proof.
    induction dl; simpl; intros; auto. destruct r; simpl. easy.
    inv H. inv H0. f_equal; auto.
    - apply lsub_zero_r; auto.
    - apply IHdl; auto. 
  Qed.
  
  (** dl - dl = 0 *)
  Lemma dlsub_self : forall dl r c, 
      let Asub := fun a b => a + (-b) in
      length dl = r -> width dl c ->
      dmap2 Asub dl dl = (dlzero Azero r c).
  Proof.
    induction dl; simpl; intros; subst; try easy. inv H0.
    rewrite (IHdl (length dl) (length a)); auto.
    unfold dlzero in *. simpl. f_equal; try easy.
    apply map2_sub_self; auto.
  Qed.

End dlsub.


(* ===================================================================== *)
(** ** list dot dlist, and dlist dot dlist *)
Section ldotdl_dldotdl.
  Context `{HARing : ARing}.
  Add Ring ring_inst : (make_ring_theory HARing).
  Infix "+" := Aadd.
  Infix "*" := Amul.
  Notation "- b" := (Aopp b).
  Notation Asub := (fun a b => a + (-b)).
  Infix "-" := Asub.
  
  (* a convenient notation in this section *)
  Notation ldot := (ldot (Aadd:=Aadd) (Azero:=Azero) (Amul:=Amul)).
  
  (** list dot product to dlist *)
  Fixpoint ldotdl (l : list tA) (dl : dlist tA) : list tA :=
    match dl with
    | h :: t => (ldot l h) :: (ldotdl l t)
    | [] => []
    end.
  
  (** ldotdl left with nil *)
  Lemma ldotdl_nil_l : forall dl r,
      length dl = r -> (ldotdl [] dl = lzero Azero r).
  Proof.
    induction dl; simpl; intros; subst; try easy.
    rewrite ldot_nil_l. rewrite IHdl with (r:=length dl); simpl; auto.
  Qed.
  
  (** ldotdl right with nil *)
  Lemma ldotdl_nil_r : forall r l, (ldotdl l (dnil r) = lzero Azero r).
  Proof.
    induction r; simpl; intros; auto. rewrite IHr. rewrite ldot_nil_r. easy.
  Qed.

  (** ldotdl length law *)
  Lemma ldotdl_length : forall dl l r,
      length dl = r ->
      length (ldotdl l dl) = r.
  Proof.
    induction dl; intros; simpl in *; auto.
    destruct r. easy. rewrite IHdl with (r:=r); auto.
  Qed.
  
  (** ldotdl left distributve over map *)
  Lemma ldotdl_map_distr_l :
    forall l dl {c} (f : tA -> tA)
      (f_zero : f Azero = Azero)
      (f_add : forall a b, f (a + b) = f a + f b)
      (f_mul_l : forall a b, f a * b = f (a * b)),
      length l = c -> width dl c -> 
      ldotdl (map f l) dl = map f (ldotdl l dl).
  Proof.
    induction dl; simpl; intros; auto. inv H. inv H0. f_equal.
    - rewrite ldot_map_distr_l with (r:=length l); auto.
    - apply IHdl with (c:=length l); auto.
  Qed.
  
  (** ldotdl right distributve over map *)
  Lemma ldotdl_dmap_distr_r :
    forall l dl {c} (f : tA -> tA)
      (f_zero : f Azero = Azero)
      (f_add : forall a b, f (a + b) = f a + f b)
      (f_mul_r : forall a b, a * f b = f (a * b)),
      length l = c -> width dl c -> 
      ldotdl l (dmap f dl) = map f (ldotdl l dl).
  Proof.
    induction dl; simpl; intros; auto. inv H0. f_equal.
    - rewrite ldot_map_distr_r with (r:=length l); auto.
    - apply IHdl with (c:=length l); auto.
  Qed.
  
  (** ldotdl left distributve over map2 *)
  Lemma ldotdl_dmap2_distr_l : forall l dl1 dl2 {c},
      length l = c ->
      width dl1 c -> width dl2 c ->
      (ldotdl l (dmap2 Aadd dl1 dl2) = 
         map2 Aadd (ldotdl l dl1) (ldotdl l dl2)).
  Proof.
    induction dl1,dl2; simpl; intros; auto. inv H0. inv H1.
    f_equal.
    - apply ldot_map2_distr_l with (r:=length a); auto. lia.
    - apply IHdl1 with (c:=length l); auto.
  Qed.

  (** ldotdl right distributve over dmap2 *)
  Lemma ldotdl_map2_distr_r : forall dl l1 l2 {c},
      length l1 = length l2 ->
      length dl = c -> width dl (length l1) ->
      (ldotdl (map2 Aadd l1 l2) dl = 
         map2 Aadd (ldotdl l1 dl) (ldotdl l2 dl)).
  Proof.
    induction dl; intros; simpl; auto. inv H1. f_equal.
    - apply ldot_map2_distr_r with (r:=length l1); auto.
    - apply IHdl with (c:=length dl); auto.
  Qed.
  
  (** ldotdl left with zero *)
  Lemma ldotdl_zero_l : forall dl r c,
      length dl = r -> width dl c ->
      (ldotdl (lzero Azero c) dl = lzero Azero r).
  Proof.
    induction dl; simpl; intros; auto.
    - subst; easy.
    - inv H0. rewrite IHdl with (r:=length dl); auto.
      rewrite ldot_zero_l; easy.
  Qed.
  
  (** ldotdl right with zero *)
  Lemma ldotdl_zero_r : forall l r c,
      length l = c ->
      (ldotdl l (dlzero Azero r c) = lzero Azero r).
  Proof.
    induction r; simpl; intros; auto. unfold dlzero in *. rewrite IHr; auto.
    rewrite ldot_zero_r. easy.
  Qed.
  
  (** ldotdl of consr and consc *)
  Lemma ldotdl_consr_consc : forall l2 dl2 l1 x1 r c,
      length l2 = c -> length dl2 = c -> width dl2 r ->
      (ldotdl (x1 :: l1) (consc l2 dl2) =
         ladd (Aadd:=Aadd) (lcmul (Amul:=Amul) x1 l2) (ldotdl l1 dl2)).
  Proof.
    induction l2, dl2; simpl; intros; auto. inv H1.
    rewrite ldot_cons. f_equal.
    eapply IHl2; auto. apply H5.
  Qed.

  (** ldot and ldotdl could swap first two operands.
    l1 . (l2 . dl) = l2 . (l1 . dl^T) *)
  Lemma ldot_ldotdl_swap12 : forall dl l1 l2 r c,
      length l1 = r -> length l2 = c -> length dl = r -> width dl c ->
      (ldot l1 (ldotdl l2 dl) =
         ldot l2 (ldotdl l1 (dltrans dl c))).
  Proof.
    induction dl,l1; simpl; intros; auto.
    - rewrite ldotdl_nil_l with (r:=c); try apply dnil_length.
      rewrite ldot_zero_r; cbv. easy.
    - subst. inversion H1.
    - subst. inversion H1.
    - inv H2. rewrite ldot_cons.
      rewrite ldotdl_consr_consc with (r:=length l1) (c:=length a); auto.
      + rewrite ldot_ladd_distr_l with (r:=length l2);
          auto using lcmul_length, ldotdl_length, dltrans_length.
        rewrite <- IHdl with (r:=length l1); auto.
        rewrite ldot_lcmul_distr_r. easy.
      + rewrite dltrans_length; auto.
      + apply dltrans_width; auto.
  Qed.

  (** ldotdl with consr at right operend *)
  Lemma ldotdl_consr_r : forall l1 l2 dl2 r c,
      length l1 = r -> length l2 = r -> length dl2 = c -> width dl2 r ->
      (ldotdl l1 (l2 :: dl2) = (ldot l1 l2) :: (ldotdl l1 dl2)).
  Proof.
    induction l1,l2,dl2; simpl; intros; easy.
  Qed.
  
  (** ldotdl right distributive over ladd.
    (l1 + l2) . dl = l1 . dl + l2.dl *)
  Lemma ldotdl_ladd_distr_r : forall l1 l2 dl r c,
      length l1 = r -> length l2 = r -> length dl = c -> width dl r ->
      (ldotdl (ladd (Aadd:=Aadd) l1 l2) dl = 
         ladd (Aadd:=Aadd) (ldotdl l1 dl) (ldotdl l2 dl)).
  Proof.
    induction dl; simpl; intros; auto. inv H2.
    rewrite <- IHdl with (r:=length l1) (c:=length dl); auto.
    rewrite ldot_ladd_distr_r with (r:=length l1); easy.
  Qed.
  
  (** ldotdl with lcmul is assocociative.
    cmul a (dot l dl) = dot (cmul a l) dl *)
  Lemma ldotdl_lcmul_assoc : forall dl a l r c,
      length l = r -> length dl = c -> width dl r ->
      (lcmul (Amul:=Amul) a (ldotdl l dl) = ldotdl (lcmul (Amul:=Amul) a l) dl).
  Proof.
    induction dl; simpl; intros; auto. inv H1.
    rewrite IHdl with (r:=length l) (c:=length dl); auto.
    rewrite ldot_lcmul_distr_l. easy.
  Qed.
  
  (** a * (x :: l) = (a * x) :: (a * l) *)
  Lemma lcmul_cons : forall a x l,
      (lcmul (Amul:=Amul) a (x :: l) = (Amul a x) :: (lcmul (Amul:=Amul) a l)).
  Proof.
    intros. easy.
  Qed.
  
  (** a * 0 = 0 *)
  Lemma lcmul_zero_r : forall a n,
      lcmul (Amul:=Amul) a (lzero Azero n) = lzero Azero n.
  Proof.
    intros. unfold lcmul. rewrite map_repeat. unfold lzero. f_equal. ring.
  Qed.
  
  (** l dotdl E = l *)
  Lemma ldotdl_dlunit : forall l {n},
      length l = n -> (ldotdl l (dlunit Azero Aone n) = l).
  Proof.
    induction l; simpl; intros; auto.
    - subst. simpl. easy.
    - destruct n. easy. inv H. simpl. f_equal.
      + rewrite ldot_cons. rewrite ldot_zero_r. ring.
      + erewrite (ldotdl_consr_consc);
          try apply repeat_length; try apply dlunit_length; try apply dlunit_width.
        rewrite IHl; try easy.
        rewrite lcmul_zero_r. rewrite ladd_zero_l; easy.
  Qed.
  
  (** dlist dot product *)
  Fixpoint dldotdl (dl1 dl2 : dlist tA) : dlist tA :=
    match dl1 with
    | h1 :: t1 => (ldotdl h1 dl2) :: (dldotdl t1 dl2)
    | [] => []
    end.
  
  (** dldotdl length law *)
  Lemma dldotdl_length : forall dl1 dl2 r1,
      length dl1 = r1 ->
      length (dldotdl dl1 dl2) = r1.
  Proof.
    induction dl1; intros; auto. simpl in *. destruct r1. easy.
    rewrite IHdl1 with (r1:=r1); auto.
  Qed.

  (** dldotdl width law *)
  Lemma dldotdl_width : forall dl1 dl2 r2 c,
      length dl2 = r2 -> width dl1 c -> width dl2 c ->
      width (dldotdl dl1 dl2) r2.
  Proof.
    unfold width; induction dl1; intros; simpl in *; auto. inv H0. constructor.
    - apply ldotdl_length; auto.
    - apply IHdl1 with (c:=length a); auto.
  Qed.

  (** dldotdl consr left *)
  Lemma dldotdl_consr_l : forall l1 dl1 dl2,
      dldotdl (l1 :: dl1) dl2 = (ldotdl l1 dl2) :: (dldotdl dl1 dl2). 
  Proof.
    simpl. easy.
  Qed.
  
  (** dldotdl consr right *)
  Lemma dldotdl_consr_r : forall dl1 l2 dl2 c,
      length l2 = c ->
      width dl1 c ->
      width dl2 c ->
      dldotdl dl1 (l2 :: dl2) = consc (ldotdl l2 dl1) (dldotdl dl1 dl2).
  Proof.
    induction dl1; simpl; intros; auto. inv H0.
    rewrite ldot_comm.
    rewrite IHdl1 with (c:=length l2); auto.
  Qed.

  (** dldotdl left distributve over dmap *)
  Lemma dldotdl_dmap_distr_l :
    forall dl1 dl2 {c} (f : tA -> tA)
      (f_zero : f Azero = Azero)
      (f_add : forall a b, f (a + b) = f a + f b)
      (f_mul_l : forall a b, f a * b = f (a * b)),
      width dl1 c -> width dl2 c ->
      dldotdl (dmap f dl1) dl2 = dmap f (dldotdl dl1 dl2).
  Proof.
    induction dl1; simpl; intros; auto. inv H. f_equal.
    - apply ldotdl_map_distr_l with (c:=length a); auto.
    - apply IHdl1 with (c:=length a); auto.
  Qed.

  (** dldotdl right distributve over dmap *)
  Lemma dldotdl_dmap_distr_r :
    forall dl1 dl2 {c} (f : tA -> tA)
      (f_zero : f Azero = Azero)
      (f_add : forall a b, f (a + b) = f a + f b)
      (f_mul_r : forall a b, a * f b = f (a * b)),
      width dl1 c -> width dl2 c ->
      dldotdl dl1 (dmap f dl2) = dmap f (dldotdl dl1 dl2).
  Proof.
    induction dl1; simpl; intros; auto. inv H. f_equal.
    - apply ldotdl_dmap_distr_r with (c:=length a); auto.
    - apply IHdl1 with (c:=length a); auto.
  Qed.
  
  (** dldotdl left distributve over dmap2 *)
  Lemma dldotdl_dmap2_distr_l : forall dl1 dl2 dl3 {c},
      width dl1 c -> width dl2 c -> width dl3 c -> 
      dldotdl dl1 (dmap2 Aadd dl2 dl3) =
        dmap2 Aadd (dldotdl dl1 dl2) (dldotdl dl1 dl3).
  Proof.
    induction dl1; simpl; intros; auto. inv H. f_equal.
    - apply ldotdl_dmap2_distr_l with (c:=length a); auto.
    - apply IHdl1 with (c:=length a); auto.
  Qed.
  
  (** dldotdl right distributve over dmap2 *)
  Lemma dldotdl_dmap2_distr_r : forall dl1 dl2 dl3 {c},
      width dl1 c -> width dl2 c -> width dl3 c -> 
      dldotdl (dmap2 Aadd dl1 dl2) dl3 = 
        dmap2 Aadd (dldotdl dl1 dl3) (dldotdl dl2 dl3).
  Proof.
    induction dl1; destruct dl2; intros; simpl in *; try easy.
    inv H. inv H0. f_equal.
    - apply ldotdl_map2_distr_r with (c:=length dl3); auto.
    - apply IHdl1 with (c:=length a); auto. 
  Qed.

  (** dldotdl [] dl = [] *)
  Lemma dldotdl_nil_l : forall dl, dldotdl [] dl = [].
  Proof. intros. simpl. auto. Qed.
  
  (** dldotdl dl [] = dnil *)
  Lemma dldotdl_nil_r : forall dl, dldotdl dl [] = dnil (length dl).
  Proof.
    induction dl; simpl; intros; subst; simpl; subst; try easy.
    f_equal; auto.
  Qed.

  Section test.
    Variable a11 a12 a21 a22 : tA.
    Let d1 := [[a11;a12]].
    Let d2 := [[a11;a12];[a21;a22]].
    (* Compute dldotdl (dnil 2) d1. *)
    (* Compute dldotdl (dnil 2) d2. *)
    (* Compute dldotdl (dnil 3) d2. *)
    (* Compute dldotdl d1 (dnil 2). *)
    (* Compute dldotdl d2 (dnil 2). *)
    (* Compute dldotdl d2 (dnil 3). *)
    (* Compute ldotdl [] d2.  *)
  End test.

  (** dldotdl dnil dl = dlzero *)
  Lemma dldotdl_dnil_l : forall dl n r c,
      length dl = r -> width dl c ->
      dldotdl (dnil n) dl = dlzero Azero n r.
  Proof.
    intros dl n. revert dl. induction n; intros; simpl.
    - unfold dlzero. simpl. auto.
    - rewrite dlzero_Sr. f_equal.
      + rewrite ldotdl_nil_l with (r:=r); auto.
      + apply IHn with (c:=c); auto.
  Qed.
  
  (** dldotdl dl dnil = dnil *)
  Lemma dldotdl_dnil_r : forall dl n r c,
      length dl = r -> width dl c ->
      dldotdl dl (dnil n) = dlzero Azero r n.
  Proof.
    intros dl n r. revert dl n. induction r; intros; simpl.
    - apply length_zero_iff_nil in H. subst. reflexivity.
    - destruct dl; simpl in *. lia. inversion H. inversion H0.
      rewrite IHr with (c:=c); auto. rewrite H2.
      rewrite dlzero_Sr. f_equal. rewrite ldotdl_nil_r. auto.
  Qed.

  (** dldotdl zero dl = zero *)
  Lemma dldotdl_zero_l : forall r dl c,
      width dl c ->
      dldotdl (dlzero Azero r c) dl = dlzero Azero r (length dl).
  Proof.
    induction r; simpl; intros; simpl; unfold dlzero in *; simpl; try easy.
    rewrite (IHr _ c); auto.
    erewrite (ldotdl_zero_l _); auto.
  Qed.
  
  (** dldotdl dl zero = zero *)
  Lemma dldotdl_zero_r : forall dl c t,
      width dl c ->
      dldotdl dl (dlzero Azero t c) = dlzero Azero (length dl) t.
  Proof.
    induction dl; simpl; intros; auto. inv H.
    unfold dlzero; simpl. f_equal.
    - rewrite dlzero_rw. rewrite ldotdl_zero_r; auto.
    - apply IHdl. auto.
  Qed.
  
  (** dltrans for dldotdl with right decomposition *)
  Lemma dltrans_dldotdl_right : forall d1 d2 l2 r,
      dltrans (dldotdl d1 (l2 :: d2)) (S r) =
        (ldotdl l2 d1) :: (dltrans (dldotdl d1 d2) r).
  Proof.
    unfold width; induction d1; intros; simpl in *. easy.
    specialize (IHd1 d2 l2 r).
    destruct (dltrans (dldotdl d1 (l2 :: d2)) (S r)); try easy. inv IHd1.
    f_equal. f_equal; auto. apply ldot_comm.
  Qed.
  
  (** dldotdl commutation *)
  Lemma dldotdl_comm : forall d1 d2 r c,
      length d1 = r -> width d1 c -> width d2 c ->
      dldotdl d1 d2 = dltrans (dldotdl d2 d1) r.
  Proof.
    induction d1; simpl; intros; subst.
    - rewrite dldotdl_nil_r. rewrite dltrans_nil. easy.
    - inv H0. rewrite dltrans_dldotdl_right.
      f_equal; try easy. apply IHd1 with (c:=length a); auto.
  Qed.
  
  (** l * (d1 . d2)^T = (l . d1^T) . d2 *)
  Lemma ldotdl_dldotdl_dltrans_assoc : forall d1 d2 l {r c},
      width d1 c ->
      length d2 = r -> width d2 c ->
      (ldotdl l (dltrans (dldotdl d1 d2) r) =
         ldotdl (ldotdl l (dltrans d1 c)) d2).
  Proof.
    unfold width. induction d1; intros.
    - subst. simpl. rewrite ?ldotdl_nil_r.
      rewrite ldotdl_zero_l with (r:=length d2); auto.
    - inv H. simpl. destruct l.
      + rewrite ldotdl_nil_l with (r:=length d2).
        2:{ apply consc_length.
            apply ldotdl_length; auto.
            apply dltrans_length. apply dldotdl_width with (c:=length a); auto. }
        rewrite ldotdl_nil_l with (r:=length a).
        2:{ apply consc_length; auto.
            apply dltrans_length; auto. }
        rewrite ldotdl_zero_l with (r:=length d2); auto.
      + erewrite ldotdl_consr_consc with (r:=length d1);
          auto using dltrans_length, dltrans_width.
        2:{ rewrite dltrans_length.
            rewrite ldotdl_length with (r:=length d2); auto.
            apply dldotdl_width with (c:=length a); auto. }
        2:{ apply dltrans_width. apply dldotdl_length; auto.
            apply dldotdl_width with (c:=length a); auto. }
        rewrite ldotdl_consr_consc with (r:=length d1) (c:=length a);
          auto using dltrans_length, dltrans_width.
        erewrite ldotdl_lcmul_assoc with (r:=length a); auto.
        rewrite ldotdl_ladd_distr_r with (r:=length a) (c:=length d2);
          auto using lcmul_length, ldotdl_length, dltrans_length.
        rewrite IHd1 with (c:=length a); auto.
  Qed.

  (** dldotdl association *)
  Lemma dldotdl_assoc : forall d1 d2 d3 r c,
      width d2 c ->
      length d3 = r -> width d3 c ->
      dldotdl (dldotdl d1 (dltrans d2 c)) d3 =
        dldotdl d1 (dltrans (dldotdl d2 d3) r).
  Proof.
    induction d1; simpl; intros; auto.
    f_equal.
    - rewrite ldotdl_dldotdl_dltrans_assoc with (c:=c); auto.
    - apply IHd1; auto.
  Qed.
  
  (** dldotdl left with dlunit *)
  Lemma dldotdl_dlunit_l : forall (dl : dlist tA) {c},
      width dl c -> 
      dldotdl (dlunit Azero Aone c) dl = dltrans dl c.
  Proof.
    induction dl; simpl; intros; try easy.
    - rewrite dldotdl_nil_r. rewrite dlunit_length. easy.
    - inversion H.
      rewrite dldotdl_consr_r with (c:=c); auto using dlunit_width.
      rewrite IHdl; auto.
      rewrite ldotdl_dlunit; easy.
  Qed.
  
  (** dldotdl right with dlunit *)
  Lemma dldotdl_dlunit_r : forall (dl : dlist tA) {c},
      width dl c -> 
      dldotdl dl (dlunit Azero Aone c) = dl.
  Proof.
    induction dl; simpl; intros; auto. inversion H.
    rewrite IHdl; auto. rewrite ldotdl_dlunit; easy.
  Qed.
  
End ldotdl_dldotdl.


(* ===================================================================== *)
(** ** Properties of dlcmul *)
Section dlcmul_properties.
  Context `{F:Field}.
  Context {AeqDec: Dec (@eq tA)}.
  
  (** Mapping cmul to dlist keep unchanged imply k = 1 or dlist is zero *)
  Lemma dlcmul_fixpoint_imply_k1_or_dlzero : 
    forall {r c} k (dl : dlist tA) (H1 : length dl = r) (H2 : width dl c),
      map (map (fun x => Amul k x)) dl = dl ->
      ((k = Aone) \/ dl = dlzero Azero r c).
  Proof.
    unfold width,dlzero; induction r; intros.
    - rewrite length_zero_iff_nil in H1. subst. right. cbv. easy.
    - simpl. destruct dl. easy. simpl in *. inv H.
      pose proof (lcmul_fixpoint_imply_k1_or_lzero l eq_refl k H3).
      inversion H1. inversion H2.
      specialize (IHr c k dl H5 H8 H4). clear H1 H2.
      destruct IHr, H; auto. right.
      rewrite H3,H4. rewrite H7 in *. rewrite <- H. f_equal.
      rewrite H, H5. auto.
  Qed.
  
  (** Mapping mulc to dlist keep unchanged imply k = 1 or dlist is zero *)
  Lemma dlmulc_fixpoint_imply_k1_or_dlzero : 
    forall {r c} k (dl : dlist tA) (H1 : length dl = r) (H2 : width dl c),
      map (map (fun x => Amul x k)) dl = dl ->
      ((k = Aone) \/ dl = dlzero Azero r c).
  Proof.
    intros. apply dlcmul_fixpoint_imply_k1_or_dlzero; auto.
    rewrite <- H at 2.
    apply map_ext. intros.
    apply map_ext. intros. apply commutative. 
  Qed.

  (** Mapping cmul to dlist got zero imply k = 0 or dlist is zero *)
  Lemma dlcmul_zero_imply_k0_or_dlzero : 
    forall {r c} k (dl : dlist tA) (H1 : length dl = r) (H2 : width dl c),
      map (map (fun x => Amul k x)) dl = (dlzero Azero r c) ->
      ((k = Azero) \/ dl = dlzero Azero r c).
  Proof.
    unfold width, dlzero; induction r; intros.
    - rewrite length_zero_iff_nil in H1. subst. cbv. right. easy.
    - destruct dl. easy. simpl in *.
      inversion H1. inversion H2. inversion H. clear H1 H2 H.
      specialize (IHr c k dl H3 H6).
      rewrite H3, <- H9, H8. subst.
      assert (map (map (fun x : tA => Amul k x)) dl =
                repeat (lzero Azero (length l)) (length dl)).
      { rewrite H9. rewrite H8. auto. }
      apply IHr in H.
      (*  {k = 0} + {k <> 0} *)
      destruct (Aeqdec k Azero); auto.
      destruct H; auto. right. f_equal.
      + apply lcmul_eq0_imply_k0_or_lzero in H8; auto.
        destruct H8; auto. easy.
      + rewrite H9. rewrite H at 1. f_equal. rewrite H8. auto.
  Qed.
  
End dlcmul_properties.




(* ===================================================================== *)
(** ** Set element with a constant value *)
Section SetByConstant.
  
  (* --------------------------------------------------------------------- *)
  (** *** Modify a dlist *)
  
  (** dl[i,j] = x *)
  Fixpoint dlset {tA} (dl : dlist tA) (i j : nat) (x : tA) 
    : dlist tA :=
    match dl, i with
    | [], _ => []
    | l :: dl, 0 => (lset l j x) :: dl
    | l :: dl, S i' => l :: (dlset dl i' j x)
    end. 
  
  (* Compute dlset [] 0 1 9. *)
  (* Compute dlset [[1;2];[3;4;5]] 0 1 9. *)
  (* Compute dlset [[1;2];[3;4;5]] 1 1 9. *)
  (* Compute dlset [[1;2];[3;4;5]] 2 1 9. *)
  (* Compute dlset [[1;2];[3;4;5]] 1 5 9. *)
  
  (** Length property *)
  Lemma dlset_length : forall {tA} dl i r j x, 
      length dl = r ->
      length (@dlset tA dl i j x) = r.
  Proof.
    intros tA dl; induction dl; auto. destruct i; intros; auto; simpl in *.
    destruct r; auto. easy.
  Qed.
  
  (** Width property *)
  Lemma dlset_width : forall {tA} dl i c j x, 
      width dl c ->
      width (@dlset tA dl i j x) c.
  Proof.
    unfold width. intros tA dl; induction dl; auto.
    destruct i; intros; simpl in *; auto; inv H; constructor; auto.
    apply lset_length; auto.
  Qed.

End SetByConstant.


(* ===================================================================== *)
(** ** Set element with a generation function *)
Section SetByFunction.

  (** Inner version, i0 is given position, i is changed in every loop *)
  Fixpoint dlsetf_aux {tA} (dl : dlist tA) (i0 i j : nat) 
    (f : nat -> nat -> tA) 
    : dlist tA :=
    match dl, i with
    | [], _ => []
    | l :: dl, 0 => (lsetf l j (f i0)) :: dl
    | l :: dl, S i' => l :: (dlsetf_aux dl i0 i' j f)
    end. 
  
  (** User version that hide i0 parameter *)
  Definition dlsetf {tA} (dl : dlist tA) (i j : nat) 
    (f : nat -> nat -> tA) 
    : dlist tA :=
    dlsetf_aux dl i i j f.
  
  (* Let f_gen := fun (i j : nat) => (i + j + 10).
  Compute dlsetf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 0 f_gen.
  Compute dlsetf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 1 f_gen.
  Compute dlsetf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 2 f_gen.
  Compute dlsetf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 3 f_gen.
  Compute dlsetf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 4 f_gen.
  Compute dlsetf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 0 f_gen.
  Compute dlsetf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 1 f_gen.
  Compute dlsetf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 2 f_gen.
  Compute dlsetf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 3 f_gen.
  Compute dlsetf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 4 f_gen.
   *)
  
  (** Length property *)
  Lemma dlsetf_aux_length : forall {tA} dl i r i0 j f, 
      length dl = r ->
      length (@dlsetf_aux tA dl i0 i j f) = r.
  Proof.
    intros tA dl; induction dl; auto. destruct i; auto; simpl; intros.
    destruct r; auto. easy.
  Qed.
  
  Lemma dlsetf_length : forall {tA} dl r i j f, 
      length dl = r ->
      length (@dlsetf tA dl i j f) = r.
  Proof.
    intros. apply dlsetf_aux_length. auto.
  Qed.
  
  (** Width property *)
  Lemma dlsetf_aux_width : forall {tA} dl i c i0 j f, 
      width dl c ->
      width (@dlsetf_aux tA dl i0 i j f) c.
  Proof.
    unfold width. intros tA dl; induction dl; auto. 
    induction i; intros; simpl in *; auto; inv H; constructor; auto.
    apply lsetf_length; auto.
  Qed.
  
  Lemma dlsetf_width : forall {tA} dl i c j f, 
      width dl c ->
      width (@dlsetf tA dl i j f) c.
  Proof.
    intros. apply dlsetf_aux_width; auto.
  Qed.

End SetByFunction.


(* ===================================================================== *)
(** ** Set row with a constant value *)
Section SetRowByConstant.
  
  (** Definition *)
  Fixpoint dlsetRow {tA} (dl : dlist tA) (i : nat) (x : list tA) 
    : dlist tA :=
    match dl, i with
    | [], _ => []
    | l :: dl, 0 => x :: dl
    | l :: dl, S i' => l :: (dlsetRow dl i' x)
    end. 
  
  (*   Compute dlsetRow [] 0 [8;9].
  Compute dlsetRow [[1;2];[3;4;5]] 0 [8;9].
  Compute dlsetRow [[1;2];[3;4;5]] 1 [8;9].
  Compute dlsetRow [[1;2];[3;4;5]] 2 [8;9].
   *)  
  (** Length property *)
  Lemma dlsetRow_length : forall {tA} dl i r x, 
      length dl = r ->
      length (@dlsetRow tA dl i x) = r.
  Proof.
    intros tA dl; induction dl; auto. destruct i; auto; intros; simpl in *.
    destruct r; auto. easy.
  Qed.
  
  (** Width property *)
  Lemma dlsetRow_width : forall {tA} dl i c x,
      length x = c ->
      width dl c ->
      width (@dlsetRow tA dl i x) c.
  Proof.
    unfold width; intros tA dl; induction dl; auto. 
    induction i; intros; simpl in *; inv H0; constructor; auto.
  Qed.

  (** Index out-of-bound *)
  Lemma dlsetRow_idxOutOfBound : forall {tA} dl i r c l,
      length dl = r -> width dl c -> i >= r -> @dlsetRow tA dl i l = dl.
  Proof.
    intros tA dl i. revert dl. induction i; intros; simpl.
    - assert (r = 0). lia. rewrite H2 in *. apply length_zero_iff_nil in H.
      rewrite H in *. simpl. auto.
    - destruct dl; auto. simpl in *. destruct r; try lia.
      f_equal.
      apply IHi with r c; auto. inv H0; auto. lia.
  Qed.

End SetRowByConstant.


(* ===================================================================== *)
(** ** Set row with a generation function *)
Section SetRowByFunction.
  
  (** Inner version, i0 is given position, i is changed in every loop *)
  Fixpoint dlsetRowf_aux {tA} (dl : dlist tA) (i0 i : nat) 
    (f : nat -> list tA) 
    : dlist tA :=
    match dl, i with
    | [], _ => []
    | l :: dl, 0 => (f i0) :: dl
    | l :: dl, S i' => l :: (dlsetRowf_aux dl i0 i' f)
    end. 
  
  (** User version that hide i0 parameter *)
  Definition dlsetRowf {tA} (dl : dlist tA) (i : nat) 
    (f : nat -> list tA) 
    : dlist tA :=
    dlsetRowf_aux dl i i f.
  
  (*   Let f_gen := fun (i : nat) => [i+10;i+11;i+12].
  Compute dlsetRowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 f_gen.
  Compute dlsetRowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 f_gen.
  Compute dlsetRowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 2 f_gen.
  Compute dlsetRowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 3 f_gen.
   *) 
  
  (** Length property *)
  Lemma dlsetRowf_aux_length : forall {tA} dl i r i0 f, 
      length dl = r ->
      length (@dlsetRowf_aux tA dl i0 i f) = r.
  Proof.
    intros tA dl; induction dl; auto. induction i; auto.
    intros. simpl. destruct r; auto. easy.
  Qed.
  
  Lemma dlsetRowf_length : forall {tA} dl r i f, 
      length dl = r ->
      length (@dlsetRowf tA dl i f) = r.
  Proof.
    intros. apply dlsetRowf_aux_length. auto.
  Qed.
  
  (** Width property *)
  Lemma dlsetRowf_aux_width : forall {tA} dl i c i0 f, 
      length (f i0) = c ->
      width dl c ->
      width (@dlsetRowf_aux tA dl i0 i f) c.
  Proof.
    unfold width; intros tA dl; induction dl; auto. 
    induction i; intros; simpl in *; auto; inv H0; constructor; auto.
  Qed.
  
  Lemma dlsetRowf_width : forall {tA} dl i c f, 
      length (f i) = c ->
      width dl c ->
      width (@dlsetRowf tA dl i f) c.
  Proof.
    intros. apply dlsetRowf_aux_width; auto.
  Qed.

End SetRowByFunction.


(* ===================================================================== *)
(** ** Row Transform *)
Section RowTransform.

  Context `{HARing : ARing}.
  
  (** *** Swap two rows *)

  (** Swap row i1 and row i2 *)
  Definition dlistRowSwap (dl : dlist tA) (i1 i2 : nat) : dlist tA :=
    let r := length dl in
    if (i1 <? r) && (i2 <? r)
    then 
      let row_i1 := nth i1 dl [] in
      let row_i2 := nth i2 dl [] in
      dlsetRow (dlsetRow dl i1 row_i2) i2 row_i1
    else dl.
  
  (** Index out-of-bound *)
  Lemma dlistRowSwap_idxOutOfBound_i1 : forall dl r c i1 i2,
      length dl = r -> width dl c -> i1 >= r -> dlistRowSwap dl i1 i2 = dl.
  Proof.
    intros. unfold dlistRowSwap.
    rewrite H in *. apply Nat.ltb_ge in H1. rewrite H1; simpl. auto.
  Qed.

  (** Index out-of-bound *)
  Lemma dlistRowSwap_idxOutOfBound_i2 : forall dl r c i1 i2,
      length dl = r -> width dl c -> i2 >= r -> dlistRowSwap dl i1 i2 = dl.
  Proof.
    intros. unfold dlistRowSwap.
    rewrite H in *. apply Nat.ltb_ge in H1. rewrite H1; simpl.
    rewrite andb_false_r. auto.
  Qed.

  (** Length property *)
  Lemma dlistRowSwap_length : forall dl r c i1 i2, 
      length dl = r -> width dl c -> length (dlistRowSwap dl i1 i2) = r.
  Proof.
    intros. unfold dlistRowSwap.
    rewrite H in *. destruct (i1 <? r) eqn:E1, (i2 <? r) eqn:E2; simpl; auto.
    repeat rewrite dlsetRow_length with (r:=r); auto.
  Qed.

  (** Width property *)
  Lemma dlistRowSwap_width : forall dl r c i1 i2,
      length dl = r -> width dl c -> width (dlistRowSwap dl i1 i2) c.
  Proof.
    intros. unfold dlistRowSwap.
    rewrite H in *. destruct (i1 <? r) eqn:E1, (i2 <? r) eqn:E2; simpl; auto.
    repeat apply dlsetRow_width; auto; apply dlist_nth_length; auto; try lia;
      rewrite H in *; solve_nat_ineq.
  Qed.

  
  (** *** K times of one row *)

  (** k times of row i  *)
  Definition dlistRowK (dl : dlist tA) (i : nat) (k : tA) : dlist tA :=
    let r := length dl in
    if (i <? r)
    then 
      let row_i := nth i dl [] in
      let row_i_K := lcmul (Amul:=Amul) k row_i in
      dlsetRow dl i row_i_K
    else dl.

  (** Index out-of-bound *)
  Lemma dlistRowK_idxOutOfBound : forall dl r c i k,
      length dl = r -> width dl c -> i >= r -> dlistRowK dl i k = dl.
  Proof.
    intros. unfold dlistRowK.
    rewrite H in *. apply Nat.ltb_ge in H1. rewrite H1; simpl. auto.
  Qed.

  (** Length property *)
  Lemma dlistRowK_length : forall dl r c i k,
      length dl = r -> width dl c -> length (dlistRowK dl i k) = r.
  Proof.
    intros. unfold dlistRowK.
    rewrite H in *. destruct (i <? r) eqn:Ei; simpl; auto.
    repeat rewrite dlsetRow_length with (r:=r); auto.
  Qed.

  (** Width property *)
  Lemma dlistRowK_width : forall dl r c i k,
      length dl = r -> width dl c -> width (dlistRowK dl i k) c.
  Proof.
    intros. unfold dlistRowK.
    rewrite H in *. destruct (i <? r) eqn:Ei; simpl; auto.
    repeat apply dlsetRow_width; auto.
    rewrite lcmul_length with (n:=c); auto.
    apply dlist_nth_length; auto; try lia; rewrite H in *; solve_nat_ineq.
  Qed.

  
  (** *** Add K times of one row to another row *)

  (* add k times of row i1 to row i2, that is: row(i2) = row(i2) + k * row(i1) *)
  Definition dlistRowKAdd (dl : dlist tA) (i1 i2 : nat) (k : tA) : dlist tA :=
    let r := length dl in
    if (i1 <? r) && (i2 <? r)
    then 
      let row_i1 := nth i1 dl [] in
      let row_i2 := nth i2 dl [] in
      let row_i2' := ladd (Aadd:=Aadd) (lcmul (Amul:=Amul) k row_i1) row_i2 in
      dlsetRow dl i2 row_i2'
    else dl.

  (** Index out-of-bound *)
  Lemma dlistRowKAdd_idxOutOfBound_i1 : forall dl r c i1 i2 k,
      length dl = r -> width dl c -> i1 >= r -> dlistRowKAdd dl i1 i2 k = dl.
  Proof.
    intros. unfold dlistRowKAdd.
    rewrite H in *. apply Nat.ltb_ge in H1. rewrite H1; simpl. auto.
  Qed.

  (** Index out-of-bound *)
  Lemma dlistRowKAdd_idxOutOfBound_i2 : forall dl r c i1 i2 k,
      length dl = r -> width dl c -> i2 >= r -> dlistRowKAdd dl i1 i2 k = dl.
  Proof.
    intros. unfold dlistRowKAdd.
    rewrite H in *. apply Nat.ltb_ge in H1. rewrite H1; simpl.
    rewrite andb_false_r. auto.
  Qed.

  (** Length property *)
  Lemma dlistRowKAdd_length : forall dl r c i1 i2 k,
      length dl = r -> width dl c -> length (dlistRowKAdd dl i1 i2 k) = r.
  Proof.
    intros. unfold dlistRowKAdd.
    rewrite H in *. destruct (i1 <? r) eqn:E1, (i2 <? r) eqn:E2; simpl; auto.
    repeat rewrite dlsetRow_length with (r:=r); auto.
  Qed.

  (** Width property *)
  Lemma dlistRowKAdd_width : forall dl r c i1 i2 k,
      length dl = r -> width dl c -> width (dlistRowKAdd dl i1 i2 k) c.
  Proof.
    intros. unfold dlistRowKAdd.
    rewrite H in *. destruct (i1 <? r) eqn:E1, (i2 <? r) eqn:E2; simpl; auto.
    repeat apply dlsetRow_width; auto.
    rewrite ladd_length with (n:=c); auto.
    rewrite lcmul_length with (n:=c); auto.
    apply dlist_nth_length; auto; try lia; rewrite H in *; solve_nat_ineq.
    apply dlist_nth_length; auto; try lia; rewrite H in *; solve_nat_ineq.
  Qed.
  
End RowTransform.

Section test.
  Let dlistRowK := dlistRowK (Amul:=Nat.mul).
  Let dlistRowKAdd := dlistRowKAdd (Aadd:=Nat.add) (Amul:=Nat.mul).
  Let dl := [[1;2];[3;4];[5;6]].
  (* Compute dlistRowSwap dl 0 1. *)
  (* Compute dlistRowK dl 0 2. *)
  (* Compute dlistRowKAdd dl 0 1 2. *)
End test.


(* ===================================================================== *)
(** ** dlist remove one row and/or one column *)
Section dlremove.
  Context {tA : Type} {Azero : tA}.

  Lemma firstn_width : forall (dl : dlist tA) c n, width dl c -> width (firstn n dl) c.
  Proof.
    induction dl; intros; destruct n; simpl; auto. constructor.
    inv H. constructor; auto. apply IHdl. auto.
  Qed.
    
  Lemma skipn_width : forall (dl : dlist tA) c n, width dl c -> width (skipn n dl) c.
  Proof.
    induction dl; intros; destruct n; simpl; auto. apply IHdl. inv H; auto.
  Qed.

  (** *** 取前n列 *)
  Fixpoint firstnC (n : nat) (dl : dlist tA) : dlist tA :=
    match dl with
    | [] => []
    | l :: dl' => (firstn n l) :: (firstnC n dl')
    end.

  Lemma firstnC_length : forall dl r n,
      length dl = r -> length (firstnC n dl) = r.
  Proof.
    induction dl; intros; simpl in *; auto.
    destruct r. lia. rewrite IHdl with (r:=r); auto.
  Qed.
  
  Lemma firstnC_width : forall (dl : dlist tA) c n,
      width dl c -> n < c -> width (firstnC n dl) n.
  Proof.
    induction dl; intros; simpl in *; auto. constructor. inversion H.
    constructor; auto. rewrite firstn_length. lia. apply IHdl with (c:=c); auto.
  Qed.

  Lemma firstnC_overflow : forall dl r c n,
      length dl = r -> width dl c -> n >= c -> firstnC n dl = dl.
  Proof.
    induction dl; intros; auto. simpl. destruct r; simpl in *. lia.
    inversion H. inversion H0. f_equal; auto.
    - apply firstn_all2. lia.
    - apply IHdl with (r:=r)(c:=c); auto.
  Qed.

  (** *** 丢弃前n列 *)
  Fixpoint skipnC (n : nat) (dl : dlist tA) : dlist tA :=
    match dl with
    | [] => []
    | l :: dl' => (skipn n l) :: (skipnC n dl')
    end.

  Lemma skipnC_length : forall dl r n,
      length dl = r -> length (skipnC n dl) = r.
  Proof.
    induction dl; intros; simpl in *; auto.
    destruct r. lia. rewrite IHdl with (r:=r); auto.
  Qed.
  
  Lemma skipnC_width : forall (dl : dlist tA) c n,
      width dl c -> n < c -> width (skipnC n dl) (c - n).
  Proof.
    induction dl; intros; simpl in *; auto. constructor. inversion H.
    constructor; auto. rewrite skipn_length. lia. apply IHdl with (c:=c); auto.
  Qed.

  Lemma skipnC_overflow : forall dl r c n,
      length dl = r -> width dl c -> n >= c -> skipnC n dl = dnil r.
  Proof.
    induction dl; intros; simpl in *; auto.
    - subst. auto.
    - destruct r; simpl in *. lia. inversion H. inversion H0.
      rewrite IHdl with (r:=r)(c:=c); auto. f_equal; auto.
      rewrite skipn_all2; auto. lia.
  Qed.
  

  (** *** 删除一行 *)
  (*
  Definition dlremoveRow (dl : dlist tA) (i : nat) : dlist tA :=
    (firstn i dl) ++ (skipn (S i) dl).

  Lemma dlremoveRow_length : forall dl r i,
      length dl = (S r) -> i < S r -> length (dlremoveRow dl i) = r.
  Proof.
    intros. unfold dlremoveRow.
    rewrite app_length.
    rewrite firstn_length, skipn_length. lia.
  Qed.
    
  Lemma dlremoveRow_width : forall dl c i,
      width dl c -> width (dlremoveRow dl i) c.
  Proof.
    intros. unfold dlremoveRow. apply app_width. split.
    apply firstn_width; auto. apply skipn_width; auto.
  Qed.
   *)

  Fixpoint dlremoveRow (dl : dlist tA) (i : nat) : dlist tA :=
    match dl with
    | [] => []
    | l :: dl' => match i with
                 | O => dl'
                 | S i' => l :: (dlremoveRow dl' i')
                 end
    end.

  Lemma dlremoveRow_length : forall dl r i,
      length dl = (S r) -> i < S r -> length (dlremoveRow dl i) = r.
  Proof.
    induction dl; intros; simpl in *. lia. destruct i; auto.
    destruct r; try lia. simpl. rewrite IHdl with (r:=r); auto. lia.
  Qed.
    
  Lemma dlremoveRow_width : forall dl c i,
      width dl c -> width (dlremoveRow dl i) c.
  Proof.
    induction dl; intros; simpl in *; auto.
    apply cons_width_iff in H. destruct H. destruct i; auto.
    apply cons_width_iff. split; auto.
  Qed.

  
  (** *** 删除一列 *)
  Definition dlremoveCol (dl : dlist tA) (i : nat) : dlist tA :=
    (firstnC i dl) @@ (skipnC (S i) dl).

  Lemma dlremoveCol_length : forall dl r i,
      length dl = r -> length (dlremoveCol dl i) = r.
  Proof.
    intros. unfold dlremoveCol. rewrite dlappc_length with (r:=r); auto.
    rewrite firstnC_length with (r:=r); auto.
    rewrite skipnC_length with (r:=r); auto.
  Qed.
  
  Lemma dlremoveCol_width : forall (dl : dlist tA) c i,
      width dl (S c) -> i < (S c) -> width (dlremoveCol dl i) c.
  Proof.
    intros. unfold dlremoveCol.
    replace c with (i + (S c - (S i))); try lia. apply dlappc_width.
    apply firstnC_width with (c:=S c); auto.
    destruct (i =? c) eqn:Ei.
    - apply Nat.eqb_eq in Ei. subst.
      rewrite skipnC_overflow with (r:=length dl) (c:=S c); auto.
      rewrite Nat.sub_diag. apply dnil_width.
    - apply Nat.eqb_neq in Ei.
      apply skipnC_width with (c:=S c); auto. lia.
  Qed.
  

  (** *** 删除一行和一列 *)
  Definition dlremove (dl : dlist tA) (i j : nat) : dlist tA :=
    dlremoveCol (dlremoveRow dl i) j.

  Lemma dlremove_length : forall dl r c i j,
      length dl = (S r) -> width dl c -> i < S r -> j < c ->
      length (dlremove dl i j) = r.
  Proof.
    intros. unfold dlremove.
    rewrite dlremoveCol_length with (r:=r); auto.
    rewrite dlremoveRow_length with (r:=r); auto.
  Qed.
  
  Lemma dlremove_width : forall dl r c i j,
      length dl = r -> width dl (S c) -> i < r -> j < S c ->
      width (dlremove dl i j) c.
  Proof.
    intros. unfold dlremove.
    apply dlremoveCol_width; auto. apply dlremoveRow_width; auto.
  Qed.

End dlremove.

Section test.
  Let dl := [[1;2;3];[4;5;6];[7;8;9]].
  (* Compute skipnC 3 []. *)
  (* Compute skipnC 3 dl. *)
  (* Compute dlremove dl 1 1. *)
  
End test.


(* ===================================================================== *)
(** ** Setoid equal of list *)
Section listSetoidEq.
  Context {tA : Type}.

  (** Two list `l1` and `l2` are setoid equal under `R` relation *)
  Definition listSetoidEq {tA} (R : tA -> tA -> Prop) (l1 l2 : list tA) : Prop :=
    SetoidList.eqlistA R l1 l2.
  
  (** Two dlist `d1` and `d2` are setoid equal under `R` relation *)
  Definition dlistSetoidEq {tA} (R : tA -> tA -> Prop) (d1 d2 : dlist tA) : Prop :=
    SetoidList.eqlistA (listSetoidEq R) d1 d2.
  
End listSetoidEq.


(* ======================================================================= *)
(** ** Special search algorithm *)
Section search.

  (** Find the minimum element from a list *)
  Section list_min.
    (** Find the minimum element from a list (Auxiliary function).
      Parameters:
      l         the given list
      cmp       compare function, t1 < t2 is true, otherwise false
      val       minimum value, init is the head of l
         
      Return:
      if the given list is empty, return val
      otherwise, return the value we need.
     *)
    Fixpoint list_min_aux {tA} (val : tA) (l : list tA) (cmp : tA -> tA -> bool) : tA :=
      match l with
      | [] => val
      | a :: tl =>
          if cmp a val
          then list_min_aux a tl cmp
          else list_min_aux val tl cmp
      end.

    (** Find the minimum element from a list.

      Parameters:
      T0    default value of A
      cmp   compare function, t1 < t2 is true, otherwise false
      l     the given list
         
      Return:
      if the given list is empty, return T0
      otherwise, return the value we need.
     *)
    Definition list_min {tA} (T0 : tA) (cmp : tA -> tA -> bool) (l : list tA) : tA :=
      list_min_aux (hd T0 l) l cmp.

    Section test.
      
      Open Scope nat.
      (* Compute list_min 9 Nat.ltb []. *)
      (* Compute list_min 0 Nat.ltb [2;3;4;1;5]. *)
      (* Compute list_min 0 Nat.ltb [2;3;4;1;1;5]. (* find the first minimum *) *)
      (* Compute list_min 0 Nat.ltb [1;2;3;4;5]. *)
      (* Compute list_min 0 Nat.ltb [2;3;4;5;1]. *)
      
    End test.

  End list_min.


  (** Find the index of the minimum element from a list *)
  Section list_min_pos.
    (** Find the index of the minimum element from a list (Auxiliary function).

      Parameters:
      l         the given list
      cmp       compare function, t1 < t2 is true, otherwise false
      min_val   minimum value, init is the head of l
      min_pos   record position where the element is minum, init is 0
      cnt       to count the position, init is 0
         
      Return:
      if the given list is empty, return min_pos
      otherwise, return the value we need.
     *)
    Fixpoint list_min_pos_aux {tA} (cmp : tA -> tA -> bool) (l : list tA) 
      (min_val : tA) (min_pos : nat) (cnt : nat) : nat :=
      match l with
      | [] => min_pos
      | a :: tl =>
          if cmp a min_val 
          then list_min_pos_aux cmp tl a cnt (S cnt)
          else list_min_pos_aux cmp tl min_val min_pos (S cnt)
      end.

    (** Find the index of the minimum element from a list.

      Parameters:
      T0    default value of A, only be used as the parameter of hd, any value is ok.
      cmp   compare function, t1 < t2 is true, otherwise false
      l     the given list
         
      Return:
      if the given list is empty, return 0
      otherwise, return the value we need.
     *)
    Definition list_min_pos {tA} (A0 : tA) (cmp : tA -> tA -> bool) (l : list tA) : nat :=
      list_min_pos_aux cmp l (hd A0 l) 0 0.

    (** Spec: no any other elements is smaller than the result. *)
    Lemma list_min_pos_spec : forall {tA} (A0 : tA) (cmp : tA -> tA -> bool) (l : list tA),
        let min_pos :=  list_min_pos A0 cmp l in
        let min_val := nth min_pos l A0 in
        Forall (fun a => cmp a min_val = false) l.
    Proof.
      intros tA A0 cmp l. simpl. induction l; constructor.
    Abort.

    Section test.
      
      Open Scope nat.
      (* Compute list_min_pos 9 Nat.ltb []. *)
      (* Compute list_min_pos 0 Nat.ltb [2;3;4;1;5]. *)
      (* Compute list_min_pos 0 Nat.ltb [2;3;4;1;1;5]. (* find the first minimum *) *)
      (* Compute list_min_pos 0 Nat.ltb [1;2;3;4;5]. *)
      (* Compute list_min_pos 0 Nat.ltb [2;3;4;5;1]. *)
      
    End test.
  End list_min_pos.

End search.

