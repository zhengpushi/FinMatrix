(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : sequence model (seqsum is tail recursion)
  author    : ZhengPu Shi
  date      : 2022.06
 *)

Require Export Basic.
Require Export NatExt.
Require Export ListExt.
Require Export Hierarchy.

Generalizable Variables A Aadd Azero Aopp Amul Aone Ainv Ale Alt.
Generalizable Variables B Badd Bzero.

Open Scope nat_scope.
Open Scope A_scope.


(* ######################################################################### *)
(** * Properties of sequence *)

(* ======================================================================= *)
(** ** Basic properties of sequence *)

(** Top (S n) elements of a sequence satisfy P, iff
    top n elements of the sequencoe satisfy P and the n-th element hold too. *)
Lemma seq_prop_S_iff : forall (P : nat -> Prop) (n : nat),
    (forall i, i < S n -> P i) <-> (forall i, i < n -> P i) /\ P n.
Proof.
  intros. split; intros.
  - split; auto.
  - destruct H. bdestruct (i =? n); subst; auto. apply H; lia.
Qed.

(* ======================================================================= *)
(** ** Equality of sequence *)
Section seqeq.
  Context {A : Type}.
  
  (** Equality of two sequence which have one index *)
  Definition seqeq n (f g : nat -> A) := forall i, i < n -> f i = g i.

  (** seqeq is an equivalence relation *)
  #[export] Instance seqeq_equiv : forall n, Equivalence (seqeq n).
  Proof.
    intros. constructor; intro; intros; hnf in *; intros; auto.
    rewrite H; auto. rewrite H,H0; auto.
  Qed.

  (** seqeq of S has a equivalent form. *)
  Lemma seqeq_S : forall n (f g : nat -> A),
      seqeq (S n) f g <-> (seqeq n f g) /\ (f n = g n).
  Proof.
    intros. unfold seqeq. split; intros. split; auto.
    destruct H. bdestruct (i =? n); subst; auto. apply H. lia.
  Qed.

  (** seqeq is decidable  *)
  Lemma seqeq_dec : forall n f g,
      (forall a b : A, {a = b} + {a <> b}) -> {seqeq n f g} + {~seqeq n f g}.
  Proof.
    intros n f g H. unfold seqeq. induction n.
    - left. easy.
    - destruct IHn as [H1 | H1].
      + destruct (H (f n) (g n)) as [H2 | H2].
        * left. intros. bdestruct (i =? n). subst; auto. apply H1. lia.
        * right. intro H3. rewrite H3 in H2; auto.
      + right. intro H3. destruct H1. auto.
  Qed.
  
End seqeq.

(* ======================================================================= *)
(** ** Equality of sequence with two indexes *)
Section seq2eq.
  Context {A : Type}.

  (** Equality of two sequence which have two indexes *)
  Definition seq2eq r c (f g : nat -> nat -> A) := 
    forall ri ci, ri < r -> ci < c -> f ri ci = g ri ci.
  
  (** seq2eq of Sr has a equivalent form. *)
  Lemma seq2eq_Sr : forall r c (f g : nat -> nat -> A), 
      seq2eq (S r) c f g <-> (seq2eq r c f g) /\ (seqeq c (f r) (g r)).
  Proof.
    intros. unfold seq2eq, seqeq. split; intros. split; auto.
    destruct H. bdestruct (ri =? r); subst; auto. apply H; lia.
  Qed.

  (** seq2eq of Sc has a equivalent form. *)
  Lemma seq2eq_Sc : forall r c (f g : nat -> nat -> A), 
      seq2eq r (S c) f g <-> (seq2eq r c f g) /\ (seqeq r (fun i => f i c) (fun i => g i c)).
  Proof.
    intros. unfold seq2eq, seqeq. split; intros. split; auto.
    destruct H. bdestruct (ci =? c); subst; auto. apply H; lia.
  Qed.

  #[export] Instance seq2eq_equiv : forall r c, Equivalence (seq2eq r c).
  Proof.
    intros. unfold seq2eq. constructor; intro; intros; auto.
    rewrite H; auto. rewrite H,H0; auto.
  Qed.

  (** seq2eq is decidable  *)
  Lemma seq2eq_dec : forall r c f g,
      (forall a b : A, {a = b} + {a <> b}) -> {seq2eq r c f g} + {~seq2eq r c f g}.
  Proof.
    intros r c f g H. unfold seq2eq. revert c. induction r; intros.
    - left. easy.
    - destruct (IHr c) as [H1 | H1].
      + (* give a new proposition *)
        pose proof (seqeq_dec c (f r) (g r) H) as H2. unfold seqeq in H2.
        destruct H2 as [H2 | H2].
        * left. intros. bdestruct (ri =? r); subst; auto. apply H1; lia.
        * right. intro H3. specialize (H3 r). destruct H2. auto.
      + right. intro H2. destruct H1. auto.
  Qed.
  
End seq2eq.


(* ######################################################################### *)
(** * Folding of a sequence *)
Section seqfold.
  Context {A B : Type}.

  (** ((a + v.1) + v.2) + ... *)
  Fixpoint seqfoldl (s : nat -> A) (n : nat) (b : B) (f : B -> A -> B) : B :=
    match n with
    | O => b
    | S n' => seqfoldl s n' (f b (s n')) f
    end.
    
  (** ... + (v.(n-1) + (v.n + a)) *)
  Fixpoint seqfoldr (s : nat -> A) (n : nat) (b : B) (g : A -> B -> B) : B :=
    match n with
    | O => b
    | S n' => seqfoldr s n' (g (s n') b) g
    end.

  Lemma seqfoldl_eq_seqfoldr :
    forall (s : nat -> A) (n : nat) (b : B)
      (f : B -> A -> B) (g : A -> B -> B) (f_eq_b : forall a b, f b a = g a b),
      seqfoldl s n b f = seqfoldr s n b g.
  Proof.
    intros. revert s n b. induction n; intros; simpl; auto.
    rewrite IHn. f_equal. auto.
  Qed.

  Lemma seqfoldl_eq : forall (s1 s2 : nat -> A) (n : nat) (b1 b2 : B) (f : B -> A -> B),
      (forall i, i < n -> s1 i = s2 i) -> b1 = b2 ->
      seqfoldl s1 n b1 f = seqfoldl s2 n b2 f.
  Proof.
    intros s1 s2 n. revert s1 s2. induction n; intros; auto.
    simpl. apply IHn; auto. subst. f_equal. auto.
  Qed.

  Lemma seqfoldr_eq : forall (s1 s2 : nat -> A) (n : nat) (b1 b2 : B) (f : A -> B -> B),
      (forall i, i < n -> s1 i = s2 i) -> b1 = b2 ->
      seqfoldr s1 n b1 f = seqfoldr s2 n b2 f.
  Proof.
    intros s1 s2 n. revert s1 s2. induction n; intros; auto.
    simpl. apply IHn; auto. subst. f_equal. auto.
  Qed.

End seqfold.

(* ######################################################################### *)
(** * Sum/Product of a sequence *)

(** ** Basic properties for sequence sum/product *)
Section seqsum_seqprod.

  (** *** Sequence product *)

  (* Let's have a monoid structure *)
  Context `{HMonoid : Monoid}.
  Notation "0" := Azero : A_scope.
  Infix "+" := Aadd : A_scope.
  
  (** Sum of a sequence.
      ∑(n,f) = f[0] + (... (f[n-2] + (f[n-1] + 0)) ...)  *)
  Fixpoint seqsumAux (n : nat) (f : nat -> A) (acc : A) : A :=
    match n with
    | O => acc
    | S n' => seqsumAux n' f (f n' + acc)
    end.
  Definition seqsum (n : nat) (f : nat -> A) : A := seqsumAux n f 0.

  (** Replace the inital value of seqsumAux *)
  Lemma seqsumAux_rebase : forall n f a, seqsumAux n f a = seqsumAux n f 0 + a.
  Proof.
    induction n; intros; simpl. amonoid.
    rewrite IHn. rewrite IHn with (a:=f n + 0). amonoid.
  Qed.
  
  (* seqsum with length 0 equal to 0 *)
  Lemma seqsum_len0 : forall f, seqsum 0 f = 0.
  Proof. intros. auto. Qed.

  (** Sum a sequence of (S n) elements, equal to addition of Sum and tail *)
  Lemma seqsumS_tail : forall f n, seqsum (S n) f = seqsum n f + f n.
  Proof. unfold seqsum. intros; simpl. rewrite seqsumAux_rebase. amonoid. Qed.
  
  (** Sum a sequence of (S n) elements, equal to addition of head and Sum *)
  Lemma seqsumS_head : forall n f, seqsum (S n) f = f O + seqsum n (fun i => f (S i)).
  Proof.
    unfold seqsum. induction n; intros; simpl. auto.
    rewrite seqsumAux_rebase with (a:=(f (S n) + 0)).
    rewrite <- !associative. rewrite <- IHn. simpl.
    rewrite seqsumAux_rebase. rewrite seqsumAux_rebase with (a:=(f n + 0)). amonoid.
  Qed.

  (** Sum of a sequence which every element is zero get zero. *)
  Lemma seqsum_eq0 : forall (n : nat) (f : nat -> A), 
      (forall i, i < n -> f i = 0) -> seqsum n f = 0.
  Proof.
    unfold seqsum. induction n; simpl; intros. auto.
    rewrite seqsumAux_rebase. rewrite IHn; auto. rewrite H; auto. amonoid.
  Qed.

  (** Two sequences are equal, imply the sum are equal. *)
  Lemma seqsum_eq : forall (n : nat) (f g : nat -> A),
      (forall i, i < n -> f i = g i) -> seqsum n f = seqsum n g.
  Proof.
    induction n; intros; simpl. rewrite !seqsum_len0. auto.
    rewrite !seqsumS_tail. rewrite IHn with (g:=g); auto. f_equal; auto.
  Qed.

  (** Sum a sequence which only one item is nonzero, then got this item. *)
  Lemma seqsum_unique : forall (n : nat) (f : nat -> A) (a : A) (i : nat), 
      i < n -> f i = a -> (forall j, j < n -> j <> i -> f j = 0) -> seqsum n f = a.
  Proof.
    induction n; intros. lia.
    rewrite seqsumS_tail. bdestruct (i =? n).
    - subst. rewrite seqsum_eq0. amonoid. intros. apply H1; lia.
    - rewrite IHn with (a:=a)(i:=i); auto; try lia. rewrite H1; auto. amonoid.
  Qed.

  (** Sum the m+n elements equal to plus of two parts.
      Σ[i,0,(m+n)] f(i) = Σ[i,0,m] f(i) + Σ[i,0,n] f(m + i). *)
  Lemma seqsum_plusIdx : forall m n f,
      seqsum (m + n) f = seqsum m f + seqsum n (fun i => f (m + i)%nat). 
  Proof.
    (* induction on `n` is simpler than on `m` *)
    intros. induction n.
    - rewrite seqsum_len0. rewrite Nat.add_0_r. amonoid.
    - replace (m + S n)%nat with (S (m + n))%nat; auto.
      rewrite !seqsumS_tail. rewrite IHn. amonoid.
  Qed.
  
  (** Sum the m+n elements equal to plus of two parts.
      (i < m -> f(i) = g(i)) ->
      (i < n -> f(m+i) = h(i)) ->
      Σ[i,0,(m+n)] f(i) = Σ[i,0,m] g(i) + Σ[i,0,n] h(i). *)
  Lemma seqsum_plusIdx_ext : forall m n f g h,
      (forall i, i < m -> f i = g i) ->
      (forall i, i < n -> f (m + i)%nat = h i) ->
      seqsum (m + n) f = seqsum m g + seqsum n h.
  Proof.
    intros. induction n; simpl.
    - rewrite seqsum_len0. rewrite Nat.add_0_r. amonoid. apply seqsum_eq. auto.
    - replace (m + S n)%nat with (S (m + n))%nat; auto.
      rewrite !seqsumS_tail. rewrite IHn; auto. agroup.
  Qed.

  (** Sum the m+1+n elements equal to plus of three parts.
      Σ[i,0,(m+1+n)] f(i) = Σ[i,0,m] f(i) + f(m) + Σ[i,0,n] f(S (m + i)) *)
  Lemma seqsum_plusIdx_three : forall m n f,
      seqsum (m + S n) f = seqsum m f + f m + seqsum n (fun i => f (S (m + i))%nat). 
  Proof.
    intros. rewrite seqsum_plusIdx. rewrite associative. f_equal.
    rewrite seqsumS_head. f_equal.
    - f_equal. lia.
    - apply seqsum_eq; intros. f_equal. lia.
  Qed.

  (* Let's have an abelian monoid *)
  Context `{HAMonoid : AMonoid A Aadd 0}.
  
  (** Sum with plus of two sequence equal to plus with two sum. *)
  Lemma seqsum_add : forall (n : nat) (f g : nat -> A),
      seqsum n f + seqsum n g = seqsum n (fun i => f i + g i).
  Proof.
    induction n; intros; simpl. rewrite !seqsum_len0. amonoid.
    rewrite !seqsumS_tail. rewrite <- IHn; auto. amonoid.
  Qed.
  
  (** The order of two nested summations can be exchanged.
      ∑[i,0,r](∑[j,0,c] f_ij) = 
      f00 + f01 + ... + f0c + 
      f10 + f11 + ... + f1c + 
      ...
      fr0 + fr1 + ... + frc = 
      ∑[j,0,c](∑[i,0,r] f_ij) *)
  Lemma seqsum_seqsum : forall r c f,
      seqsum r (fun i => seqsum c (fun j => f i j)) =
        seqsum c (fun j => seqsum r (fun i => f i j)).
  Proof.
    induction r; intros.
    - rewrite !seqsum_len0. rewrite seqsum_eq0; auto.
    - rewrite seqsumS_tail. rewrite IHr. rewrite seqsum_add.
      apply seqsum_eq; intros. rewrite seqsumS_tail. auto.
  Qed.

  
  (** Let's have an abelian group structure *)
  Context `{HAGroup : AGroup A Aadd Azero Aopp}.
  Notation "- a" := (Aopp a) : A_scope.
  
  (** Opposition of the sum of a sequence. *)
  Lemma seqsum_opp : forall (n : nat) (f : nat -> A),
      - (seqsum n f) = seqsum n (fun i => - f i).
  Proof.
    induction n; intros; simpl.
    - rewrite !seqsum_len0. agroup.
    - rewrite !seqsumS_tail. rewrite <- IHn; auto. agroup.
  Qed.

  
  (** Let's have an abelian ring structure *)
  Context `{HARing : ARing A Aadd Azero Aopp Amul Aone}.
  Add Ring ring_inst : (make_ring_theory HARing).
  Notation "1" := Aone : A_scope.
  Infix "*" := Amul : A_scope.
  
  (** Scalar multiplication of the sum of a sequence (simple form). *)
  Lemma seqsum_cmul_l : forall (n : nat) (f : nat -> A) (k : A),
      k * seqsum n f = seqsum n (fun i => k * f i).
  Proof.
    induction n; intros; simpl.
    - rewrite !seqsum_len0. ring.
    - rewrite !seqsumS_tail. ring_simplify. rewrite <- IHn. ring.
  Qed.

  (** Scalar multiplication of the sum of a sequence (simple form). *)
  Lemma seqsum_cmul_r : forall (n : nat) (f : nat -> A) (k : A),
      seqsum n f * k = seqsum n (fun i => f i * k).
  Proof.
    intros. rewrite commutative. rewrite seqsum_cmul_l.
    apply seqsum_eq; intros; ring.
  Qed.
  
  (** Product two sum equal to sum of products.
      Σ[i,0,m] f(i) * Σ[i,0,n] g(i) = Σ[i,0,m*n] f(i/n)*g(i%n).
    
      For example:
        (a + b + c) * (x + y) = a*x + a*y + b*x + b*y + c*x + c*y
   *)
  Lemma seqsum_product : forall m n f g,
      n <> O ->
      seqsum m f * seqsum n g = seqsum (m * n) (fun i => f (i / n) * g (i mod n)).
  Proof.
    induction m; intros; simpl.
    - rewrite !seqsum_len0. ring.
    - replace (n + m * n)%nat with (m * n + n)%nat by ring.
      rewrite seqsum_plusIdx. rewrite <- IHm; auto.
      rewrite seqsumS_tail. ring_simplify. agroup.
      rewrite seqsum_cmul_l. apply seqsum_eq; intros.
      rewrite add_mul_div; auto. rewrite add_mul_mod; auto.
  Qed.


  (** *** Sequence product *)

  (** Product of a sequence.
      ∏(n,f) = f[0] * (... (f[n-2] * (f[n-1] * 1)) ...)  *)
  Fixpoint seqprodAux (n : nat) (f : nat -> A) (acc : A) : A :=
    match n with
    | O => acc
    | S n' => seqprodAux n' f (f n' * acc)
    end.
  Definition seqprod (n : nat) (f : nat -> A) : A := seqprodAux n f 1.

  (** Replace the inital value of seqprodAux *)
  Lemma seqprodAux_rebase : forall n f a, seqprodAux n f a = seqprodAux n f 1 * a.
  Proof.
    induction n; intros; simpl. ring.
    rewrite IHn. rewrite IHn with (a:=f n * 1). ring.
  Qed.
  
  (** seqprod with length 0 equal to 1 *)
  Lemma seqprod_len0 : forall f, seqprod 0 f = 1.
  Proof. intros. auto. Qed.

  (** Prod a sequence of (S n) elements, equal to addition of Prod and tail *)
  Lemma seqprodS_tail : forall f n, seqprod (S n) f = seqprod n f * f n.
  Proof. unfold seqprod. intros; simpl. rewrite seqprodAux_rebase. ring. Qed.
  
  (** Prod a sequence of (S n) elements, equal to addition of head and Prod *)
  Lemma seqprodS_head : forall n f, seqprod (S n) f = f O * seqprod n (fun i => f (S i)).
  Proof.
    unfold seqprod. induction n; intros; simpl. auto.
    rewrite seqprodAux_rebase with (a:=(f (S n) * 1)).
    rewrite <- !associative. rewrite <- IHn. simpl.
    rewrite seqprodAux_rebase.
    rewrite seqprodAux_rebase with (a:=(f n * 1)). ring.
  Qed.

  (** Product of a sequence which every element is one get one. *)
  Lemma seqprod_eq1 : forall (n : nat) (f : nat -> A), 
      (forall i, i < n -> f i = 1) -> seqprod n f = 1.
  Proof.
    unfold seqprod. induction n; simpl; intros. auto.
    rewrite seqprodAux_rebase. rewrite IHn; auto. rewrite H; auto. ring.
  Qed.

  (** Two sequences are equal, imply the prod are equal. *)
  Lemma seqprod_eq : forall (n : nat) (f g : nat -> A),
      (forall i, i < n -> f i = g i) -> seqprod n f = seqprod n g.
  Proof.
    induction n; intros; simpl. rewrite !seqprod_len0. auto.
    rewrite !seqprodS_tail. rewrite IHn with (g:=g); auto. f_equal; auto.
  Qed.

  (** Prod a sequence which only one item is non-one, then got this item. *)
  Lemma seqprod_unique : forall (n : nat) (f : nat -> A) (a : A) (i : nat), 
      i < n -> f i = a -> (forall j, j < n -> j <> i -> f j = 1) -> seqprod n f = a.
  Proof.
    induction n; intros. lia.
    rewrite seqprodS_tail. bdestruct (i =? n).
    - subst. rewrite seqprod_eq1. ring. intros. apply H1; lia.
    - rewrite IHn with (a:=a)(i:=i); auto; try lia. rewrite H1; auto. ring.
  Qed.

  (** Prod the m+n elements equal to plus of two parts.
      ∏[i,0,(m+n)] f(i) = ∏[i,0,m] f(i) * ∏[i,0,n] f(m + i). *)
  Lemma seqprod_plusIdx : forall m n f,
      seqprod (m + n) f = seqprod m f * seqprod n (fun i => f (m + i)%nat). 
  Proof.
    (* induction on `n` is simpler than on `m` *)
    intros. induction n.
    - rewrite seqprod_len0. rewrite Nat.add_0_r. ring.
    - replace (m + S n)%nat with (S (m + n))%nat; auto.
      rewrite !seqprodS_tail. rewrite IHn. ring.
  Qed.

  (** Prod the m+1+n elements equal to product of three parts.
      ∏[i,0,(m+1+n)] f(i) = ∏[i,0,m] f(i) * f(m) * ∏[i,0,n] f(S (m + i)) *)
  Lemma seqprod_plusIdx_three : forall m n f,
      seqprod (m + S n) f = seqprod m f * f m * seqprod n (fun i => f (S (m + i))%nat). 
  Proof.
    intros. rewrite seqprod_plusIdx. rewrite associative. f_equal.
    rewrite seqprodS_head. f_equal.
    - f_equal. lia.
    - apply seqprod_eq; intros. f_equal. lia.
  Qed.
  
  (** Scalar multiplication of the prod of a sequence (simple form). *)
  Lemma seqprod_cmul_l : forall (n : nat) (f : nat -> A) (k : A) (j : nat),
      j < n ->
      k * seqprod n f =
        seqprod n (fun i => if i =? j then (k * f i) else f i).
  Proof.
    induction n; intros; simpl. lia.
    rewrite !seqprodS_tail. ring_simplify.
    bdestruct (j =? n).
    - subst.
      rewrite Nat.eqb_refl. pose aringMulAMonoid. amonoid.
      apply seqprod_eq; intros.
      bdestruct (i =? n); auto; lia.
    - rewrite <- IHn; try lia. f_equal.
      bdestruct (n =? j); auto. subst; easy.
  Qed.

  (** Scalar multiplication of the prod of a sequence (simple form). *)
  Lemma seqprod_cmul_r : forall (n : nat) (f : nat -> A) (k : A) (j : nat),
      j < n ->
      seqprod n f * k =
        seqprod n (fun i => if i =? j then (f i * k) else f i).
  Proof.
    intros. rewrite commutative. rewrite seqprod_cmul_l with (j:=j); auto.
    apply seqprod_eq; intros. bdestruct (i =? j); ring.
  Qed.
  
End seqsum_seqprod.

(** ** Scalar multiplication of a sequence with different type. *)
Section seqsum_ext.

  Context `{HAMonoidA : AMonoid}.
  Context `{HAMonoidB : AMonoid B Badd Bzero}.
  Context (cmul : A -> B -> B).
  Infix "*" := cmul.

  (** a * ∑(bi) = a*(b1+b2+...) = a*b1+a*b2+... = ∑(a*bi) *)
  Section form1.
    Context (cmul_zero_keep : forall a : A, cmul a Bzero = Bzero).
    Context (cmul_badd : forall (a : A) (b1 b2 : B),
                a * (Badd b1 b2) = Badd (a * b1) (a * b2)).
    Lemma seqsum_cmul_l_ext : forall {n} (a : A) (f : nat -> B),
        a * (@seqsum _ Badd Bzero n f) = @seqsum _ Badd Bzero n (fun i => a * f i).
    Proof.
      induction n; intros; simpl; auto. unfold seqsum in *.
      rewrite (seqsumAux_rebase _ f). rewrite (seqsumAux_rebase _ (fun i => a * f i)).
      rewrite cmul_badd. rewrite IHn. amonoid.
    Qed.
  End form1.
  
  (** ∑(ai) * b = (a1+a2+a3)*b = a1*b+a2*b+a3*b = ∑(ai*b) *)
  Section form2.
    Context (cmul_zero_keep : forall b : B, cmul Azero b = Bzero).
    Context (cmul_aadd : forall (a1 a2 : A) (b : B),
                (Aadd a1 a2) * b = Badd (a1 * b) (a2 * b)).
    Lemma seqsum_cmul_r_ext : forall {n} (b : B) (f : nat -> A),
        (@seqsum _ Aadd Azero n f) * b = @seqsum _ Badd Bzero n (fun i => f i * b).
    Proof.
      induction n; intros; simpl; auto. unfold seqsum in *.
      rewrite (seqsumAux_rebase _ f). rewrite (seqsumAux_rebase _ (fun i => f i * b)).
      rewrite !cmul_aadd. rewrite IHn. amonoid.
      rewrite cmul_zero_keep. amonoid.
    Qed.
  End form2.
  
End seqsum_ext.


(* ======================================================================= *)
(** ** More properties of sequence on special structure *)
Section seqsum_more.

  Context `{HOrderedARing : OrderedARing}.
  Add Ring ring_inst : (make_ring_theory HOrderedARing).
  Infix "+" := Aadd.
  Notation "2" := (Aone + Aone).
  Notation "0" := Azero.
  Infix "*" := Amul.
  Notation "- a" := (Aopp a).
  Infix "-" := (fun a b => a + (- b)).
  Notation "a ²" := (a * a) (at level 1) : A_scope.
  Notation seqsum := (@seqsum _ Aadd 0).
  Infix "<" := Alt : A_scope.
  Infix "<=" := Ale : A_scope.

  (** If all elements of a sequence are >= 0, then the sum is >= 0 *)
  Lemma seqsum_ge0 : forall n (f : nat -> A), (forall i, (i < n)%nat -> 0 <= f i) -> 0 <= seqsum n f.
  Proof.
    induction n; intros.
    - simpl. apply le_refl.
    - rewrite seqsumS_tail.
      replace 0 with (0 + 0) by ring.
      apply le_add_compat; auto.
      rewrite identityLeft. apply IHn; auto.
  Qed.
  
  (** If all elements of a sequence are >= 0, and the sum of top (n+1) elements of
      the sequence is = 0, then the sum of top n elements are 0 *)
  Lemma seqsum_eq0_less : forall n (f : nat -> A),
      (forall i, (i < S n)%nat -> 0 <= f i) ->
      seqsum (S n) f = 0 -> seqsum n f = 0.
  Proof.
    intros. rewrite seqsumS_tail in H0.
    assert (0 <= f n); auto.
    assert (0 <= seqsum n f). apply seqsum_ge0; auto.
    apply add_eq0_imply_0_l in H0; auto.
  Qed.

  (** If all elements of a sequence are >= 0, and the sum of the sequence is = 0,
      then all elements of the sequence are 0. *)
  Lemma seqsum_eq0_imply_seq0 : forall (f : nat -> A) (n : nat), 
      (forall i, (i < n)%nat -> 0 <= f i) -> seqsum n f = 0 -> (forall i, (i < n)%nat -> f i = 0).
  Proof.
    intros f n. induction n. intros H1 H2 i H3; try easy. intros.
    assert (i < n \/ i = n)%nat by nia. destruct H2.
    - apply IHn; auto. apply seqsum_eq0_less; auto.
    - subst.
      assert (0 <= f n); auto.
      assert (0 <= seqsum n f). apply seqsum_ge0; auto.
      rewrite seqsumS_tail in H0.
      rewrite commutative in H0. apply add_eq0_imply_0_l in H0; auto.
  Qed.
  
  (** If all elements of a sequence are >= 0, then every element is <= the sum *)
  Lemma seqsum_ge_any : forall (f : nat -> A) (k n : nat),
      (forall i, (i < n)%nat -> 0 <= f i) -> (k < n)%nat -> f k <= seqsum n f.
  Proof.
    intros f k n. induction n; intros. lia.
    rewrite seqsumS_tail. bdestruct (k =? n)%nat.
    - subst.
      assert (0 <= seqsum n f). apply seqsum_ge0; auto.
      replace (f n) with (0 + f n) by ring.
      apply le_add_compat; auto. rewrite identityLeft. apply le_refl.
    - assert (f k <= seqsum n f).
      { apply IHn; auto. lia. }
      replace (f k) with (f k + 0) by ring.
      apply le_add_compat; auto.
  Qed.
  
  (** 2 * ∑(f*g) <= ∑(f)² + ∑(g)² *)
  Lemma seqsum_Mul2_le_PlusSqr : forall (f g : nat -> A) n,
      2 * seqsum n (fun i : nat => f i * g i) <=
        seqsum n (fun i : nat => (f i)²) + seqsum n (fun i : nat => (g i)²).
  Proof.
    intros. induction n.
    - simpl. ring_simplify. apply le_refl.
    - rewrite !seqsumS_tail. ring_simplify. 
      replace ((f n) ² + (g n) ² + seqsum n (fun i : nat => (f i) ²) +
                 seqsum n (fun i : nat => (g i) ²))
        with ((seqsum n (fun i : nat => (f i) ²) + seqsum n (fun i : nat => (g i) ²)) +
                ((f n) ² + (g n) ²)) by ring.
      apply le_add_compat; auto. apply mul_le_add_sqr.
  Qed.

  (** (∑(f*g))² <= ∑(f)² * ∑(g)² *)
  Lemma seqsum_SqrMul_le_MulSqr : forall (f g : nat -> A) n,
      (seqsum n (fun i : nat => f i * g i))² <=
        seqsum n (fun i : nat => (f i)²) * seqsum n (fun i : nat => (g i)²).
  Proof.
    intros. induction n.
    - simpl. apply le_refl.
    - rewrite !seqsumS_tail. ring_simplify.
      remember (seqsum n (fun i : nat => f i * g i)) as a1.
      remember (seqsum n (fun i : nat => (f i) ²)) as a2.
      remember (seqsum n (fun i : nat => (g i) ²)) as a3.
      remember (f n) as a. remember (g n) as b.
      replace (a1 ² + 2 * a1 * a * b + a ² * b * b)
        with ((a1 ² + a ² * b * b) + 2 * a1 * a * b) by ring.
      replace (a ² * b * b + a ² * a3 + b ² * a2 + a2 * a3)
        with ((a2 * a3 + a ² * b * b) + (a ² * a3 + b ² * a2)) by ring.
      apply le_add_compat. apply le_add_compat; auto. apply le_refl.
      rewrite Heqa1, Heqa2, Heqa3, Heqa, Heqb.
      (* Change the form by abstraction *)
      remember (fun i => f i * g n) as F.
      remember (fun i => g i * f n) as G.
      replace ((f n) ² * seqsum n (fun i : nat => (g i) ²))
        with (seqsum n (fun i => (G i) ²)).
      replace ((g n) ² * seqsum n (fun i : nat => (f i) ²))
        with (seqsum n (fun i => (F i) ²)).
      replace (2 * seqsum n (fun i : nat => f i * g i) * f n * g n)
        with (2 * seqsum n (fun i => F i * G i)).
      + rewrite (commutative (seqsum n (fun i => (G i)²))).
        apply seqsum_Mul2_le_PlusSqr.
      + rewrite !associative. f_equal.
        rewrite seqsum_cmul_r. apply seqsum_eq; intros.
        rewrite HeqF, HeqG. ring.
      + rewrite seqsum_cmul_l. apply seqsum_eq; intros. rewrite HeqF. ring.
      + rewrite seqsum_cmul_l. apply seqsum_eq; intros. rewrite HeqG. ring.
  Qed.
  
End seqsum_more.


(* ######################################################################### *)
(** * Sum of a sequence with bounds *)
Section seqsumb.
  
  (** Let's have an monoid structure *)
  Context `{HAMonoid : AMonoid}.
  Infix "+" := Aadd : A_scope.
  Notation seqsum := (@seqsum _ Aadd Azero).

  (** Sum of a sequence with lower bounds and length *)
  (* ∑(f,lo,n) = 0 + f lo + f (lo+1) + ... + f (lo+n-1) *)
  Fixpoint seqsumb (f : nat -> A) (lo n : nat) : A := 
    match n with
    | O => Azero
    | S n' => seqsumb f lo n' + f (lo + n')%nat
    end.

  (** Sum of a sequence with bounds equal to sum of a sequence *)
  Lemma seqsumb_eq_seqsum : forall (n : nat) (f : nat -> A),
      seqsumb f 0 n = seqsum n f.
  Proof.
    induction n; intros; simpl; auto. unfold seqsum in *.
    rewrite seqsumAux_rebase. rewrite IHn. amonoid.
  Qed.

  (** Sum of a sequence which every element is zero get zero. *)
  Lemma seqsumb_eq0 : forall (f : nat -> A) (lo n : nat), 
      (forall i, i < n -> f (lo+i)%nat = Azero) -> seqsumb f lo n = Azero.
  Proof.
    intros. induction n; simpl; auto. rewrite H,IHn; auto; try lia. amonoid.
  Qed.

  (** Two sequences are equal, imply the sum are equal. *)
  Lemma seqsumb_eq : forall (f g : nat -> A) (lo n : nat),
      (forall i, i < n -> f (lo+i) = g (lo+i))%nat ->
      seqsumb f lo n = seqsumb g lo n.
  Proof. intros. induction n; simpl; auto. rewrite H,IHn; auto. Qed.

  (** Sum a sequence of (S n) elements, equal to addition of Sum and tail *)
  Lemma seqsumbS_tail : forall f lo n,
      seqsumb f lo (S n) = seqsumb f lo n + f (lo + n)%nat.
  Proof. reflexivity. Qed.
  
  (** Sum a sequence of (S n) elements, equal to addition of head and Sum *)
  Lemma seqsumbS_head : forall f lo n, 
      seqsumb f lo (S n) = f lo + seqsumb (fun i => f (S i)) lo n.
  Proof.
    intros. induction n; simpl in *. amonoid. rewrite IHn.
    replace (lo + S n)%nat with (S (lo + n)); auto. amonoid.
  Qed.

  (** Sum of a sequence given by `l2f l` equal to folding of sublist of `l` *)
  Lemma seqsumb_l2f : forall (l : list A) lo n,
      length l = n ->
      seqsumb (@l2f _ Azero n l) lo n = fold_right Aadd Azero (sublist l lo n).
  Proof.
    unfold l2f. induction l; intros.
    - simpl in H. subst; simpl. auto.
    - destruct n; simpl in H. lia. rewrite seqsumbS_head. rewrite IHl; auto.
      rewrite sublist_cons. simpl. destruct lo; simpl; auto.
      rewrite (sublist_Sn Azero).
      bdestruct (length l <=? lo)%nat; simpl; auto.
      rewrite nth_overflow; try lia.
      rewrite sublist_overflow; try lia. simpl. amonoid.
  Qed.
  
  (** Sum with plus of two sequence equal to plus with two sum. *)
  Lemma seqsumb_add : forall (f g h : nat -> A) (lo n : nat),
      (forall i, i < n -> h (lo+i)%nat = f (lo+i)%nat + g (lo+i)%nat) ->
      seqsumb h lo n = seqsumb f lo n + seqsumb g lo n.
  Proof.
    intros. induction n; simpl. amonoid. rewrite IHn; auto. agroup.
  Qed.

  
  (** Let's have a group structure *)
  Context `{G : Group A Aadd Azero Aopp}.
  Notation "- a" := (Aopp a) : A_scope.

  
  (** Opposition of the sum of a sequence. *)
  Lemma seqsumb_opp : forall (f g : nat -> A) (lo n : nat),
      (forall i, i < n -> f (lo+i)%nat = - g (lo+i)%nat) ->
      (seqsumb f lo n) = - (seqsumb g lo n).
  Proof.
    intros. induction n; simpl. rewrite group_opp_0; auto.
    rewrite H,IHn; auto. rewrite group_opp_distr. amonoid.
  Qed.

  (** Sum a sequence which only one item is nonzero, then got this item. *)
  Lemma seqsumb_unique : forall (f : nat -> A) (k : A) (lo n i : nat), 
      i < n -> f (lo+i)%nat = k ->
      (forall j, j < n -> i <> j -> f (lo+j)%nat = Azero) -> seqsumb f lo n = k.
  Proof.
    intros f k lo n. induction n; intros. lia. simpl. bdestruct (i =? n).
    - subst. rewrite seqsumb_eq0; try amonoid. intros. apply H1; try lia.
    - replace (seqsumb f lo n) with k.
      replace (f (lo + n)%nat) with Azero; try amonoid.
      rewrite H1; auto. rewrite (IHn i); auto. lia.
  Qed.

  (** Sum the m+n elements equal to plus of two parts.
      Σ[i,lo,(m+n)] f(i) = Σ[i,lo,m] f(i) + Σ[i,lo+m,n] f(m + i). *)
  Lemma seqsumb_plusSize : forall f lo m n,
      seqsumb f lo (m + n) = seqsumb f lo m + seqsumb f (lo+m) n. 
  Proof.
    (* induction on `n` is simpler than on `m` *)
    intros. induction n; intros; simpl.
    - rewrite Nat.add_0_r. amonoid.
    - replace (m + S n)%nat with (S (m + n))%nat; auto. simpl.
      rewrite IHn. agroup.
  Qed.
  
  (** Sum the m+n elements equal to plus of two parts.
      (i < m -> f(lo+i) = g(lo+i)) ->
      (i < n -> f(lo+m+i) = h(lo+i)) ->
      Σ[i,lo,(m+n)] f(i) = Σ[i,lo,m] g(i) + Σ[i,lo+m,n] h(i). *)
  Lemma seqsumb_plusIdx_ext : forall f g h lo m n,
      (forall i, i < m -> f (lo+i)%nat = g (lo+i)%nat) ->
      (forall i, i < n -> f (lo+m+i)%nat = h (lo+i)%nat) ->
      seqsumb f lo (m + n) = seqsumb g lo m + seqsumb h lo n.
  Proof.
    intros. induction n; intros; simpl.
    - rewrite Nat.add_0_r. amonoid. apply seqsumb_eq. auto.
    - replace (m + S n)%nat with (S (m + n))%nat; auto. simpl.
      rewrite IHn. agroup. auto.
  Qed.
  
  (** The order of two nested summations can be exchanged.
      ∑[i,lor,r](∑[j,loc,c] f_ij) = 
      ... + f11 + ... + f1c + 
                    ...
      ... + fr1 + ... + frc = 
      ∑[j,loc,c](∑[i,lor,r] f_ij) *)
  Lemma seqsumb_seqsumb_exchg : forall f lor loc r c,
      seqsumb (fun i => seqsumb (fun j => f i j) loc c) lor r =
        seqsumb (fun j => seqsumb (fun i => f i j) lor r) loc c.
  Proof.
    intros f lor loc. induction r.
    - destruct c; simpl; auto. rewrite seqsumb_eq0; auto. amonoid.
    - destruct c; simpl; auto. rewrite seqsumb_eq0; auto. amonoid.
      replace (seqsumb (fun i : nat => seqsumb (fun j : nat => f i j) loc c
                                   + f i (loc+c)%nat) lor r)
        with ((seqsumb (fun i : nat => seqsumb (fun j : nat => f i j) loc c) lor r) +
                (seqsumb (fun i : nat => f i (loc + c)%nat) lor r)).
      replace (seqsumb (fun j : nat => seqsumb (fun i : nat => f i j) lor r
                                   + f (lor+r)%nat j) loc c)
        with ((seqsumb (fun j : nat => seqsumb (fun i : nat => f i j) lor r) loc c) +
                (seqsumb (fun j : nat => f (lor+r)%nat j) loc c)).
      rewrite IHr. agroup.
      symmetry. apply seqsumb_add; auto.
      symmetry. apply seqsumb_add; auto.
  Qed.


  (** Let's have an ring structure *)
  Context `{HARing : ARing A Aadd Azero Aopp Amul Aone}.
  Infix "*" := Amul : A_scope.
  Add Ring ring_inst : (make_ring_theory HARing).
  
  
  (** Scalar multiplication of the sum of a sequence. *)
  Lemma seqsumb_cmul : forall k (f g : nat -> A) (lo n : nat),
       (forall i, i < n -> f (lo+i)%nat = k * g (lo+i)%nat) ->
      seqsumb f lo n = k * seqsumb g lo n.
  Proof.
    intros. induction n; simpl. ring. rewrite H, IHn; auto. ring.
  Qed.

  (** Product two sum equal to sum of products.
      Σ[i,lo,m] f(i) * Σ[i,lo,n] g(i) = Σ[i,lo,m*n] f((i-lo)/n)*g((i-lo)%n).
    
      For example:
        (a + b + c) * (x + y) = a*x + a*y + b*x + b*y + c*x + c*y
   *)
  Lemma seqsumb_product : forall f g lo m n,
      n <> O ->
      seqsumb f lo m * seqsumb g lo n =
        seqsumb (fun i => f ((i-lo) / n)%nat * g ((i-lo) mod n)%nat) lo (m * n). 
  Proof.
    intros. induction m; simpl. ring. ring_simplify. rewrite IHm.
    replace (n + m * n)%nat with (m * n + n)%nat by ring.
    rewrite seqsumb_plusSize. agroup.
    Abort.
  
End seqsumb.

(* ======================================================================= *)
(** ** Usage demo *)
Section test.
  Notation seqsum := (@seqsum _ plus 0).

  Example seq1 := fun x : nat => x.
  Example seq2 := fun x : nat => S x.
  (* Compute seqsum 3 seq1. *)
  (* Compute seqsum 3 seq2. *)
End test. 
