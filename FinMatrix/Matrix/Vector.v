(*
  Copyright 2023 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : vector implemented with Fin-fun model
  author    : ZhengPu Shi
  date      : 2023.12

  remark    :
  1. High-dimensional vectors can be expressed by repeating the `vec` structure.
  2. Four forms of a "list/function/vector"
     
     FF --- vec
     | \  / |
     |  \/  |
     |  /\  |
     | /  \ |
     F ---- list
     
     FF: Fin-indexing-Function,
     F : natural-number-indexing-Function
     vec : vector has given length, made be list
     list : a list of data
     
     These forms have conversion functions between each other.
 *)


Require Export TupleExt ListExt Hierarchy.
Require Export RExt RealFunction.
Require Export Fin Sequence.
Require Import Extraction.

Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv Ale Alt Altb Aleb a2r.
Generalizable Variable B Badd Bzero.

(** Control the scope *)
Open Scope R_scope.
Open Scope nat_scope.
Open Scope fin_scope.
Open Scope A_scope.
Open Scope vec_scope.

(* ======================================================================= *)
(** ** Definition of vector type [vec] *)

Definition vec {A : Type} (n : nat) := fin n -> A.


(* ======================================================================= *)

(** ** Cast between two [vec] type with actual equal range *)

(** Cast from [vec n] type to [vec m] type if [n = m] *)
(* Definition cast_vec : forall {A} n m, n = m -> @vec A n = @vec A m. *)
(* Proof. intros. subst. auto. Qed. *)

Definition cast_vec {A} n m (a : @vec A n) (H : n = m) : @vec A m :=
  eq_rect_r (fun n0 => vec n0 -> vec m) (fun a0 : vec m => a0) H a.


(* ======================================================================= *)
(** ** Get element of a vector *)

(** v.i *)
(* Definition vnth {A n} (a : @vec A n) (i : fin n) : A := a i. *)
(* Notation "a .[ i ]" := (vnth a i) : vec_scope. *)

Notation vnth A n a i := ((a:@vec A n) (i:fin n)).
Notation "a .[ i ]" := (vnth _ _ a i) : vec_scope.

(** i = j -> a.[Fin i] = a.[Fin j] *)
Lemma vnth_eq : forall {A n} (a : @vec A n) i j (Hi: i < n) (Hj: j < n),
    i = j -> a.[Fin i Hi] = a.[Fin j Hj].
Proof. intros. subst. f_equal. apply fin_eq_iff; auto. Qed.

(* Note that: these notatiosn are dangerous.
   For example, `@nat2finS 3 0` ~ `@nat2finS 3 3` are all expected index.
   but `@nat2finS 3 4` ~ `...` will become `@nat2finS 3 0`, its error index.
 *)
Notation "a .1" := (a.[#0]) : vec_scope.
Notation "a .2" := (a.[#1]) : vec_scope.
Notation "a .3" := (a.[#2]) : vec_scope.
Notation "a .4" := (a.[#3]) : vec_scope.
Notation "a .x" := (a.[#0]) : vec_scope.
Notation "a .y" := (a.[#1]) : vec_scope.
Notation "a .z" := (a.[#2]) : vec_scope.


(* ======================================================================= *)
(** ** Equality of vector *)

(** a = b <-> forall i, a.[i] = b.[i] *)
Lemma veq_iff_vnth : forall {A} {n} (a b : @vec A n),
    a = b <-> forall (i : fin n), a.[i] = b.[i].
Proof.
  intros. split; intros; subst; auto.
  extensionality i; auto.
Qed.

(** a[(i,H1)] = b[(i,H2)] -> a[(i,H3)] = b[(i,H4)] *)
Lemma vnth_sameIdx_imply : forall {A n} {a b : @vec A n} {i} {H1 H2 H3 H4 : i < n},
    a (Fin i H1) = b (Fin i H2) ->
    a (Fin i H3) = b (Fin i H4).
Proof.
  intros.
  replace (Fin i H3:fin n) with (Fin i H1:fin n).
  replace (Fin i H4:fin n) with (Fin i H2:fin n); auto.
  apply fin_eq_iff; auto. apply fin_eq_iff; auto.
Qed.

(** {u = v} + {u <> v} *)
#[export] Instance veq_dec : forall {A n} {AeqDec : Dec (@eq A)},
    Dec (@eq (@vec A n)).
Proof.
  intros. constructor. induction n; intros.
  - left. extensionality i. fin.
  - destruct (IHn (fun i => a #(fin2nat i)) (fun i => b #(fin2nat i))) as [H|H].
    + destruct (Aeqdec (a#n) (b#n)) as [H1|H1].
      * left. extensionality i. destruct (fin2nat i ??< n)%nat as [E|E].
        ** pose proof (equal_f H). specialize (H0 (fin2PredRange i E)).
           simpl in H0. rewrite nat2finS_fin2nat in H0. auto.
        ** pose proof (fin2nat_lt i). assert (fin2nat i = n) by lia.
           assert (i = #n).
           { eapply fin2nat_imply_nat2fin in H2. rewrite <- H2.
             erewrite nat2finS_eq. auto. }
           subst. auto.
      * right. intro. destruct H1. subst. auto.
    + right. intro. subst. easy.
      Unshelve. auto.
Qed.

(** The equality of 0-D vector *)
Lemma v0eq : forall {A} (a b : @vec A 0), a = b.
Proof. intros. apply veq_iff_vnth. intros. exfalso. apply fin0_False; auto. Qed.

Lemma v0neq : forall {A} (a b : @vec A 0), a <> b -> False.
Proof. intros. destruct H. apply v0eq. Qed.

(** The equality of 1-D vector *)
Lemma v1eq_iff : forall {A} (a b : @vec A 1), a = b <-> a.1 = b.1.
Proof.
  intros. split; intros; subst; auto. unfold nat2finS in H; simpl in H.
  repeat destruct nat_ltb_reflect; try lia.
  apply veq_iff_vnth; intros. destruct i as [n Hn].
  destruct n; [apply (vnth_sameIdx_imply H)|].
  lia.
Qed.

Lemma v1neq_iff : forall {A} (a b : @vec A 1), a <> b <-> a.1 <> b.1.
Proof. intros. rewrite v1eq_iff. tauto. Qed.

(** The equality of 2-D vector *)
Lemma v2eq_iff : forall {A} (a b : @vec A 2), a = b <-> a.1 = b.1 /\ a.2 = b.2.
Proof.
  intros. split; intros; subst; auto. unfold nat2finS in H; simpl in H.
  destruct H as [H1 H2]. repeat destruct nat_ltb_reflect; try lia.
  apply veq_iff_vnth; intros. destruct i as [n Hn].
  destruct n; [apply (vnth_sameIdx_imply H1)|].
  destruct n; [apply (vnth_sameIdx_imply H2)|].
  lia.
Qed.

Lemma v2neq_iff : forall {A} (a b : @vec A 2), a <> b <-> (a.1 <> b.1 \/ a.2 <> b.2).
Proof. intros. rewrite v2eq_iff. tauto. Qed.

(** The equality of 3-D vector *)
Lemma v3eq_iff : forall {A} (a b : @vec A 3),
    a = b <-> a.1 = b.1 /\ a.2 = b.2 /\ a.3 = b.3.
Proof.
  intros. split; intros; subst; auto. unfold nat2finS in H; simpl in H.
  destruct H as [H1 [H2 H3]]. repeat destruct nat_ltb_reflect; try lia.
  apply veq_iff_vnth; intros. destruct i as [n Hn].
  destruct n; [apply (vnth_sameIdx_imply H1)|].
  destruct n; [apply (vnth_sameIdx_imply H2)|].
  destruct n; [apply (vnth_sameIdx_imply H3)|].
  lia.
Qed.

Lemma v3neq_iff : forall {A} (a b : @vec A 3),
    a <> b <-> (a.1 <> b.1 \/ a.2 <> b.2 \/ a.3 <> b.3).
Proof. intros. rewrite v3eq_iff. tauto. Qed.

(** The equality of 4-D vector *)
Lemma v4eq_iff : forall {A} (a b : @vec A 4),
    a = b <-> a.1 = b.1 /\ a.2 = b.2 /\ a.3 = b.3 /\ a.4 = b.4.
Proof.
  intros. split; intros; subst; auto. unfold nat2finS in H; simpl in H.
  destruct H as [H1 [H2 [H3 H4]]]. repeat destruct nat_ltb_reflect; try lia.
  apply veq_iff_vnth; intros. destruct i as [n Hn].
  destruct n; [apply (vnth_sameIdx_imply H1)|].
  destruct n; [apply (vnth_sameIdx_imply H2)|].
  destruct n; [apply (vnth_sameIdx_imply H3)|].
  destruct n; [apply (vnth_sameIdx_imply H4)|].
  lia.
Qed.

Lemma v4neq_iff : forall {A} (a b : @vec A 4),
    a <> b <-> (a.1 <> b.1 \/ a.2 <> b.2 \/ a.3 <> b.3 \/ a.4 <> b.4).
Proof. intros. rewrite v4eq_iff. tauto. Qed.

(** a <> b <-> ∃ i, a.[i] <> b.[i] *)
Lemma vneq_iff_exist_vnth_neq : forall {A n} (a b : @vec A n),
    a <> b <-> exists i, a.[i] <> b.[i].
Proof.
  intros. rewrite veq_iff_vnth. split; intros.
  - apply not_all_ex_not; auto.
  - apply ex_not_not_all; auto.
Qed.


(* ======================================================================= *)
(** ** Vector with same elements *)
Section vrepeat.
  Context {A} {Azero : A} {n : nat}.
  
  Definition vrepeat (a : A) : @vec A n := fun _ => a.

  (** (repeat a).i = a *)
  Lemma vnth_vrepeat : forall a i, (vrepeat a).[i] = a.
  Proof. intros. unfold vrepeat; auto. Qed.

End vrepeat.


(* ======================================================================= *)
(** ** Zero vector *)
Section vzero.
  Context {A} (Azero : A) {n : nat}.
  
  Definition vzero : @vec A n := vrepeat Azero.

  (** vzero.i = 0 *)
  Lemma vnth_vzero : forall i, vzero.[i] = Azero.
  Proof. intros. apply vnth_vrepeat. Qed.

End vzero.


(* ======================================================================= *)
(** ** Convert between nat-index-function (f) and vector (v) *)
Section f2v_v2f.
  Context {A} (Azero : A).

  Definition f2v {n} (f : nat -> A) : @vec A n := fun i => f (fin2nat i).

  (** (f2v a).i = a i *)
  Lemma vnth_f2v : forall {n} f i, (@f2v n f).[i] = f (fin2nat i).
  Proof. auto. Qed.

  Lemma f2v_inj : forall {n} (f g : nat -> A),
      @f2v n f = @f2v n g -> (forall i, i < n -> f i = g i).
  Proof. intros. unfold f2v in *. apply (equal_f H (Fin i H0)). Qed.


  Definition v2f {n} (a : @vec A n) : (nat -> A) :=
    fun i => match (i ??< n)%nat with
           | left E => a (nat2fin i E)
           | _ => Azero
           end.
  
  (** (v2f a) i = a.[nat2fin i] *)
  Lemma nth_v2f : forall {n} (a : @vec A n) (i : nat) (H : i < n),
      (v2f a) i = a.[nat2fin i H].
  Proof. intros. unfold v2f. fin. Qed.
  
  (** (v2f a) i = a[#i] *)
  Lemma nth_v2f_nat2finS : forall {n} (a : @vec A (S n)) i,
      i < S n -> (v2f a) i = a.[#i].
  Proof.
    intros. rewrite nth_v2f with (H:=H).
    rewrite nat2finS_eq with (E:=H). auto.
  Qed.
  
  Lemma v2f_inj : forall {n} (a b : @vec A n),
      (forall i, i < n -> (v2f a) i = (v2f b) i) -> a = b.
  Proof.
    intros. apply veq_iff_vnth; intros.
    specialize (H (fin2nat i) (fin2nat_lt _)).
    unfold v2f in *. fin. destruct E. fin.
  Qed.
    

  (** f2v (v2f a) = a *)
  Lemma f2v_v2f : forall {n} (a : vec n), (@f2v n (v2f a)) = a.
  Proof.
    intros. apply veq_iff_vnth; intros. rewrite vnth_f2v.
    rewrite nth_v2f with (H:=fin2nat_lt _). fin.
  Qed.

  (** v2f (f2v a) = a *)
  Lemma v2f_f2v : forall {n} (a : nat -> A) i, i < n -> v2f (@f2v n a) i = a i.
  Proof. intros. rewrite nth_v2f with (H:=H). rewrite vnth_f2v. auto. Qed.

End f2v_v2f.


(* ======================================================================= *)
(** ** Convert between list and vector *)
Section l2v_v2l.
  Context {A} (Azero : A).

  Definition l2v {n : nat} (l : list A) : vec n := fun i => nth (fin2nat i) l Azero.

  (** (l2v l).i = nth i l *)
  Lemma vnth_l2v : forall {n} (l : list A) i, (@l2v n l).[i] = nth (fin2nat i) l Azero.
  Proof. auto. Qed.

  (** l2v l1 = l2v l2 -> l1 = l2 *)
  Lemma l2v_inj : forall {n} (l1 l2 : list A),
      length l1 = n -> length l2 = n -> @l2v n l1 = @l2v n l2 -> l1 = l2.
  Proof.
    intros. unfold l2v in *.
    apply list_eq_ext with (Azero:=Azero)(n:=n); auto; intros.
    pose proof (equal_f H1). specialize (H3 (nat2fin i H2)); simpl in H3. auto.
  Qed.

  Definition v2l {n} (a : vec n) : list A := map a (finseq n).

  (** nth i (v2l a) = a.i *)
  Lemma nth_v2l : forall {n} (a : vec n) (i : nat) (E : i < n),
      nth i (v2l a) Azero = a (nat2fin i E).
  Proof. intros. unfold v2l. rewrite nth_map_finseq with (E:=E). auto. Qed.
  
  (** length (v2l a) = n *)
  Lemma v2l_length : forall {n} (a : vec n), length (v2l a) = n.
  Proof. intros. unfold v2l. rewrite map_length, finseq_length. auto. Qed.


  (** v2l a = v2l b -> a = b *)
  Lemma v2l_inj : forall {n} (a b : vec n), v2l a = v2l b -> a = b.
  Proof.
    intros. unfold v2l in *. apply veq_iff_vnth; intros.
    rewrite map_ext_in_iff in H. apply (H i). apply In_finseq.
  Qed.

  (** l2v (v2l a) = a *)
  Lemma l2v_v2l : forall {n} (a : vec n), (@l2v n (v2l a)) = a.
  Proof.
    intros. apply veq_iff_vnth; intros.
    rewrite vnth_l2v. rewrite nth_v2l with (E:=fin2nat_lt _).
    rewrite nat2fin_fin2nat. auto.
  Qed.

  (** v2l (l2v l) = l *)
  Lemma v2l_l2v : forall {n} (l : list A), length l = n -> v2l (@l2v n l) = l.
  Proof.
    intros. apply list_eq_ext with (Azero:=Azero)(n:=n); intros; auto.
    - rewrite nth_v2l with (E:=H0). rewrite vnth_l2v.
      rewrite fin2nat_nat2fin. auto.
    - apply v2l_length.
  Qed.
  
  (** ∀ v, (∃ l, l2v l = a) *)
  Lemma l2v_surj : forall {n} (a : vec n), (exists l, @l2v n l = a).
  Proof. intros. exists (v2l a). apply l2v_v2l. Qed.

  (** ∀ l, (∃ v, v2l v = l) *)
  Lemma v2l_surj : forall {n} (l : list A), length l = n -> (exists a : vec n, v2l a = l).
  Proof. intros. exists (l2v l). apply v2l_l2v; auto. Qed.

End l2v_v2l.

Section test.
  (* [1;2;3] *)
  Let v : vec 3 := fun (f:fin 3) => fin2nat f + 1.
  (* Compute (v2l v). *)
  (* Compute (l2v 3 [1;2;3]). *)
  
  Goal @l2v _ 0 3 [1;2;3] = v.
  Proof.
    apply veq_iff_vnth; intros.
    repeat (destruct i; simpl; auto; try lia).
  Qed.
  
End test.


(* ======================================================================= *)
(** ** vector with specific size *)
Section vec_specific.
  Context {A} {Azero : A}.
  Variable a1 a2 a3 a4 : A.
  
  Definition mkvec0 : @vec A 0 := fun _ => Azero. (* anything is ok *)
  Definition mkvec1 : @vec A 1 := l2v Azero [a1].
  Definition mkvec2 : @vec A 2 := l2v Azero [a1;a2].
  Definition mkvec3 : @vec A 3 := l2v Azero [a1;a2;a3].
  Definition mkvec4 : @vec A 4 := l2v Azero [a1;a2;a3;a4].
End vec_specific.


(* ======================================================================= *)
(** ** 自然基的基向量 *)
Section veye.
  Context {A} (Azero Aone : A).
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Notation vzero := (vzero 0).
  Context {one_neq_zero : 1 <> 0}.

  Definition veye {n} (i : fin n) : @vec A n :=
    fun j => if i ??= j then 1 else 0.
  
  (** (veye i).i = 1 *)
  Lemma vnth_veye_eq : forall {n} i, (@veye n i).[i] = 1.
  Proof. intros. unfold veye. fin. Qed.

  (** (veye i).j = 0 *)
  Lemma vnth_veye_neq : forall {n} i j, i <> j -> (@veye n i).[j] = 0.
  Proof. intros. unfold veye. fin. Qed.
  
  (** veye <> 0 *)
  Lemma veye_neq0 : forall {n} i, @veye n i <> vzero.
  Proof.
    intros. intro. rewrite veq_iff_vnth in H. specialize (H i).
    rewrite vnth_veye_eq, vnth_vzero in H. easy.
  Qed.
  
End veye.


(* ======================================================================= *)
(** ** natural basis, 自然基（最常见的一种标准正交基) *)
Section veyes.
  Context {A} (Azero Aone : A).
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Notation vzero := (vzero 0).
  Context {one_neq_zero : 1 <> 0}.

  Definition veyes (n : nat) : @vec (@vec A n) n := fun i => veye Azero Aone i.

  (** veyes.ii = 1 *)
  Lemma vnth_veyes_eq : forall {n} i, (veyes n).[i].[i] = 1.
  Proof. intros. unfold veyes. apply vnth_veye_eq. Qed.

  (** veyes.ij = 0 *)
  Lemma vnth_veyes_neq : forall {n} i j, i <> j -> (veyes n).[i].[j] = 0.
  Proof. intros. unfold veyes. apply vnth_veye_neq; auto. Qed.
  
End veyes.



(* ======================================================================= *)
(** ** Mapping of a vector *)
Section vmap.
  Context {A B : Type} (f : A -> B).
  
  Definition vmap {n} (a : @vec A n) : @vec B n := fun i => f (a i).

  (** (vmap f a).i = f (a.i) *)
  Lemma vnth_vmap : forall {n} (a : vec n) i, (vmap a).[i] = f (a.[i]).
  Proof. intros. unfold vmap; auto. Qed.

End vmap.


(* ======================================================================= *)
(** ** Mapping of two vectors *)
Section vmap2.
  Context {A B C : Type} (f : A -> B -> C).
  
  Definition vmap2 {n} (a : @vec A n) (b : @vec B n) : @vec C n :=
    fun i => f a.[i] b.[i].

  (** (vmap2 f a b).i = f (a.i) (b.i) *)
  Lemma vnth_vmap2 : forall {n} (a b : vec n) i, (vmap2 a b).[i] = f a.[i] b.[i].
  Proof. intros. unfold vmap2; auto. Qed.

  (* vmap2 f a b = vmap id (fun i => f u.i v.i) *)
  Lemma vmap2_eq_vmap : forall {n} (a b : vec n),
      vmap2 a b = vmap (fun a => a) (fun i => f a.[i] b.[i]).
  Proof. intros. auto. Qed.
  
End vmap2.


(** vmap2 on same type *)
Section vmap2_sametype.
  Context `{ASGroup}.

  (** vmap2 f a b = vmap2 f b a *)
  Lemma vmap2_comm : forall {n} (a b : vec n),
      vmap2 Aadd a b = vmap2 Aadd b a.
  Proof. intros. apply veq_iff_vnth; intros. unfold vmap2. agroup. Qed.
  
  (** vmap2 f (vmap2 f a b) c = vmap2 f a (vmap2 f b c) *)
  Lemma vmap2_assoc : forall {n} (a b c : vec n),
      vmap2 Aadd (vmap2 Aadd a b) c = vmap2 Aadd a (vmap2 Aadd b c).
  Proof. intros. apply veq_iff_vnth; intros. unfold vmap2. agroup. Qed.
End vmap2_sametype.


(* ======================================================================= *)
(** ** Set element of a vector *)
Section vset.
  Context {A} {Azero : A}.

  (** Set i-th element vector `a` with `x` *)
  Definition vset {n} (a : @vec A n) (i : fin n) (x : A) : @vec A n :=
    fun j => if j ??= i then x else a.[j].

  (** (vset a i x).i = x *)
  Lemma vnth_vset_eq : forall {n} (a : @vec A n) (i : fin n) (x : A),
      (vset a i x).[i] = x.
  Proof. intros. unfold vset. fin. Qed.
  
  (** (vset a i x).j = a.[j] *)
  Lemma vnth_vset_neq : forall {n} (a : @vec A n) (i j : fin n) (x : A),
      i <> j -> (vset a i x).[j] = a.[j].
  Proof. intros. unfold vset. fin. Qed.
  
End vset.


(* ======================================================================= *)
(** ** Swap two element of a vector *)
Section vswap.
  Context {A : Type}.
  
  (* Swap the i-th and j-th element of vector `a` *)
  Definition vswap {n} (a : @vec A n) (i j : fin n) : @vec A n :=
    fun k => if k ??= i
           then a.[j]
           else (if k ??= j then a.[i] else a.[k]).

  Lemma vnth_vswap_i : forall {n} (a : @vec A n) (i j : fin n),
      (vswap a i j).[i] = a.[j].
  Proof. intros. unfold vswap. fin. Qed.

  Lemma vnth_vswap_j : forall {n} (a : @vec A n) (i j : fin n),
      (vswap a i j).[j] = a.[i].
  Proof. intros. unfold vswap. fin. Qed.

  Lemma vnth_vswap_other : forall {n} (a : @vec A n) (i j k : fin n),
      i <> k -> j <> k -> (vswap a i j).[k] = a.[k].
  Proof. intros. unfold vswap. fin. Qed.

  Lemma vswap_vswap : forall {n} (a : @vec A n) (i j : fin n),
      vswap (vswap a i j) j i = a.
  Proof. intros. apply veq_iff_vnth; intros. unfold vswap. fin. Qed.

End vswap.


(* ======================================================================= *)
(** ** Insert element to a vector *)
Section vinsert.
  Context {A} {Azero : A}.
  Notation v2f := (v2f Azero).
  Notation vzero := (vzero Azero).

  Definition vinsert {n} (a : @vec A n) (i : fin (S n)) (x : A) : @vec A (S n).
    intros j. destruct (j ??< i) as [E|E].
    - refine (a.[fin2PredRange j _]).
      apply Nat.lt_le_trans with (fin2nat i); auto.
      (* apply PeanoNat.lt_n_Sm_le. *)
      apply Arith_prebase.lt_n_Sm_le.
      apply fin2nat_lt.
    - destruct (j ??= i) as [E1|E1].
      + apply x.
      + refine (a.[fin2PredRangePred j _]).
        assert (fin2nat j > fin2nat i).
        apply nat_ge_neq_imply_gt; auto. apply not_lt; auto.
        apply Nat.lt_lt_0 in H; auto.
  Defined.
  
  (** Another definition, which have simpler logic, but need `Azero`. *)
  Definition vinsert' {n} (v : @vec A n) (i : fin (S n)) (x : A) : @vec A (S n) :=
    f2v (fun j => if (j ??< fin2nat i)%nat
                then (v2f v) j
                else (if (j ??= fin2nat i)%nat
                      then x
                      else (v2f v) (pred j))).

  (* These two definitions are equivalent *)
  Lemma vinsert_eq_vinsert' : forall {n} (a : @vec A n) (i : fin (S n)) (x : A),
      vinsert a i x = vinsert' a i x.
  Proof.
    intros. apply veq_iff_vnth; intros j.
    unfold vinsert, vinsert',f2v,v2f,fin2PredRange, fin2PredRangePred.
    destruct i as [i Hi], j as [j Hj]; simpl. fin.
  Qed.

  (** j < i -> (v2f (vinsert a i x)) j = (v2f a) i *)
  Lemma vinsert_spec_lt : forall {n} (a : @vec A n) (i : fin (S n)) (x : A) (j : nat),
      j < fin2nat i -> v2f (vinsert a i x) j = v2f a j.
  Proof.
    intros. rewrite vinsert_eq_vinsert'. pose proof (fin2nat_lt i).
    unfold vinsert',v2f,f2v. fin.
  Qed.

  (** (v2f (vinsert a i x)) i = x *)
  Lemma vinsert_spec_eq : forall {n} (a : @vec A n) (i : fin (S n)) (x : A),
      v2f (vinsert a i x) (fin2nat i) = x.
  Proof.
    intros. rewrite vinsert_eq_vinsert'.
    pose proof (fin2nat_lt i). unfold vinsert',v2f,f2v. fin.
  Qed.
  
  (** i < j -> 0 < j -> j < S n -> (v2f (vinsert a i x)) j = (v2f a) (pred i) *)
  Lemma vinsert_spec_gt : forall {n} (a : @vec A n) (i : fin (S n)) (x : A) (j : nat),
      fin2nat i < j -> 0 < j -> j < S n -> v2f (vinsert a i x) j = v2f a (pred j).
  Proof.
    intros. rewrite vinsert_eq_vinsert'. pose proof (fin2nat_lt i).
    unfold vinsert',v2f,f2v. fin.
  Qed.
  
  (** j < i -> (vinsert a i x).[j] = a.[j] *)
  Lemma vnth_vinsert_lt :
    forall {n} (a : @vec A n) (i j : fin (S n)) x (H : fin2nat j < fin2nat i),
      (vinsert a i x).[j] =
        a.[fin2PredRange j (nat_lt_ltS_lt _ _ _ H (fin2nat_lt _))].
  Proof.
    intros. pose proof (vinsert_spec_lt a i x (fin2nat j) H).
    erewrite !nth_v2f in H0. fin. rewrite H0. f_equal. apply fin_eq_iff; auto.
    Unshelve. fin. pose proof (fin2nat_lt i). lia.
  Qed.

  (** (vinsert a i x).[i] = a *)
  Lemma vnth_vinsert_eq : forall {n} (a : @vec A n) (i : fin (S n)) x,
      (vinsert a i x).[i] = x.
  Proof.
    intros. pose proof (vinsert_spec_eq a i x).
    pose proof (fin2nat_lt i). unfold v2f in *. fin. 
  Qed.

  (** 0 < j -> (vinsert a i x).[j] = a.(pred j) *)
  Lemma vnth_vinsert_gt :
    forall {n} (a : @vec A n) (i j : fin (S n)) x (H : 0 < fin2nat j),
      fin2nat i < fin2nat j -> (vinsert a i x).[j] = a.[fin2PredRangePred j H].
  Proof.
    intros.
    pose proof (vinsert_spec_gt a i x (fin2nat j) H0 H (fin2nat_lt _)).
    erewrite !nth_v2f in H1. fin. rewrite H1. fin. Unshelve. fin. 
  Qed.

  (** (vzero <<- Azero) = vzero *)
  Lemma vinsert_vzero_eq0 : forall {n} i, @vinsert n vzero i Azero = vzero.
  Proof.
    intros. rewrite vinsert_eq_vinsert'.
    apply veq_iff_vnth; intros j. rewrite vnth_vzero.
    destruct i as [i Hi], j as [j Hj].
    unfold vinsert',f2v,v2f; simpl. fin.
  Qed.

  (** (a <<- x) = vzero -> x = Azero *)
  Lemma vinsert_eq0_imply_x0 {AeqDec : Dec (@eq A)} : forall {n} (a : @vec A n) i x,
      vinsert a i x = vzero -> x = Azero.
  Proof.
    intros. rewrite veq_iff_vnth in *. specialize (H i).
    rewrite vnth_vzero in H. rewrite <- H.
    symmetry. apply vnth_vinsert_eq.
  Qed.

  (** (a <<- x) = vzero -> a = vzero *)
  Lemma vinsert_eq0_imply_v0 {AeqDec : Dec (@eq A)} : forall {n} (a : @vec A n) i x,
      vinsert a i x = vzero -> a = vzero.
  Proof.
    intros.
    pose proof (vinsert_eq0_imply_x0 a i x H). subst.
    rewrite !veq_iff_vnth in *; intros j.
    destruct (j ??< i).
    - specialize (H (fin2SuccRange j)). erewrite vnth_vinsert_lt in H; fin.
    - specialize (H (fin2SuccRangeSucc j)). erewrite vnth_vinsert_gt in H; fin.
      Unshelve. fin. fin.
  Qed.

  (** (a <<- x) = vzero <-> a = vzero /\ x = Azero  *)
  Lemma vinsert_eq0_iff {AeqDec : Dec (@eq A)} : forall {n} (a : @vec A n) i x,
      vinsert a i x = vzero <-> (a = vzero /\ x = Azero).
  Proof.
    simp.
    - apply vinsert_eq0_imply_v0 in H; auto.
    - apply vinsert_eq0_imply_x0 in H; auto.
    - subst. apply vinsert_vzero_eq0.
  Qed.

  (** (a <<- x) <> vzero <-> a <> vzero \/ x <> Azero  *)
  Lemma vinsert_neq0_iff {AeqDec : Dec (@eq A)} : forall {n} (a : @vec A n) i x,
      vinsert a i x <> vzero <-> (a <> vzero \/ x <> Azero).
  Proof. intros. rewrite vinsert_eq0_iff. tauto. Qed.

End vinsert.

Section test.
  Let n := 5.
  Let a : vec n := l2v 9 [1;2;3;4;5].
  (* Compute v2l (vinsert a #1 7). *)
  (* Compute v2l (vinsert a #5 7). *)
End test.    


(* ======================================================================= *)
(** ** Remove one element *)
Section vremove.
  Context {A} {Azero : A}.
  Notation v2f := (v2f Azero).

  (** Removes i-th element from vector `a` *)
  Definition vremove {n} (a : @vec A (S n)) (i : fin (S n)) : @vec A n :=
    fun j => if j ??< i
           then a (fin2SuccRange j)
           else a (fin2SuccRangeSucc j). 

  (* Another definition, which have simpler logic, but need `Azero`. *)
  Definition vremove' {n} (a : @vec A (S n)) (i : fin (S n)) : @vec A n :=
    f2v (fun j => if (j ??< fin2nat i)%nat then v2f a j else v2f a (S j)).
  
  (* These two definitions are equivalent *)
  Lemma vremove_eq_vremove' : forall {n} (a : @vec A (S n)) (i : fin (S n)),
      vremove a i = vremove' a i.
  Proof.
    intros. apply veq_iff_vnth; intros j.
    unfold vremove, vremove', f2v, v2f.
    unfold fin2SuccRange, fin2SuccRangeSucc.
    destruct i as [i Hi], j as [j Hj]; simpl. fin.
    erewrite nat2finS_eq. apply fin_eq_iff; auto. Unshelve. auto.
  Qed.

  (** j < i -> (vremove a i).j = v.j *)
  Lemma vremove_spec_lt : forall {n} (a : @vec A (S n)) (i : fin (S n)) (j : nat),
      j < fin2nat i -> v2f (vremove a i) j = v2f a j.
  Proof.
    intros. rewrite vremove_eq_vremove'. unfold v2f,vremove',f2v.
    destruct i as [i Hi]; simpl in *. fin.
  Qed.
  
  (** i <= j -> j < n -> (vremove a i).j = v.(S j) *)
  Lemma vremove_spec_ge : forall {n} (a : @vec A (S n)) (i : fin (S n)) (j : nat),
      fin2nat i <= j -> j < n -> v2f (vremove a i) j = v2f a (S j).
  Proof.
    intros. rewrite vremove_eq_vremove'. unfold vremove',f2v,v2f.
    destruct i as [i Hi]; simpl in *. fin.
  Qed.

  (** j < i -> (vremove a i).j = a.j *)
  Lemma vnth_vremove_lt : forall {n} (a : @vec A (S n)) (i : fin (S n)) (j : fin n),
      fin2nat j < fin2nat i -> (vremove a i).[j] = v2f a (fin2nat j).
  Proof.
    intros. rewrite vremove_eq_vremove'. unfold vremove',f2v,v2f.
    destruct i as [i Hi], j as [j Hj]; simpl in *. fin.
  Qed.
  
  (** i <= j -> j < n -> (vremove a i).j = a.(S j) *)
  Lemma vnth_vremove_ge : forall {n} (a : @vec A (S n)) (i : fin (S n)) (j : fin n),
      fin2nat i <= fin2nat j -> fin2nat j < n ->
      (vremove a i).[j] = v2f a (S (fin2nat j)).
  Proof.
    intros. rewrite vremove_eq_vremove'. unfold vremove',f2v,v2f.
    destruct i as [i Hi], j as [j Hj]; simpl in *. fin.
  Qed.

  (** vremove (vinsert a i x) i = a *)
  Lemma vremove_vinsert : forall {n} (a : @vec A n) (i : fin (S n)) (x : A),
      vremove (vinsert a i x) i = a.
  Proof.
    intros. rewrite vremove_eq_vremove', (vinsert_eq_vinsert' (Azero:=Azero)).
    apply veq_iff_vnth; intros j.
    destruct i as [i Hi], j as [j Hj].
    unfold vremove',vinsert',f2v,v2f; simpl in *. fin.
  Qed.
  
  (** vinsert (vremove a i) (a.[i]) = a *)
  Lemma vinsert_vremove : forall {n} (a : @vec A (S n)) (i : fin (S n)),
      vinsert (vremove a i) i (a.[i]) = a.
  Proof.
    intros. rewrite vremove_eq_vremove', (vinsert_eq_vinsert' (Azero:=Azero)).
    apply veq_iff_vnth; intros j.
    destruct i as [i Hi], j as [j Hj].
    unfold vremove',vinsert',f2v,v2f; simpl in *. fin.
  Qed.
  
End vremove.

Section vmap_vinsert_vremove.
  Context {A B C : Type} {Azero : A} {Bzero : B} {Czero : C}.
  Context (f1 : A -> B).
  Context (f2 : A -> B -> C).

  (** vmap f (vremove a i) = vremove (vmap f v) i *)
  Lemma vmap_vremove : forall {n} (a : @vec A (S n)) i,
      vmap f1 (vremove a i) = vremove (vmap f1 a) i.
  Proof.
    intros. apply veq_iff_vnth; intros j. rewrite vnth_vmap.
    pose proof (fin2nat_lt i). pose proof (fin2nat_lt j).
    destruct (j ??< i).
    - rewrite (vnth_vremove_lt (Azero:=Azero)); auto.
      rewrite (vnth_vremove_lt (Azero:=Bzero)); auto.
      erewrite !nth_v2f. unfold vmap. auto.
    - rewrite (vnth_vremove_ge (Azero:=Azero)); try lia.
      rewrite (vnth_vremove_ge (Azero:=Bzero)); try lia.
      erewrite !nth_v2f. unfold vmap. auto.
      Unshelve. lia. lia.
  Qed.

  (** vmap2 f (vremove a i) (vremove b i) = vremove (vmap2 a b) i *)
  Lemma vmap2_vremove_vremove : forall {n} (a : @vec A (S n)) (b : @vec B (S n)) i,
      vmap2 f2 (vremove a i) (vremove b i) = vremove (vmap2 f2 a b) i.
  Proof.
    intros. apply veq_iff_vnth; intros j. rewrite vnth_vmap2.
    pose proof (fin2nat_lt i). pose proof (fin2nat_lt j).
    destruct (j ??< i).
    - rewrite (vnth_vremove_lt (Azero:=Azero)); auto.
      rewrite (vnth_vremove_lt (Azero:=Bzero)); auto.
      rewrite (vnth_vremove_lt (Azero:=Czero)); auto.
      erewrite !nth_v2f. rewrite vnth_vmap2. auto.
    - rewrite (vnth_vremove_ge (Azero:=Azero)); try lia.
      rewrite (vnth_vremove_ge (Azero:=Bzero)); try lia.
      rewrite (vnth_vremove_ge (Azero:=Czero)); try lia.
      erewrite !nth_v2f. rewrite vnth_vmap2. auto.
      Unshelve. lia. lia.
  Qed.

  (** vmap2 (vinsert a i x) b = vinsert (vmap2 a (vremove b i)) i (f x b.i) *)
  Lemma vmap2_vinsert_l : forall {n} (a : @vec A n) (b : @vec B (S n)) i (x : A),
      vmap2 f2 (vinsert a i x) b =
        vinsert (vmap2 f2 a (vremove b i)) i (f2 x (b.[i])).
  Proof.
    intros. apply veq_iff_vnth; intros j. rewrite vnth_vmap2.
    destruct (j ??< i) as [E|E].
    - rewrite (vnth_vinsert_lt (Azero:=Azero)) with (H:=E).
      rewrite (vnth_vinsert_lt (Azero:=Czero)) with (H:=E).
      rewrite vnth_vmap2. fin.
      rewrite (vnth_vremove_lt (Azero:=Bzero)); fin.
      erewrite nth_v2f with (H:=fin2nat_lt _); fin.
    - destruct (j ??= i) as [E1|E1]; fin.
      + apply fin2nat_inj in E1; rewrite E1.
        rewrite (vnth_vinsert_eq (Azero:=Azero)).
        rewrite (vnth_vinsert_eq (Azero:=Czero)). auto.
      + assert (fin2nat i < fin2nat j) by lia.
        assert (0 < fin2nat j) by lia.
        rewrite (vnth_vinsert_gt (Azero:=Azero)) with (H:=H0); auto.
        rewrite (vnth_vinsert_gt (Azero:=Czero)) with (H:=H0); auto.
        rewrite vnth_vmap2. fin.
        rewrite (vnth_vremove_ge (Azero:=Bzero)); fin.
        * assert (S (pred (fin2nat j)) < S n).
          rewrite Nat.succ_pred; try lia. apply fin2nat_lt.
          rewrite nth_v2f with (H:=H1). fin. destruct j. fin.
        * pose proof (fin2nat_lt j). lia.
  Qed.
  
  (** vmap2 a (vinsert b i x) = vinsert (vmap2 (vremove a i) b) i (f a.i x) *)
  Lemma vmap2_vinsert_r : forall {n} (a : @vec A (S n)) (b : @vec B n) i (x : B),
      vmap2 f2 a (vinsert b i x) =
        vinsert (vmap2 f2 (vremove a i) b) i (f2 (a.[i]) x).
  Proof.
    intros. apply veq_iff_vnth; intros j. rewrite vnth_vmap2.
    destruct (j ??< i) as [E|E].
    - assert (fin2nat j < n). pose proof (fin2nat_lt i). lia.
      rewrite (vnth_vinsert_lt (Azero:=Bzero)) with (H:=E).
      rewrite (vnth_vinsert_lt (Azero:=Czero)) with (H:=E).
      rewrite vnth_vmap2. f_equal.
      rewrite (vnth_vremove_lt (Azero:=Azero)); auto. simpl.
      rewrite nth_v2f with (H:=fin2nat_lt _). fin.
    - destruct (j ??= i) as [E1|E1].
      + apply fin2nat_inj in E1; rewrite E1.
        rewrite (@vnth_vinsert_eq _ Bzero).
        rewrite (@vnth_vinsert_eq _ Czero). auto.
      + assert (fin2nat i < fin2nat j) by lia.
        assert (0 < fin2nat j) by lia.
        rewrite (vnth_vinsert_gt (Azero:=Bzero)) with (H:=H0); auto.
        rewrite (vnth_vinsert_gt (Azero:=Czero)) with (H:=H0); auto.
        rewrite vnth_vmap2. f_equal.
        rewrite (vnth_vremove_ge (Azero:=Azero)); fin.
        * assert (S (pred (fin2nat j)) < S n).
          rewrite Nat.succ_pred; try lia. apply fin2nat_lt.
          rewrite nth_v2f with (H:=H1). fin. destruct j. fin.
        * pose proof (fin2nat_lt j). lia.
  Qed.

End vmap_vinsert_vremove.


(* ======================================================================= *)
(** ** Get head or tail element *)
Section vhead_vtail.
  Context {A} {Azero : A}.

  (** Get head element *)
  Definition vhead {n} (a : @vec A (S n)) : A := a.[fin0].

  (** vhead a is = a.0 *)
  Lemma vhead_spec : forall {n} (a : @vec A (S n)), vhead a = (v2f Azero a) 0.
  Proof.
    intros. unfold vhead. erewrite nth_v2f. f_equal.
    apply fin_eq_iff; auto. Unshelve. lia.
  Qed.

  (** vhead a = a $ 0 *)
  Lemma vhead_eq : forall {n} (a : @vec A (S n)), vhead a = a.[fin0].
  Proof. auto. Qed.

  
  (** Get tail element *)
  Definition vtail {n} (a : @vec A (S n)) : A := a.[#n].

  (** vtail a = a.(n - 1) *)
  Lemma vtail_spec : forall {n} (a : @vec A (S n)), vtail a = (v2f Azero a) n.
  Proof.
    intros. unfold vtail. erewrite nth_v2f. erewrite nat2finS_eq. f_equal.
    Unshelve. lia.
  Qed.

  (** vtail a = a $ (n - 1) *)
  Lemma vtail_eq : forall {n} (a : @vec A (S n)), vtail a = a.[#n].
  Proof. auto. Qed.

End vhead_vtail.


(* ======================================================================= *)
(** ** Get head or tail elements *)
Section vheadN_vtailN.
  Context {A} {Azero : A}.

  (** Get head elements *)
  Definition vheadN {m n} (a : @vec A (m + n)) : @vec A m :=
    fun i => a.[fin2AddRangeR i].

  (** i < m -> (vheadN a).i = (v2f a).i *)
  Lemma vheadN_spec : forall {m n} (a : @vec A (m + n)) i,
      i < m -> v2f Azero (vheadN a) i = (v2f Azero a) i.
  Proof.
    intros. unfold vheadN. erewrite !nth_v2f. f_equal.
    apply fin_eq_iff; auto. Unshelve. all: try lia.
  Qed.

  (** (vheadN a).i = a.i *)
  Lemma vnth_vheadN : forall {m n} (a : @vec A (m + n)) i,
      (vheadN a).[i] = a.[fin2AddRangeR i].
  Proof. auto. Qed.

  
  (** Get tail elements *)
  Definition vtailN {m n} (a : @vec A (m + n)) : @vec A n :=
    fun i => a.[fin2AddRangeAddL i].

  (** i < n -> (vtailN a).i = (v2f a).(m + i) *)
  Lemma vtailN_spec : forall {m n} (a : @vec A (m + n)) i,
      i < n -> v2f Azero (vtailN a) i = (v2f Azero a) (m + i).
  Proof.
    intros. unfold vtailN. erewrite !nth_v2f. f_equal.
    apply fin_eq_iff; auto. Unshelve. all: try lia.
  Qed.

  (** (vtailN a).i = a.(n + i) *)
  Lemma vnth_vtailN : forall {m n} (a : @vec A (m + n)) i,
      (vtailN a).[i] = a.[fin2AddRangeAddL i].
  Proof. auto. Qed.

End vheadN_vtailN.


(* ======================================================================= *)
(** ** Remove exact one element at head or tail *)
Section vremoveH_vremoveT.
  Context {A} {Azero : A}.
  Notation v2f := (v2f Azero).
  Notation vzero := (vzero Azero).

  (** *** vremoveH *)
  
  (** Remove head element *)
  Definition vremoveH {n} (a : @vec A (S n)) : @vec A n :=
    fun i => a.[fin2SuccRangeSucc i].

  (** i < n -> (vremoveH a).i = v.(S i) *)
  Lemma vremoveH_spec : forall {n} (a : @vec A (S n)) (i : nat),
      i < n -> v2f (vremoveH a) i = v2f a (S i).
  Proof.
    intros. unfold vremoveH,v2f. fin.
  Qed.
  
  (** (vremoveH a).i = a.(S i) *)
  Lemma vnth_vremoveH : forall {n} (a : @vec A (S n)) (i : fin n),
      (vremoveH a).[i] = a.[fin2SuccRangeSucc i].
  Proof. intros. unfold vremoveH. auto. Qed.
  
  (** a <> 0 -> vhead a = 0 -> vremoveH a <> 0 *)
  Lemma vremoveH_neq0_if : forall {n} (a : @vec A (S n)),
      a <> vzero -> vhead a = Azero -> vremoveH a <> vzero.
  Proof.
    intros. intro. destruct H. apply veq_iff_vnth; intros.
    rewrite veq_iff_vnth in H1. unfold vremoveH in H1. rewrite vhead_eq in H0.
    destruct (fin2nat i ??= 0)%nat as [E|E].
    - rewrite vnth_vzero. destruct i; simpl in *; subst.
      f_equal. apply fin_eq_iff; auto.
    - assert (0 < fin2nat i). pose proof (fin2nat_lt i). lia.
      specialize (H1 (fin2PredRangePred i H)).
      rewrite fin2SuccRangeSucc_fin2PredRangePred in H1. rewrite H1. cbv. auto.
  Qed.

  (** vremoveH also hold, if hold for all elements *)
  Lemma vremoveH_hold : forall {n} (a : @vec A (S n)) (P : A -> Prop),
      (forall i, P (a.[i])) -> (forall i, P ((vremoveH a).[i])).
  Proof. intros. unfold vremoveH. auto. Qed.

  
  (** *** vremoveT *)

  (** Remove tail element *)
  Definition vremoveT {n} (a : @vec A (S n)) : @vec A n :=
    fun i => a.[fin2SuccRange i].

  (** i < n -> (vremoveT a).i = a.i *)
  Lemma vremoveT_spec : forall {n} (a : @vec A (S n)) (i : nat),
      i < n -> v2f (vremoveT a) i = v2f a i.
  Proof.
    intros. unfold vremoveT,v2f. fin.
    erewrite fin2SuccRange_nat2fin. apply fin_eq_iff; auto.
    Unshelve. auto.
  Qed.
  
  (** (vremoveT a).i = a.i *)
  Lemma vnth_vremoveT : forall {n} (a : @vec A (S n)) (i : fin n),
      (vremoveT a).[i] = a.[fin2SuccRange i].
  Proof. intros. unfold vremoveT. auto. Qed.
  
  (** v <> 0 -> vtail v = 0 -> vremoveT v <> 0 *)
  Lemma vremoveT_neq0_if : forall {n} (a : @vec A (S n)),
      a <> vzero -> vtail a = Azero -> vremoveT a <> vzero.
  Proof.
    intros. intro. destruct H. apply veq_iff_vnth; intros.
    rewrite veq_iff_vnth in H1. unfold vremoveT in H1.
    rewrite vtail_eq in H0.
    destruct (fin2nat i ??= n)%nat as [E|E].
    - destruct i; simpl in *; subst. rewrite vnth_vzero. f_equal.
      erewrite nat2finS_eq. apply fin_eq_iff; auto.
    - assert (fin2nat i < n). pose proof (fin2nat_lt i). lia.
      specialize (H1 (fin2PredRange i H)).
      rewrite fin2SuccRange_fin2PredRange in H1. rewrite H1. cbv. auto.
      Unshelve. auto.
  Qed.

  (** vremoveT also hold, if hold for all elements *)
  Lemma vremoveT_hold : forall {n} (a : @vec A (S n)) (P : A -> Prop),
      (forall i, P (a.[i])) -> (forall i, P ((vremoveT a).[i])).
  Proof. intros. unfold vremoveT. auto. Qed.

End vremoveH_vremoveT.


(* ======================================================================= *)
(** ** Remove elements at head or tail *)
Section vremoveHN_vremoveTN.
  Context {A} {Azero : A}.
  Notation v2f := (v2f Azero).
  Notation vzero := (vzero Azero).

  (** *** vremoveHN *)
  
  (** Remove head elements *)
  Definition vremoveHN {m n} (a : @vec A (m + n)) : @vec A n :=
    fun i => a.[fin2AddRangeAddL i].

  (** i < n -> (vremoveHN a).i = a.(m + i) *)
  Lemma vremoveHN_spec : forall {m n} (a : @vec A (m + n)) (i : nat),
      i < n -> v2f (vremoveHN a) i = v2f a (m + i).
  Proof.
    intros. unfold vremoveHN. erewrite !nth_v2f. f_equal.
    apply fin2nat_imply_nat2fin; simpl. auto.
    Unshelve. all: lia.
  Qed.
  
  (** (vremoveHN a).i = a.(m + i) *)
  Lemma vnth_vremoveHN : forall {m n} (a : @vec A (m + n)) (i : fin n),
      (vremoveHN a).[i] = a.[fin2AddRangeAddL i].
  Proof. auto. Qed.
  
  (** a <> 0 -> vheadN v = 0 -> vremoveHN a <> 0 *)
  Lemma vremoveHN_neq0_if : forall {m n} (a : @vec A (m + n)),
      a <> vzero -> vheadN a = vzero -> vremoveHN a <> vzero.
  Proof.
    intros. intro.
    rewrite veq_iff_vnth in H0. unfold vheadN in H0.
    rewrite veq_iff_vnth in H1. unfold vremoveHN in H1.
    destruct H. apply veq_iff_vnth; intros.
    destruct (m ??<= fin2nat i)%nat as [E|E].
    - specialize (H1 (fin2AddRangeAddL' i E)).
      rewrite fin2AddRangeAddL_fin2AddRangeAddL' in H1. rewrite H1. cbv. auto.
    - assert (fin2nat i < m). lia.
      specialize (H0 (fin2AddRangeR' i H)).
      rewrite fin2AddRangeR_fin2AddRangeR' in H0. rewrite H0. cbv. auto.
  Qed.
  
  
  (** *** vremoveTN *)

  (** Remove tail elements *)
  Definition vremoveTN {m n} (a : @vec A (m + n)) : @vec A m :=
    fun i => a.[fin2AddRangeR i].

  (** i < n -> (vremoveTN a).i = a.i *)
  Lemma vremoveTN_spec : forall {m n} (a : @vec A (m + n)) (i : nat),
      i < m -> v2f (vremoveTN a) i = v2f a i.
  Proof.
    intros. unfold vremoveTN,v2f. fin.
  Qed.
  
  (** (vremoveTN a).i = a.i *)
  Lemma vnth_vremoveTN : forall {m n} (a : @vec A (m + n)) (i : fin m),
      (vremoveTN a).[i] = a.[fin2AddRangeR i].
  Proof. intros. auto. Qed.
  
  (** a <> 0 -> vtailN v = 0 -> vremoveTN a <> 0 *)
  Lemma vremoveTN_neq0_if : forall {m n} (a : @vec A (m + n)),
      a <> vzero -> vtailN a = vzero -> vremoveTN a <> vzero.
  Proof.
    intros. intro.
    rewrite veq_iff_vnth in H0. unfold vtailN in H0.
    rewrite veq_iff_vnth in H1. unfold vremoveTN in H1.
    destruct H. apply veq_iff_vnth; intros.
    destruct (m ??<= fin2nat i)%nat as [E|E].
    - specialize (H0 (fin2AddRangeAddL' i E)).
      rewrite fin2AddRangeAddL_fin2AddRangeAddL' in H0. rewrite H0. cbv. auto.
    - assert (fin2nat i < m). lia.
      specialize (H1 (fin2AddRangeR' i H)).
      rewrite fin2AddRangeR_fin2AddRangeR' in H1. rewrite H1. cbv. auto.
  Qed.

End vremoveHN_vremoveTN.


(* ======================================================================= *)
(** ** Construct vector with one element at the head or tail position *)
Section vconsH_vconsT.
  Context {A} {Azero : A}.
  Notation v2f := (v2f Azero).
  Notation vzero := (vzero Azero).

  (** *** vconsH *)

  (** cons at head: [x; a] *)
  Definition vconsH {n} (x : A) (a : @vec A n) : @vec A (S n).
    intros i. destruct (fin2nat i ??= 0)%nat. exact x.
    assert (0 < fin2nat i). apply neq_0_lt_stt; auto.
    apply (a.[fin2PredRangePred i H]).
  Defined.

  (** i = 0 -> (v2f [x; a]) i = a *)
  Lemma vconsH_spec_0 : forall {n} x (a : @vec A n) (i : nat),
      i = 0 -> v2f (vconsH x a) i = x.
  Proof.
    intros. subst. unfold vconsH,v2f; simpl. auto.
  Qed.

  (** 0 < i -> i < n -> [x; a].i = a.(pred i) *)
  Lemma vconsH_spec_gt0 : forall {n} x (a : @vec A n) (i : nat),
      0 < i -> i < n -> v2f (vconsH x a) i = v2f a (pred i).
  Proof.
    intros. unfold vconsH,v2f; simpl. fin.
  Qed.

  (** i = 0 -> [x; a].i = a *)
  Lemma vnth_vconsH_0 : forall {n} x (a : @vec A n) i,
      i = fin0 -> (vconsH x a).[i] = x.
  Proof. intros. subst. unfold vconsH. simpl. auto. Qed.
  
  (** 0 < i -> [x; a].i = a.(pred i)  *)
  Lemma vnth_vconsH_gt0 : forall {n} x (a : @vec A n) i (H: 0 < fin2nat i),
      (vconsH x a).[i] = a.[fin2PredRangePred i H].
  Proof.
    intros. unfold vconsH. fin.
  Qed.

  (** [x; a] = 0 <-> x = 0 /\ v = 0 *)
  Lemma vconsH_eq0_iff : forall {n} x (a : @vec A n),
      vconsH x a = vzero <-> x = Azero /\ a = vzero.
  Proof.
    intros. rewrite !veq_iff_vnth. split; intros.
    - split; intros; auto.
      + specialize (H fin0). rewrite vnth_vconsH_0 in H; auto.
      + specialize (H (fin2SuccRangeSucc i)). rewrite vnth_vzero in *. rewrite <- H.
        erewrite vnth_vconsH_gt0. f_equal.
        rewrite fin2PredRangePred_fin2SuccRangeSucc. auto.
    - destruct H. subst. destruct (fin2nat i ??= 0)%nat.
      + rewrite vnth_vconsH_0; auto. destruct i; simpl in *. apply fin_eq_iff; auto.
      + erewrite vnth_vconsH_gt0; auto.
        Unshelve. rewrite fin2nat_fin2SuccRangeSucc. lia. lia.
  Qed.
  
  (** [x; a] <> 0 <-> x <> 0 \/ a <> 0 *)
  Lemma vconsH_neq0_iff : forall {n} x (a : @vec A n),
      vconsH x a <> vzero <-> x <> Azero \/ a <> vzero.
  Proof. intros. rewrite vconsH_eq0_iff. tauto. Qed.

  (** vconsH (vhead a) (vremoveH a) = a *)
  Lemma vconsH_vhead_vremoveH : forall {n} (a : @vec A (S n)),
      vconsH (vhead a) (vremoveH a) = a.
  Proof.
    intros. apply veq_iff_vnth; intros. destruct (fin2nat i ??= 0)%nat.
    - rewrite vnth_vconsH_0. 
      + unfold vhead. f_equal. destruct i; simpl in *; auto. apply fin_eq_iff; auto.
      + destruct i; simpl in *. apply fin_eq_iff; auto.
    - erewrite vnth_vconsH_gt0. rewrite vnth_vremoveH. f_equal.
      rewrite fin2SuccRangeSucc_fin2PredRangePred. auto.
      Unshelve. lia.
  Qed.

  (** vremoveH (vconsH a x) = a *)
  Lemma vremoveH_vconsH : forall {n} x (a : @vec A n), vremoveH (vconsH x a) = a.
  Proof.
    intros. apply veq_iff_vnth; intros i. rewrite vnth_vremoveH.
    erewrite vnth_vconsH_gt0. f_equal. apply fin2PredRangePred_fin2SuccRangeSucc.
    Unshelve. rewrite fin2nat_fin2SuccRangeSucc. lia.
  Qed.
  
  (** vhead (vconsH a x) = x *)
  Lemma vhead_vconsH : forall {n} (a : @vec A n) x, vhead (vconsH x a) = x.
  Proof. intros. unfold vhead. rewrite vnth_vconsH_0; auto. Qed.

  (** [0; vzero] = vzero *)
  Lemma vconsH_0_vzero : forall {n}, @vconsH n Azero vzero = vzero.
  Proof. intros. unfold vconsH. apply veq_iff_vnth; intros. fin. Qed.
  
  
  (** *** vconsT *)

  (** cons at tail: [a; x] *)
  Definition vconsT {n} (a : @vec A n) (x : A) : @vec A (S n).
    intros i. destruct (fin2nat i ??< n)%nat as [E|E].
    - apply (a.[fin2PredRange i E]).
    - apply x.
  Defined.
  
  (** i = n -> (v2f [a; x]) i = a *)
  Lemma vconsT_spec_n : forall {n} x (a : @vec A n) (i : nat),
      i = n -> v2f (vconsT a x) i = x.
  Proof. intros. subst. unfold vconsT,v2f; simpl. fin. Qed.

  (** i < n -> (v2f [a; x]) i = a.(pred i) *)
  Lemma vconsT_spec_lt : forall {n} x (a : @vec A n) (i : nat),
      i < n -> v2f (vconsT a x) i = v2f a i.
  Proof. intros. unfold vconsT,v2f; simpl. fin. Qed.

  (** i = n -> [a; x].i = a *)
  Lemma vnth_vconsT_n : forall {n} x (a : @vec A n) i,
      fin2nat i = n -> (vconsT a x).[i] = x.
  Proof. intros. unfold vconsT. fin. Qed.

  (** i < n -> [a; x].i = a.(pred i) *)
  Lemma vnth_vconsT_lt : forall {n} x (a : @vec A n) i (H: fin2nat i < n),
      (vconsT a x).[i] = a (fin2PredRange i H).
  Proof. intros. unfold vconsT. fin. Qed.

  (** [a; x] = 0 <-> a = 0 /\ x = 0*)
  Lemma vconsT_eq0_iff : forall {n} (a : @vec A n) x,
      vconsT a x = vzero <-> a = vzero /\ x = Azero.
  Proof.
    intros. rewrite !veq_iff_vnth. split; intros.
    - split; intros; auto.
      + specialize (H (fin2SuccRange i)). rewrite vnth_vzero in *. rewrite <- H.
        erewrite vnth_vconsT_lt. f_equal.
        rewrite fin2PredRange_fin2SuccRange. auto.
      + specialize (H (nat2finS n)). rewrite vnth_vconsT_n in H; auto.
        rewrite fin2nat_nat2finS; auto.
    - pose proof (fin2nat_lt i).
      destruct H. subst. destruct (fin2nat i ??= n)%nat.
      + rewrite vnth_vconsT_n; auto.
      + erewrite vnth_vconsT_lt; auto.
        Unshelve. all: try lia. rewrite fin2nat_fin2SuccRange. apply fin2nat_lt.
  Qed.
  
  (** [a; x] <> 0 <-> a <> 0 \/ x <> 0*)
  Lemma vconsT_neq0_iff : forall {n} (a : @vec A n) x,
      vconsT a x <> vzero <-> a <> vzero \/ x <> Azero.
  Proof.
    intros. rewrite vconsT_eq0_iff. split; intros.
    apply not_and_or in H; auto. apply or_not_and; auto.
  Qed.

  (** vconsT (vremoveT a) (vtail a) = a *)
  Lemma vconsT_vremoveT_vtail : forall {n} (a : @vec A (S n)),
      vconsT (vremoveT a) (vtail a) = a.
  Proof.
    intros. apply veq_iff_vnth; intros. destruct (fin2nat i ??= n)%nat.
    - destruct i as [i Hi]. simpl in *. subst. rewrite vnth_vconsT_n; auto.
      rewrite vtail_eq. f_equal. erewrite nat2finS_eq. apply fin_eq_iff; auto.
    - erewrite vnth_vconsT_lt. rewrite vnth_vremoveT. f_equal.
      rewrite fin2SuccRange_fin2PredRange. auto.
      Unshelve. all: try lia. pose proof (fin2nat_lt i). lia.
  Qed.

  (** vremoveT (vconsT a x) = a *)
  Lemma vremoveT_vconsT : forall {n} (a : @vec A n) x, vremoveT (vconsT a x) = a.
  Proof.
    intros. apply veq_iff_vnth; intros i. rewrite vnth_vremoveT.
    erewrite vnth_vconsT_lt. f_equal. apply fin2PredRange_fin2SuccRange.
    Unshelve. rewrite fin2nat_fin2SuccRange. apply fin2nat_lt.
  Qed.
  
  (** vtail (vconsT a x) = x *)
  Lemma vtail_vconsT : forall {n} (a : @vec A n) x, vtail (vconsT a x) = x.
  Proof.
    intros. unfold vtail. rewrite vnth_vconsT_n; auto.
    rewrite fin2nat_nat2finS; auto.
  Qed.

  (** [vzero; 0] = vzero *)
  Lemma vconsT_vzero_eq0 : forall {n}, @vconsT n vzero Azero = vzero.
  Proof.
    intros. unfold vconsT. apply veq_iff_vnth; intros. fin.
  Qed.

  (** vmap2 f (vconsT a x) (vconsT b y) = vconsT (vmap2 f a b) (f x y) *)
  Lemma vmap2_vconsT_vconsT : forall {n} (a b : @vec A n) (x y : A) (f : A -> A -> A),
      vmap2 f (vconsT a x) (vconsT b y) = vconsT (vmap2 f a b) (f x y).
  Proof.
    intros. apply veq_iff_vnth; intros. rewrite vnth_vmap2.
    unfold vconsT. fin.
  Qed.
  
End vconsH_vconsT.


(* ======================================================================= *)
(** ** Construct vector with two vectors *)
Section vapp.
  Context {A} {Azero : A}.
  Notation vzero := (vzero Azero).

  (** Append two vectors, denoted with a@b *)
  Definition vapp {m n} (a : @vec A m) (b : @vec A n) : @vec A (m + n).
    intros i. destruct (fin2nat i ??< m)%nat as [E|E].
    - exact (a.[fin2AddRangeR' i E]).
    - assert (m <= fin2nat i). apply Nat.nlt_ge; auto.
      exact (b.[fin2AddRangeAddL' i H]).
  Defined.
  
  (** i < m -> a@b.i = u.i *)
  Lemma vapp_spec_L : forall {m n} (a : @vec A m) (b : @vec A n) (i : nat),
      i < m -> v2f Azero (vapp a b) i = v2f Azero a i.
  Proof.
    intros. unfold vapp.
    assert (i < m + n). lia.
    rewrite nth_v2f with (H:=H0). rewrite nth_v2f with (H:=H). fin.
  Qed.
  
  (** m <= i -> i < m + n -> a&b.i = a.(i - m) *)
  Lemma vapp_spec_R : forall {m n} (a : @vec A m) (b : @vec A n) (i : nat),
      m <= i -> i < m + n -> v2f Azero (vapp a b) i = v2f Azero b (i - m).
  Proof.
    intros. unfold vapp.
    rewrite nth_v2f with (H:=H0). simpl. fin.
    assert (i - m < n). lia. rewrite nth_v2f with (H:=H1). f_equal.
    apply fin_eq_iff; auto.
  Qed.
  
  (** i < m -> a&b.i = a.i *)
  Lemma vnth_vapp_L : forall {m n} (a : @vec A m) (b : @vec A n) i (H: fin2nat i < m),
      (vapp a b).[i] = a.[fin2AddRangeR' i H].
  Proof.
    intros. destruct i as [i Hi]. unfold vapp. simpl. fin.
  Qed.
  
  (** m <= i -> a&b.i = b.i *)
  Lemma vnth_vapp_R : forall {m n} (a : @vec A m) (b : @vec A n) i (H : m <= fin2nat i),
      (vapp a b).[i] = b.[fin2AddRangeAddL' i H].
  Proof.
    intros. destruct i as [i Hi]. unfold vapp. simpl in *. fin.
  Qed.

  (** a@b = 0 <-> a = 0 /\ b = 0 *)
  Lemma vapp_eq0_iff : forall {m n} (a : @vec A m) (b : @vec A n),
      vapp a b = vzero <-> a = vzero /\ b = vzero.
  Proof.
    intros. rewrite !veq_iff_vnth. split; intros.
    - split; intros.
      + specialize (H (fin2AddRangeR i)).
        erewrite vnth_vapp_L in H. rewrite fin2AddRangeR'_fin2AddRangeR in H.
        rewrite H. cbv. auto.
      + specialize (H (fin2AddRangeAddL i)).
        erewrite vnth_vapp_R in H. erewrite fin2AddRangeAddL'_fin2AddRangeAddL in H.
        rewrite H. cbv. auto.
    - destruct H. destruct (fin2nat i ??< m)%nat as [E|E].
      + rewrite vnth_vapp_L with (H:=E). rewrite H. cbv. auto.
      + erewrite vnth_vapp_R. rewrite H0. cbv. auto.
        Unshelve. all: try lia.
        * rewrite fin2nat_fin2AddRangeR. apply fin2nat_lt.
        * rewrite fin2nat_fin2AddRangeAddL. lia.
  Qed.
  
  (** vapp (vheadN a) (vtailN a) = a *)
  Lemma vapp_vheadN_vtailN : forall {m n} (a : @vec A (m + n)),
      vapp (vheadN a) (vtailN a) = a.
  Proof.
    intros. apply veq_iff_vnth; intros.
    destruct (fin2nat i ??< m)%nat as [E|E].
    - erewrite vnth_vapp_L. rewrite vnth_vheadN.
      rewrite fin2AddRangeR_fin2AddRangeR'. auto.
    - erewrite vnth_vapp_R. rewrite vnth_vtailN.
      rewrite fin2AddRangeAddL_fin2AddRangeAddL'. auto.
      Unshelve. auto. lia.
  Qed.

End vapp.

Section vapp_extra.
  Context {A B C : Type}.

  (* map2 a@b c@d = (map2 a c) @ (map2 b d) *)
  Lemma vmap2_vapp_vapp :
    forall {n m} (f : A -> B -> C)
           (a : @vec A n) (b : @vec A m) (c : @vec B n) (d : @vec B m),
      vmap2 f (vapp a b) (vapp c d) = vapp (vmap2 f a c) (vmap2 f b d).
  Proof.
    intros. unfold vmap2. apply veq_iff_vnth. intros.
    destruct (fin2nat i ??< n)%nat.
    - erewrite !vnth_vapp_L. auto.
    - erewrite !vnth_vapp_R. auto.
      Unshelve. auto. lia.
  Qed.

End vapp_extra.


(* ======================================================================= *)
(** ** Construct vector from parts of a vector *)
Section vslice.
  Context {A} {Azero : A}.

  (** {i<n}, {j<n}, {k:=S j-i} -> {i+k < n} *)
  Definition vslice_idx {n} (i j : fin n)
    (k : fin (S (fin2nat j) - (fin2nat i))) : fin n.
    refine (nat2fin (fin2nat i + fin2nat k) _).
    pose proof (fin2nat_lt k). pose proof (fin2nat_lt j).
    apply nat_lt_sub_imply_lt_add in H. rewrite commutative.
    apply nat_ltS_lt_lt with (b := fin2nat j); auto.
  Defined.
  
  (** Get a slice from vector `v` which contain elements from v$i to v$j.
      1. Include the i-th and j-th element
      2. If i > i, then the result is `vec 0` *)
  Definition vslice {n} (a : @vec A n) (i j : fin n) :
    @vec A (S (fin2nat j) - (fin2nat i)) :=
    fun k => a.[vslice_idx i j k].

  Lemma vnth_vslice : forall {n} (a : @vec A n) (i j : fin n) k,
      (vslice a i j).[k] = a.[vslice_idx i j k].
  Proof. intros. auto. Qed.
  
End vslice.

Section test.
  Let n := 5.
  Let a : vec n := l2v 9 [1;2;3;4;5].
  (* Compute v2l (vslice a (nat2finS 1) (nat2finS 3)). *)
End test.




(* ======================================================================= *)
(** ** A proposition which all elements of the vector hold *)
Section vforall.
  Context {A : Type}.

  (** Every element of `a` satisfy the `P` *)
  Definition vforall {n} (a : @vec A n) (P : A -> Prop) : Prop := forall i, P (a.[i]).
  
End vforall.


(* ======================================================================= *)
(** ** A proposition which at least one element of the vector holds *)
Section vexist.
  Context {A : Type}.

  (** There exist element of `v` satisfy the `P` *)
  Definition vexist {n} (a : @vec A n) (P : A -> Prop) : Prop := exists i, P (a.[i]).
  
End vexist.


(* ======================================================================= *)
(** ** An element belongs to the vector *)
Section vmem.
  Context {A : Type}.

  (** Element `x` belongs to the vector `a` *)
  Definition vmem {n} (a : @vec A n) (x : A) : Prop := vexist a (fun x0 => x0 = x).

  Lemma vmem_vnth : forall {n} (a : @vec A n) (i : fin n), vmem a (a.[i]).
  Proof. intros. hnf. exists i; auto. Qed.

  (* If we have AeqDec *)
  Section AeqDec.
    Context {AeqDec : Dec (@eq A)}.
    
    (** {x ∈ a} + {x ∉ a} *)
    Lemma vmem_dec : forall {n} (a : @vec A n) (x : A), {vmem a x} + {~vmem a x}.
    Proof.
      intros. unfold vmem, vexist. induction n.
      - right. intro. destruct H. apply fin0_False; auto.
      - rewrite <- (vconsH_vhead_vremoveH a).
        destruct (Aeqdec (vhead a) x) as [H|H].
        + left. exists fin0. rewrite vnth_vconsH_0; auto.
        + destruct (IHn (vremoveH a)) as [H1|H1].
          * left. destruct H1 as [i H1]. exists (fin2SuccRangeSucc i).
            erewrite vnth_vconsH_gt0.
            rewrite fin2PredRangePred_fin2SuccRangeSucc. auto.
          * right. intro. destruct H1. destruct H0 as [i H0].
            destruct (fin2nat i ??= 0)%nat.
            ** rewrite vnth_vconsH_0 in H0; auto; try easy.
               destruct i; simpl in *; apply fin_eq_iff; auto.
            ** erewrite vnth_vconsH_gt0 in H0.
               eexists (fin2PredRangePred i _). apply H0.
               Unshelve. all: try lia. rewrite fin2nat_fin2SuccRangeSucc. lia.
    Qed.
    
  End AeqDec.
  
End vmem.


(* ======================================================================= *)
(** ** An vector belongs to another vector *)
Section vmems.
  Context {A : Type}.

  (** Every element of vector `a` belongs to vector `b` *)
  Definition vmems {r s} (a : @vec A r) (b : @vec A s) : Prop :=
    vforall a (fun x => vmem b x).

  Lemma vmems_refl : forall {n} (a : @vec A n), vmems a a.
  Proof. intros. unfold vmems, vforall. apply vmem_vnth. Qed.

  Lemma vmems_trans : forall {r s t} (a : @vec A r) (b : @vec A s) (c : @vec A t),
      vmems a b -> vmems b c -> vmems a c.
  Proof.
    intros. unfold vmems, vforall in *. intros.
    specialize (H i). destruct H as [j H]. rewrite <- H. auto.
  Qed.

  (* If we have AeqDec *)
  Section AeqDec.
    Context {AeqDec : Dec (@eq A)}.

    (** {a ⊆ b} + {~(a ⊆ b)} *)
    Lemma vmems_dec : forall {r s} (a : @vec A r) (b : @vec A s),
        {vmems a b} + {~vmems a b}.
    Proof.
      intros. unfold vmems, vforall. induction r.
      - left. intro. exfalso. apply fin0_False; auto.
      - rewrite <- (vconsH_vhead_vremoveH a).
        specialize (IHr (vremoveH a)). destruct IHr as [H|H].
        + destruct (vmem_dec b (vhead a)) as [H1|H1].
          * left. intros. destruct (fin2nat i ??= 0)%nat.
            ** rewrite vnth_vconsH_0; auto.
               destruct i; simpl in *; apply fin_eq_iff; auto.
            ** erewrite vnth_vconsH_gt0; auto.
          * right. apply ex_not_not_all. exists fin0. rewrite vnth_vconsH_0; auto.
        + right. intro. destruct H. intro.
          specialize (H0 (fin2SuccRangeSucc i)).
          assert (0 < fin2nat (fin2SuccRangeSucc i)).
          apply fin2nat_fin2SuccRangeSucc_gt0.
          rewrite vnth_vconsH_gt0 with (H:=H) in H0.
          rewrite fin2PredRangePred_fin2SuccRangeSucc in H0. auto.
          Unshelve. lia.
    Qed.
    
  End AeqDec.
  
End vmems.


(* ======================================================================= *)
(** ** Two vectors are equivalent (i.e., contain each other) *)
Section vequiv.
  Context {A : Type}.

  (** Two vectors are equivalent (i.e., contain each other) *)
  Definition vequiv {r s} (a : @vec A r) (b : @vec A s) : Prop :=
    vmems a b /\ vmems b a.

  Lemma vequiv_refl : forall {n} (a : @vec A n), vequiv a a.
  Proof. intros. unfold vequiv. split; apply vmems_refl. Qed.
  
  Lemma vequiv_syms : forall {r s} (a : @vec A r) (b : @vec A s), vequiv a b -> vequiv b a.
  Proof. intros. unfold vequiv in *. tauto. Qed.
  
  Lemma vequiv_trans : forall {r s t} (a : @vec A r) (b : @vec A s) (c : @vec A t),
      vequiv a b -> vequiv b c -> vequiv a c.
  Proof.
    intros. unfold vequiv in *. destruct H as [H1 H2], H0 as [H3 H4]. split.
    apply vmems_trans with b; auto.
    apply vmems_trans with b; auto.
  Qed.

  (* If we have AeqDec *)
  Section AeqDec.
    Context {AeqDec : Dec (@eq A)}.

    (** {a ∼ b} + {~(a ∼ b)} *)
    Lemma vequiv_dec : forall {r s} (a : @vec A r) (b : @vec A s),
        {vequiv a b} + {~ vequiv a b}.
    Proof.
      intros. unfold vequiv. destruct (vmems_dec a b), (vmems_dec b a); try tauto.
    Qed.
  End AeqDec.
  
End vequiv.

Section test.

  Let a : vec 2 := l2v 9 [1;2].
  Let b : vec 3 := l2v 9 [1;2;1].
  Example vequiv_example1 : vequiv a b.
  Proof.
    unfold a, b, vequiv, vmems, vmem, vforall, vexist. split.
    - intros. destruct i as [i Hi].
      repeat (destruct i; try lia); try rewrite vnth_l2v; simpl.
      exists (nat2finS 0); auto.
      exists (nat2finS 1); auto.
    - intros. destruct i as [i Hi].
      repeat (destruct i; try lia); try rewrite vnth_l2v; simpl.
      exists (nat2finS 0); auto.
      exists (nat2finS 1); auto.
      exists (nat2finS 0); auto.
  Qed.
End test.


(* (* ======================================================================= *) *)
(* (** ** An vector belongs to one but not belong to another *) *)
(* Section vdiff. *)
(*   Context {A : Type}. *)

(*   (** Elements belong to vector `u` but not belongs to vector `v` *) *)
(*   Definition vdiff {r s} (a : @vec A r) (b : @vec A s) : Prop. *)
(*     Check fun i => vmem  *)
(*     vforall a (fun x => vmem b x). *)

(* End vmems. *)



(* ======================================================================= *)
(** ** Folding of a vector *)
Section vfold.
  Context {A B : Type} {Azero : A} {Bzero : B}. 

  (** ((x + a.1) + a.2) + ... *)
  Definition vfoldl {n} (a : @vec A n) (x : B) (f : B -> A -> B) : B :=
    seqfoldl (v2f Azero a) n x f.
  
  (** ... + (v.(n-1) + (v.n + x)) *)
  Definition vfoldr {n} (a : @vec A n) (x : B) (f : A -> B -> B) : B :=
    seqfoldr (v2f Azero a) n x f.

  (** Convert `vfoldl` to `seqfoldl` *)
  Lemma vfoldl_eq_seqfoldl :
    forall {n} (a : @vec A n) (x : B) (f : B -> A -> B) (s : nat -> A),
      (forall i, a.[i] = s (fin2nat i)) -> vfoldl a x f = seqfoldl s n x f.
  Proof.
    intros. unfold vfoldl. apply seqfoldl_eq; auto.
    intros. rewrite nth_v2f with (H:=H0). rewrite H.
    rewrite fin2nat_nat2fin. auto.
  Qed.
  
End vfold.

(* ======================================================================= *)
(** ** Sum of a vector *)
Section vsum.
  Context `{HAMonoid : AMonoid}.
  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero : A_scope.
  Notation seqsum := (@seqsum _ Aadd 0).

  (** ∑a = a.0 + a.1 + ... + a.(n-1) *)
  Definition vsum {n} (a : @vec A n) := seqsum n (v2f 0 a).

  (** (∀ i, a.i = b.i) -> Σa = Σb *)
  Lemma vsum_eq : forall {n} (a b : @vec A n), (forall i, a.[i] = b.[i]) -> vsum a = vsum b.
  Proof.
    intros. unfold vsum. apply seqsum_eq; intros.
    rewrite !nth_v2f with (H:=H0). apply H.
  Qed.

  (** (∀ i, a.i = 0) -> Σa = 0 *)
  Lemma vsum_eq0 : forall {n} (a : @vec A n), (forall i, a.[i] = 0) -> vsum a = 0.
  Proof.
    intros. unfold vsum. apply seqsum_eq0; intros.
    rewrite !nth_v2f with (H:=H0). apply H.
  Qed.

  (** Convert `vsum` to `seqsum` *)
  Lemma vsum_eq_seqsum : forall {n} (a : @vec A n),
      vsum a = seqsum n (fun i => v2f 0 a i).
  Proof.
    intros. unfold vsum. apply seqsum_eq; intros. auto.
  Qed.
  
  (* (** Convert `vsum` to `seqsum` (succ form) *) *)
  (* Lemma vsum_eq_seqsum_succ : forall {n} (a : @vec A (S n)), *)
  (*     vsum a = seqsum n (fun i => a.[nat2finS i]) + a.[nat2finS n]. *)
  (* Proof. intros. apply fseqsum_eq_seqsum_succ. Qed. *)
  
  (** `vsum` of (S n) elements, equal to addition of Sum and tail *)
  Lemma vsumS_tail : forall {n} (a : @vec A (S n)),
      vsum a = vsum (fun i => a.[fin2SuccRange i]) + a.[nat2finS n].
  Proof.
    intros. unfold vsum. rewrite seqsumS_tail. f_equal.
    - apply seqsum_eq; intros. erewrite !nth_v2f. f_equal.
      erewrite fin2SuccRange_nat2fin. auto.
    - erewrite nth_v2f. erewrite nat2finS_eq. auto.
      Unshelve. all: try lia.
  Qed.

  (** `vsum` of (S n) elements, equal to addition of head and Sum *)
  Lemma vsumS_head : forall {n} (a : @vec A (S n)),
      vsum a = a.[nat2finS 0] + vsum (fun i => a.[fin2SuccRangeSucc i]).
  Proof.
    intros. unfold vsum. rewrite seqsumS_head; auto. f_equal.
    apply seqsum_eq; intros. erewrite !nth_v2f. f_equal.
    erewrite fin2SuccRangeSucc_nat2fin. auto.
    Unshelve. lia. auto.
  Qed.

  (** Σa + Σb = Σ(fun i => a.[i] + b.[i]) *)
  Lemma vsum_add : forall {n} (a b : @vec A n),
      vsum a + vsum b = vsum (fun i => a.[i] + b.[i]).
  Proof.
    intros. unfold vsum. rewrite seqsum_add. apply seqsum_eq; intros.
    rewrite !nth_v2f with (H:=H). auto.
  Qed.
  
  (** `vsum` which only one item is nonzero, then got this item. *)
  Lemma vsum_unique : forall {n} (a : @vec A n) (x : A) i,
      a.[i] = x -> (forall j, i <> j -> a.[j] = Azero) -> vsum a = x.
  Proof.
    intros. unfold vsum. apply seqsum_unique with (i:=fin2nat i); auto; fin.
    - rewrite <- H. rewrite nth_v2f with (H:=fin2nat_lt _); fin.
    - intros. unfold v2f. fin.
      specialize (H0 (nat2fin j E)). rewrite <- H0; auto.
      intro; destruct H2; subst. fin.
  Qed.

  (** `vsum` of the m+n elements equal to plus of two parts.
      Σ[0,(m+n)] a = Σ[0,m](fun i=>a[i]) + Σ[m,m+n] (fun i=>a[m+i]) *)
  Lemma vsum_plusIdx : forall m n (a : @vec A (m + n)),
      vsum a = vsum (fun i => a.[fin2AddRangeR i]) +
                 vsum (fun i => a.[fin2AddRangeAddL i]).
  Proof.
    intros. unfold vsum. rewrite seqsum_plusIdx. f_equal.
    - apply seqsum_eq; intros. erewrite !nth_v2f. f_equal. apply fin_eq_iff; auto.
    - apply seqsum_eq; intros. erewrite !nth_v2f. f_equal. apply fin_eq_iff; auto.
      Unshelve. all: try lia.
  Qed.

  (** `vsum` of the m+n elements equal to plus of two parts.
      (i < m -> a.i = b.i) ->
      (i < n -> a.(m+i) = c.i) ->
      Σ[0,(m+n)] a = Σ[0,m] b + Σ[m,m+n] c. *)
  Lemma vsum_plusIdx_ext : forall m n (a : @vec A (m + n)) (b : @vec A m) (c : @vec A n),
      (forall i : fin m, a.[fin2AddRangeR i] = b.[i]) ->
      (forall i : fin n, a.[fin2AddRangeAddL i] = c.[i]) ->
      vsum a = vsum b + vsum c.
  Proof.
    intros. unfold vsum. rewrite seqsum_plusIdx. f_equal.
    - apply seqsum_eq; intros. erewrite !nth_v2f. rewrite <- H. f_equal.
      apply fin_eq_iff; auto.
    - apply seqsum_eq; intros. erewrite !nth_v2f. rewrite <- H0. f_equal.
      apply fin_eq_iff; auto.
      Unshelve. all: try lia.
  Qed.

  (** The order of two nested summations can be exchanged.
      ∑[i,0,r](∑[j,0,c] a.ij) = 
      a00 + a01 + ... + a0c + 
      a10 + a11 + ... + a1c + 
      ...
      ar0 + ar1 + ... + arc = 
      ∑[j,0,c](∑[i,0,r] a.ij) *)
  Lemma vsum_vsum : forall r c (a : @vec (@vec A c) r),
      vsum (fun i => vsum (fun j => a.[i].[j])) =
        vsum (fun j => vsum (fun i => a.[i].[j])).
  Proof.
    intros. unfold vsum. destruct r,c; auto.
    - rewrite seqsumS_tail. simpl. rewrite seqsum_eq0; auto.
      * amonoid. unfold v2f. fin.
      * intros. unfold v2f. fin.
    - rewrite seqsumS_tail. simpl. rewrite seqsum_eq0; auto.
      * amonoid. unfold v2f. fin.
      * intros. unfold v2f. fin.
    - pose proof (seqsum_seqsum (S r) (S c) (fun i j => a #i #j)).
      match goal with
      | H: ?a1 = ?b1 |- ?a2 = ?b2 => replace a2 with a1;[replace b2 with b1|]; auto
      end.
      + apply seqsum_eq; intros. rewrite nth_v2f with (H:=H0).
        apply seqsum_eq; intros. rewrite nth_v2f with (H:=H1).
        f_equal; apply nat2finS_eq; apply fin_eq_iff.
      + apply seqsum_eq; intros. rewrite nth_v2f with (H:=H0).
        apply seqsum_eq; intros. rewrite nth_v2f with (H:=H1).
        f_equal; apply nat2finS_eq; apply fin_eq_iff.
  Qed.

  (* ∑ (a@b) = ∑a + ∑b *)
  Lemma vsum_vapp : forall {m n} (a : @vec A m) (b : @vec A n),
      vsum (vapp a b) = vsum a + vsum b.
  Proof.
    intros. apply vsum_plusIdx_ext; intros.
    - erewrite vnth_vapp_L. f_equal. rewrite fin2AddRangeR'_fin2AddRangeR. auto.
    - erewrite vnth_vapp_R. f_equal.
      rewrite fin2AddRangeAddL'_fin2AddRangeAddL. auto.
      Unshelve. rewrite fin2nat_fin2AddRangeR. apply fin2nat_lt.
      rewrite fin2nat_fin2AddRangeAddL. lia.
  Qed.

  (** ∑ (vconsT a x) = ∑ a + x *)
  Lemma vsum_vconsT : forall {n} (a : @vec A n) (x : A),
      vsum (vconsT a x) = vsum a + x.
  Proof.
    intros. rewrite vsumS_tail. f_equal.
    - apply vsum_eq; intros. erewrite vnth_vconsT_lt. fin.
    - rewrite vnth_vconsT_n; auto. fin.
      Unshelve. fin.
  Qed.
  
  (* If equip a `AGroup` *)
  Section AGroup.
    Context `{HAGroup : AGroup A Aadd Azero Aopp}.
    Notation "- a" := (Aopp a) : A_scope.
    
    (** - Σa = Σ(fun i => -a.[i]) *)
    Lemma vsum_opp : forall {n} (a : @vec A n),
        - vsum a = vsum (fun i => - a.[i]).
    Proof.
      intros. unfold vsum. rewrite seqsum_opp; auto. apply seqsum_eq; intros.
      unfold v2f. fin.
    Qed.
  End AGroup.

  (* If equip a `ARing` *)
  Section ARing.
    Context `{HARing:ARing A Aadd Azero Aopp Amul Aone}.
    Infix "*" := (Amul) : A_scope.

    (** x * Σa = Σ(fun i -> x * a.[i]) *)
    Lemma vsum_cmul_l : forall {n} (a : @vec A n) x,
        x * vsum a = vsum (fun i => x * a.[i]).
    Proof.
      intros. unfold vsum. rewrite seqsum_cmul_l. apply seqsum_eq; intros.
      unfold v2f. fin.
    Qed.
    
    (** Σa * x = Σ(fun i -> a.[i] * x) *)
    Lemma vsum_cmul_r : forall {n} (a : @vec A n) x,
        vsum a * x = vsum (fun i => a.[i] * x).
    Proof.
      intros. unfold vsum. rewrite seqsum_cmul_r. apply seqsum_eq; intros.
      unfold v2f. fin.
    Qed.
  End ARing.

  (* if equip a `OrderedARing` *)
  Section OrderedARing.
    Context `{HOrderedARing
        : OrderedARing A Aadd Azero Aopp Amul Aone Alt Ale Altb Aleb}.
    (* Check HOrderedARing : Order Alt Ale Altb Aleb. *)
    Infix "*" := (Amul) : A_scope.
    Infix "<" := Alt.
    Infix "<=" := Ale.

    (** (∀ i, 0 <= a.i) -> a.i <= ∑a *)
    Lemma vsum_ge_any : forall {n} (a : @vec A n) i,
        (forall i, Azero <= a.[i]) -> a.[i] <= vsum a.
    Proof.
      intros. unfold vsum.
      replace (a i) with (v2f 0 a (fin2nat i)).
      - apply seqsum_ge_any; fin. intros. unfold v2f. fin.
      - erewrite nth_v2f. f_equal. rewrite nat2fin_fin2nat; auto.
        Unshelve. apply fin2nat_lt.
    Qed.

    (** (∀ i, 0 <= a.i) -> 0 <= ∑a *)
    Lemma vsum_ge0 : forall {n} (a : @vec A n), (forall i, Azero <= a.[i]) -> Azero <= vsum a.
    Proof.
      intros. pose proof (vsum_ge_any a). destruct n.
      - cbv. apply le_refl.
      - apply le_trans with (a.1); auto.
    Qed.
    
    (** (∀ i, 0 <= a.i) -> (∃ i, a.i <> 0) -> 0 < ∑a *)
    Lemma vsum_gt0 : forall {n} (a : @vec A n),
        (forall i, Azero <= a.[i]) -> (exists i, a.[i] <> Azero) -> Azero < vsum a.
    Proof.
      intros. destruct H0 as [i H0].
      pose proof (vsum_ge0 a H). pose proof (vsum_ge_any a i H).
      assert (Azero < a.[i]). apply lt_if_le_and_neq; auto.
      apply lt_trans_lt_le with (a.[i]); auto.
    Qed.
    
    (** (∀i, a.i >= 0) -> ∑a = 0 -> (∀i, a.i = 0) *)
    Lemma vsum_eq0_rev : forall {n} (a : @vec A n),
        (forall i, 0 <= a.[i]) -> vsum a = 0 -> (forall i, a.[i] = 0).
    Proof.
      intros. destruct (Aeqdec (a.[i]) 0); auto. exfalso.
      pose proof (vsum_ge_any a i H). rewrite H0 in H1.
      specialize (H i).
      pose proof (@le_antisym _ _ _ _ _ HOrderedARing (a i) 0 H1 H). easy.
    Qed.
    
  End OrderedARing.

End vsum.

Arguments vsum {A} Aadd Azero {n}.


(** vsum with vinsert and vremove  *)
Section vsum_vinsert_vremove.
  Context `{HAGroup : AGroup}.
  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + - b).
  Infix "-" := Asub : A_scope.
  Notation vsum := (@vsum _ Aadd Azero).
  Notation seqsum := (@seqsum _ Aadd Azero).
  Notation seqsum_plusIdx := (@seqsum_plusIdx _ Aadd Azero).

  (** ∑(insert a i x) = ∑a + x *)
  Lemma vsum_vinsert : forall {n} (a : @vec A n) (x : A) (i : fin (S n)),
      vsum (vinsert a i x) = vsum a + x.
  Proof.
    intros. pose proof (fin2nat_lt i).
    rewrite (vinsert_eq_vinsert' _ (Azero:=Azero)).
    unfold vinsert'. unfold vsum.
    replace (S n) with (fin2nat i + (S (n - fin2nat i)))%nat at 1 by lia.
    replace n with (fin2nat i + (n - fin2nat i))%nat at 6 by lia.
    rewrite !seqsum_plusIdx. rewrite seqsumS_head.
    match goal with
    | |- ?a+(?b+?c) = _ => replace (a+(b+c)) with (a+c+b) by agroup end. f_equal.
    - f_equal.
      + apply seqsum_eq; intros. unfold v2f,f2v. fin.
      + apply seqsum_eq; intros. unfold v2f,f2v. fin.
    - unfold v2f,f2v. fin.
  Qed.

  (** ∑(remove a i) = ∑a - a.i *)
  Lemma vsum_vremove : forall {n} (a : @vec A (S n)) (i : fin (S n)),
      vsum (vremove a i) = vsum a - a.[i].
  Proof.
    intros. pose proof (fin2nat_lt i).
    rewrite (vremove_eq_vremove' (Azero:=Azero)).
    unfold vremove'. unfold vsum.
    replace n with (fin2nat i + (n - fin2nat i))%nat at 1 by lia.
    replace (S n) with (fin2nat i + (S (n - fin2nat i)))%nat at 3 by lia.
    rewrite !seqsum_plusIdx. rewrite seqsumS_head.
    match goal with
    | |- _ = ?d+(?e+?f)-?g => replace (d+(e+f)-g) with (d+f) end.
    - f_equal.
      + apply seqsum_eq; intros. unfold v2f,f2v. fin.
      + apply seqsum_eq; intros. unfold v2f,f2v. fin.
    - agroup. unfold v2f.
      replace (fin2nat i + 0)%nat with (fin2nat i) by lia. fin. agroup.
  Qed.
  
End vsum_vinsert_vremove.

(** Extension for `vsum` *)
Section vsum_ext.
  
  Context `{HAMonoidA : AMonoid}.
  Context `{HAMonoidB : AMonoid B Badd Bzero}.
  Context (cmul : A -> B -> B).
  Infix "+A" := Aadd (at level 50).
  Infix "+B" := Badd (at level 50).
  Infix "*" := cmul.
  Notation vsumA := (@vsum _ Aadd Azero).
  Notation vsumB := (@vsum _ Badd Bzero).
  
  (** ∑(x*ai) = x * a1 + ... + x * ai = x * (a1 + ... + ai) = x * ∑(ai) *)
  Section form1.
    Context (cmul_zero_keep : forall x : A, x * Bzero = Bzero).
    Context (cmul_badd : forall (x : A) (y1 y2 : B), x * (y1 +B y2) = (x * y1) +B (x * y2)).
    
    Lemma vsum_cmul_l_ext : forall {n} (x : A) (a : @vec B n),
        x * vsumB a = vsumB (fun i => x * a.[i]).
    Proof.
      intros. unfold vsumB. rewrite seqsum_cmul_l_ext; auto.
      apply seqsum_eq; intros. rewrite !nth_v2f with (H:=H). auto.
    Qed.
  End form1.
  
  (** ∑(ai*x) = a1 * x + ... + ai * x = (a1 + ... + ai) * b = ∑(ai) * x *)
  Section form2.
    Context (cmul_zero_keep : forall x : B, Azero * x = Bzero).
    Context (cmul_aadd : forall (x1 x2 : A) (y : B), (x1 +A x2) * y = (x1 * y) +B (x2 * y)).

    Lemma vsum_cmul_r_ext : forall {n} (x : B) (a : @vec A n),
        vsumA a * x = vsumB (fun i => a.[i] * x).
    Proof.
      intros. unfold vsumB. rewrite seqsum_cmul_r_ext; auto.
      apply seqsum_eq; intros. rewrite !nth_v2f with (H:=H). auto.
    Qed.
  End form2.
  
End vsum_ext.


(* ======================================================================= *)
(** ** Vector addition *)
Section vadd.
  Context `{AMonoid}.
  Infix "+" := Aadd : A_scope.
  
  Notation vec := (@vec A).
  Notation vzero := (vzero Azero).

  Definition vadd {n} (a b : vec n) : vec n := vmap2 Aadd a b.
  Infix "+" := vadd : vec_scope.

  (** (a + b) + c = a + (b + c) *)
  Lemma vadd_assoc : forall {n} (a b c : vec n), (a + b) + c = a + (b + c).
  Proof. intros. apply vmap2_assoc. Qed.

  (** a + b = b + a *)
  Lemma vadd_comm : forall {n} (a b : vec n), a + b = b + a.
  Proof. intros. apply vmap2_comm. Qed.

  (** 0 + a = a *)
  Lemma vadd_0_l : forall {n} (a : vec n), vzero + a = a.
  Proof.
    intros. apply veq_iff_vnth; intros. unfold vadd. rewrite vnth_vmap2.
    rewrite vnth_vzero. amonoid.
  Qed.

  (** a + 0 = a *)
  Lemma vadd_0_r : forall {n} (a : vec n), a + vzero = a.
  Proof. intros. rewrite vadd_comm. apply vadd_0_l. Qed.

  (** <vadd,vzero> is an abelian monoid *)
  #[export] Instance vadd_AMonoid : forall n, AMonoid (@vadd n) vzero.
  Proof.
    intros. repeat constructor; intros;
      try apply vadd_assoc;
      try apply vadd_comm;
      try apply vadd_0_l;
      try apply vadd_0_r.
  Qed.

  (** (a + b).i = a.i + b.i *)
  Lemma vnth_vadd : forall {n} (a b : vec n) i, (a + b).[i] = (a.[i] + b.[i])%A.
  Proof. intros. unfold vadd. rewrite vnth_vmap2. auto. Qed.
  
  (** (a + b) + c = (a + c) + b *)
  Lemma vadd_perm : forall {n} (a b c : vec n), (a + b) + c = (a + c) + b.
  Proof. intros. rewrite !associative. f_equal. apply commutative. Qed.

End vadd.

Section vadd_extra.
  Context `{AMonoid}.

  (* 所有向量相加后取第j个分量 = 取出向量的第j个分量后再相加 *)
  (** (∑a).j = ∑(a.j), which a is a vector of vector *)
  Lemma vnth_vsum : forall {r c} (a : @vec (@vec A c) r) j,
      (@vsum _ (@vadd _ Aadd _) (vzero Azero) _ a).[j] =
        @vsum _ Aadd Azero _ (fun i => a.[i].[j]).
  Proof.
    induction r; intros; auto.
    rewrite !vsumS_tail. rewrite vnth_vadd. rewrite IHr. auto.
  Qed.
  
End vadd_extra.


(** ** Vector opposition *)
Section vopp.
  
  (* Let's have an Abelian-Group *)
  Context `{AGroup A Aadd Azero}.
  Notation "- a" := (Aopp a) : A_scope.
  
  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Infix "+" := vadd : vec_scope.

  Definition vopp {n} (a : vec n) : vec n := vmap Aopp a.
  Notation "- a" := (vopp a) : vec_scope.

  (** (- a).i = - (a.i) *)
  Lemma vnth_vopp : forall {n} (a : vec n) i, (- a).[i] = (- (a.[i]))%A.
  Proof. intros. cbv. auto. Qed.

  (** - a + a = 0 *)
  Lemma vadd_vopp_l : forall {n} (a : vec n), (- a) + a = vzero.
  Proof. intros. apply veq_iff_vnth; intros. cbv. agroup. Qed.
  
  (** a + - a = 0 *)
  Lemma vadd_vopp_r : forall {n} (a : vec n), a + (- a) = vzero.
  Proof. intros. apply veq_iff_vnth; intros. cbv. agroup. Qed.

  (** <vadd,vzero,vopp> is an abelian group *)
  #[export] Instance vadd_AGroup : forall n, @AGroup (vec n) vadd vzero vopp.
  Proof.
    intros. repeat constructor; intros;
      try apply vadd_AMonoid;
      try apply vadd_vopp_l;
      try apply vadd_vopp_r.
  Qed.

  (* Now, we ca use group theory on this instance *)

  (** - (- a) = a *)
  Lemma vopp_vopp : forall {n} (a : vec n), - (- a) = a.
  Proof. intros. apply group_opp_opp. Qed.

  (** a = - b <-> - a = b *)
  Lemma vopp_exchange : forall {n} (a b : vec n), a = - b <-> - a = b.
  Proof. intros. split; intros; subst; rewrite vopp_vopp; auto. Qed.

  (** - (vzero) = vzero *)
  Lemma vopp_vzero : forall {n:nat}, - (@Vector.vzero _ Azero n) = vzero.
  Proof. intros. apply group_opp_0. Qed.

  (** - a = vzero <-> a = vzero *)
  Lemma vopp_eq0_iff : forall {n} (a : vec n), - a = vzero <-> a = vzero.
  Proof.
    intros. split; intros; rewrite veq_iff_vnth in *; intros;
      specialize (H0 i); rewrite vnth_vzero, vnth_vopp in *.
    - apply group_opp_eq0_iff; auto.
    - apply group_opp_eq0_iff; auto.
  Qed.
  
  (** - (a + b) = (- a) + (- b) *)
  Lemma vopp_vadd : forall {n} (a b : vec n), - (a + b) = (- a) + (- b).
  Proof. intros. rewrite group_opp_distr. apply commutative. Qed.

End vopp.


(** ** Vector subtraction *)
Section vsub.

  (* Let's have an Abelian-Group *)
  Context `{AGroup A Aadd Azero}.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + (- b))%A.
  Infix "-" := Asub : A_scope.
  
  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Infix "+" := vadd : vec_scope.
  Notation "- a" := (vopp a) : vec_scope.

  Notation "a - b" := ((a + -b)%V) : vec_scope.
  (* Definition vsub {n} (a b : vec n) : vec n := a + (- b). *)
  (* Infix "-" := vsub : vec_scope. *)

  (** (a - b).i = a.i - b.i *)
  Lemma vnth_vsub : forall {n} (a b : vec n) i, (a - b).[i] = (a.[i] - b.[i])%A.
  Proof. intros. cbv. auto. Qed.

  (** a - b = - (b - a) *)
  Lemma vsub_comm : forall {n} (a b : vec n), a - b = - (b - a).
  Proof.
    intros. rewrite group_opp_distr. rewrite group_opp_opp. auto.
  Qed.

  (** (a - b) - c = a - (b + c) *)
  Lemma vsub_assoc : forall {n} (a b c : vec n), (a - b) - c = a - (b + c).
  Proof.
    intros. rewrite associative.
    f_equal. rewrite group_opp_distr. apply commutative.
  Qed.

  (** (a + b) - c = a + (b - c) *)
  Lemma vsub_assoc1 : forall {n} (a b c : vec n), (a + b) - c = a + (b - c).
  Proof. intros. pose proof (vadd_AGroup n). agroup. Qed.

  (** (a - b) - c = (a - c) - b *)
  Lemma vsub_assoc2 : forall {n} (a b c : vec n), (a - b) - c = (a - c) - b.
  Proof. intros. pose proof (vadd_AGroup n). agroup. Qed.
  
  (** 0 - a = - a *)
  Lemma vsub_0_l : forall {n} (a : vec n), vzero - a = - a.
  Proof. intros. pose proof (vadd_AGroup n). agroup. Qed.
  
  (** a - 0 = a *)
  Lemma vsub_0_r : forall {n} (a : vec n), a - vzero = a.
  Proof. intros. pose proof (vadd_AGroup n). agroup. Qed.
  
  (** a - a = 0 *)
  Lemma vsub_self : forall {n} (a : vec n), a - a = vzero.
  Proof. intros. pose proof (vadd_AGroup n). agroup. Qed.

  (** a - b = 0 <-> a = b *)
  Lemma vsub_eq0_iff_eq : forall {n} (a b : vec n), a - b = vzero <-> a = b.
  Proof. intros. apply group_sub_eq0_iff_eq. Qed.

End vsub.


(** ** Vector scalar multiplication *)
Section vcmul.
  
  (* Let's have an Abelian-ring *)
  Context `{HARing : ARing A Aadd Azero Aopp Amul Aone}.
  Add Ring ring_inst : (make_ring_theory HARing).
  
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + (- b))%A.
  Infix "-" := Asub : A_scope.

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Infix "+" := vadd : vec_scope.
  Notation "- a" := (vopp a) : vec_scope.
  Notation "a - b" := ((a + (-b))%V) : vec_scope.
  
  Definition vcmul {n : nat} (x : A) (a : vec n) : vec n := vmap (fun y => Amul x y) a.
  Infix "\.*" := vcmul : vec_scope.

  (** (x .* a).i = x * a.i *)
  Lemma vnth_vcmul : forall {n} (a : vec n) x i, (x \.* a).[i] = x * (a.[i]).
  Proof. intros. cbv. auto. Qed.

  (** x .* (y .* a) = (x * y) .* a *)
  Lemma vcmul_assoc : forall {n} (a : vec n) x y,
      x \.* (y \.* a) = (x * y)%A \.* a.
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.

  (** x .* (y .* a) = y .* (x .* a) *)
  Lemma vcmul_perm : forall {n} (a : vec n) x y,
      x \.* (y \.* a) = y \.* (x \.* a).
  Proof. intros. rewrite !vcmul_assoc. f_equal. ring. Qed.
  
  (** (x + y) .* a = (x .* a) + (y .* a) *)
  Lemma vcmul_add : forall {n} x y (a : vec n),
      (x + y)%A \.* a = (x \.* a) + (y \.* a).
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.

  (** x .* (a + b) = (x .* a) + (x .* b) *)
  Lemma vcmul_vadd : forall {n} x (a b : vec n),
      x \.* (a + b) = (x \.* a) + (x \.* b).
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.

  (** 0 .* a = vzero *)
  Lemma vcmul_0_l : forall {n} (a : vec n), Azero \.* a = vzero.
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.

  (** a .* vzero = vzero *)
  Lemma vcmul_0_r : forall {n} a, a \.* vzero = (@Vector.vzero _ Azero n).
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.
  
  (** 1 .* a = a *)
  Lemma vcmul_1_l : forall {n} (a : vec n), Aone \.* a = a.
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.
  
  (** - 1 .* a = - a *)
  Lemma vcmul_neg1_l : forall {n} (a : vec n), (- Aone)%A \.* a = - a.
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.
  
  (** (- x) .* a = - (x .* a) *)
  Lemma vcmul_opp : forall {n} x (a : vec n), (- x)%A \.* a = - (x \.* a).
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.

  (* Tips: this proof shows a proof by computation, due to the Fin-Function 
     model. *)
  (** x .* (- a) = - (x .* a) *)
  Lemma vcmul_vopp : forall {n} x (a : vec n), x \.* (- a) = - (x \.* a).
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.

  (* Tips: this proof shows a proof by derivation *)
  (** (- x) .* (- a) = x .* a *)
  Lemma vcmul_opp_vopp : forall {n} x (a : vec n), (- x)%A \.* (- a) = x \.* a.
  Proof. intros. rewrite vcmul_vopp, vcmul_opp. rewrite vopp_vopp. auto. Qed.

  (** x .* (a - b) = (x .* a) - (x .* b) *)
  Lemma vcmul_vsub : forall {n} x (a b : vec n), x \.* (a - b) = (x \.* a) - (x \.* b).
  Proof. intros. rewrite vcmul_vadd. rewrite vcmul_vopp. auto. Qed.

  (** <vadd,vzero,vopp> is an abelian group *)
  #[export] Instance vec_AGroup : forall n, @AGroup (vec n) vadd vzero vopp.
  Proof.
    intros. repeat constructor; intros;
      try apply vadd_AMonoid;
      try apply vadd_vopp_l;
      try apply vadd_vopp_r.
  Qed.
  
  (* If equip a `Dec` *)
  Section AeqDec.
    Context {AeqDec : Dec (@eq A)}.

    (** a <> 0 -> b <> 0 -> x .* a = b -> x <> 0 *)
    Lemma vcmul_eq_imply_x_neq0 : forall {n} x (a b : vec n),
        a <> vzero -> b <> vzero -> x \.* a = b -> x <> Azero.
    Proof.
      intros. destruct (Aeqdec x Azero); auto. exfalso. subst.
      rewrite vcmul_0_l in H0. easy.
    Qed.
  End AeqDec.

  (* If equip a `Dec` and a `Field` *)
  Section Dec_Field.
    Context {AeqDec : Dec (@eq A)}.
    Context `{HField : Field A Aadd Azero Aopp Amul Aone Ainv}.
    
    (** x .* a = 0 -> (x = 0) \/ (a = 0) *)
    Lemma vcmul_eq0_imply_x0_or_v0 : forall {n} x (a : vec n),
        x \.* a = vzero -> (x = Azero) \/ (a = vzero).
    Proof.
      intros. destruct (Aeqdec x Azero); auto. right.
      apply veq_iff_vnth; intros. rewrite veq_iff_vnth in H. specialize (H i).
      cbv in H. cbv. apply field_mul_eq0_iff in H; auto. tauto.
    Qed.

    (** x .* a = 0 -> a <> 0 -> x = 0 *)
    Corollary vcmul_eq0_imply_x0 : forall {n} x (a : vec n),
        x \.* a = vzero -> a <> vzero -> x = Azero.
    Proof. intros. apply (vcmul_eq0_imply_x0_or_v0 x a) in H; tauto. Qed.

    (** x .* a = 0 -> x <> 0 -> a = 0 *)
    Corollary vcmul_eq0_imply_v0 : forall {n} x (a : vec n),
        x \.* a = vzero -> x <> Azero -> a = vzero.
    Proof. intros. apply (vcmul_eq0_imply_x0_or_v0 x a) in H; tauto. Qed.

    (** x <> 0 -> a <> 0 -> x \.* a <> 0 *)
    Corollary vcmul_neq0_neq0_neq0 : forall {n} x (a : vec n),
        x <> Azero -> a <> vzero -> x \.* a <> vzero.
    Proof. intros. intro. apply vcmul_eq0_imply_x0_or_v0 in H1; tauto. Qed.
    
    (** x .* a = a -> x = 1 \/ a = 0 *)
    Lemma vcmul_same_imply_x1_or_v0 : forall {n} x (a : vec n),
        x \.* a = a -> (x = Aone) \/ (a = vzero).
    Proof.
      intros. destruct (Aeqdec x Aone); auto. right.
      apply veq_iff_vnth; intros. rewrite veq_iff_vnth in H. specialize (H i).
      cbv in H. cbv. apply field_mul_eq_imply_a1_or_b0 in H; auto. tauto.
    Qed.
    
    (** x = 1 \/ a = 0 -> x .* a = a *)
    Lemma vcmul_same_if_x1_or_v0 : forall {n} x (a : vec n),
        (x = Aone \/ a = vzero) -> x \.* a = a.
    Proof.
      intros. destruct H; subst. apply vcmul_1_l; auto. apply vcmul_0_r; auto.
    Qed.
    
    (** x .* a = a -> a <> 0 -> x = 1 *)
    Corollary vcmul_same_imply_x1 : forall {n} x (a : vec n),
        x \.* a = a -> a <> vzero -> x = Aone.
    Proof. intros. apply (vcmul_same_imply_x1_or_v0 x a) in H; tauto. Qed.
    
    (** x .* a = a -> x <> 1 -> a = 0 *)
    Corollary vcmul_same_imply_v0 : forall {n} x (a : vec n),
        x \.* a = a -> x <> Aone -> a = vzero.
    Proof. intros. apply (vcmul_same_imply_x1_or_v0 x a) in H; tauto. Qed.

    (** x .* a = y .* a -> (x = y \/ a = 0) *)
    Lemma vcmul_sameV_imply_eqX_or_v0 : forall {n} x y (a : vec n), 
        x \.* a = y \.* a -> (x = y \/ a = vzero).
    Proof.
      intros. destruct (Aeqdec x y); auto. right. rewrite veq_iff_vnth in H.
      rewrite veq_iff_vnth. intros. specialize (H i). rewrite !vnth_vcmul in H.
      destruct (Aeqdec (a i) Azero); auto. apply field_mul_cancel_r in H; tauto.
    Qed.

    (** x .* a = y * a -> a <> 0 -> x = y *)
    Corollary vcmul_sameV_imply_eqX : forall {n} x y (a : vec n), 
        x \.* a = y \.* a -> a <> vzero -> x = y.
    Proof. intros. apply vcmul_sameV_imply_eqX_or_v0 in H; tauto. Qed.

    (** x .* a  = y .* a -> x <> y -> a = 0 *)
    Corollary vcmul_sameV_imply_v0 : forall {n} x y (a : vec n), 
        x \.* a = y \.* a -> x <> y -> a = vzero.
    Proof. intros. apply vcmul_sameV_imply_eqX_or_v0 in H; tauto. Qed.
  End Dec_Field.
  
End vcmul.


(** ** Dot product *)
Section vdot.
  
  (* Let's have an Abelian-ring *)
  Context `{HARing : ARing A Aadd Azero Aopp Amul Aone}.
  Add Ring ring_inst : (make_ring_theory HARing).
  
  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + (- b))%A.
  Infix "-" := Asub : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "1" := Aone.
  Notation "a ²" := (a * a) : A_scope.

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vcmul := (@vcmul _ Amul).
  Notation seqsum := (@seqsum _ Aadd Azero).
  Notation vsum := (@vsum _ Aadd Azero).
  Infix "+" := vadd : vec_scope.
  Notation "- a" := (vopp a) : vec_scope.
  Notation "a - b" := ((a + -b)%V) : vec_scope.
  Infix "\.*" := vcmul : vec_scope.
  
  Definition vdot {n : nat} (a b : vec n) : A := vsum (vmap2 Amul a b).
  Notation "< a , b >" := (vdot a b) : vec_scope.

  (** <a, b> = <b, a> *)
  Lemma vdot_comm : forall {n} (a b : vec n), <a, b> = <b, a>.
  Proof. intros. apply vsum_eq; intros. rewrite vmap2_comm; auto. Qed.

  (** <vzero, a> = vzero *)
  Lemma vdot_0_l : forall {n} (a : vec n), <vzero, a> = Azero.
  Proof.
    intros. unfold vdot. apply vsum_eq0; intros.
    rewrite vnth_vmap2, vnth_vzero. ring.
  Qed.
  
  (** <a, vzero> = vzero *)
  Lemma vdot_0_r : forall {n} (a : vec n), <a, vzero> = Azero.
  Proof. intros. rewrite vdot_comm, vdot_0_l; auto. Qed.

  (** <a + b, c> = <a, c> + <b, c> *)
  Lemma vdot_vadd_l : forall {n} (a b c : vec n), <a + b, c> = (<a, c> + <b, c>)%A.
  Proof.
    intros. unfold vdot. rewrite vsum_add; intros.
    apply vsum_eq; intros. rewrite !vnth_vmap2. ring.
  Qed.

  (** <a, b + c> = <a, b> + <a, c> *)
  Lemma vdot_vadd_r : forall {n} (a b c : vec n), <a, b + c> = (<a, b> + <a, c>)%A.
  Proof.
    intros. rewrite vdot_comm. rewrite vdot_vadd_l. f_equal; apply vdot_comm.
  Qed.

  (** <- a, b> = - <a, b> *)
  Lemma vdot_vopp_l : forall {n} (a b : vec n), < - a, b> = (- <a, b>)%A.
  Proof.
    intros. unfold vdot. rewrite vsum_opp; intros.
    apply vsum_eq; intros. rewrite !vnth_vmap2. rewrite vnth_vopp. ring.
  Qed.

  (** <a, - b> = - <a, b> *)
  Lemma vdot_vopp_r : forall {n} (a b : vec n), <a, - b> = (- <a, b>)%A.
  Proof. intros. rewrite vdot_comm, vdot_vopp_l, vdot_comm. auto. Qed.

  (** <a - b, c> = <a, c> - <b, c> *)
  Lemma vdot_vsub_l : forall {n} (a b c : vec n), <a - b, c> = (<a, c> - <b, c>)%A.
  Proof. intros. rewrite vdot_vadd_l. f_equal. apply vdot_vopp_l. Qed.

  (** <a, b - c> = <a, b> - <a, c> *)
  Lemma vdot_vsub_r : forall {n} (a b c : vec n), <a, b - c> = (<a, b> - <a, c>)%A.
  Proof. intros. rewrite vdot_vadd_r. f_equal. apply vdot_vopp_r. Qed.

  (** <x .* a, b> = x .* <a, b> *)
  Lemma vdot_vcmul_l : forall {n} (a b : vec n) x, <x \.* a, b> = x * <a, b>.
  Proof.
    intros. unfold vdot. rewrite vsum_cmul_l; intros.
    apply vsum_eq; intros. rewrite !vnth_vmap2. rewrite vnth_vcmul. ring.
  Qed.
  
  (** <a, x .* b> = x .* <a, b> *)
  Lemma vdot_vcmul_r : forall {n} (a b : vec n) x, <a, x \.* b> = x * <a, b>.
  Proof.
    intros. rewrite vdot_comm. rewrite vdot_vcmul_l. f_equal; apply vdot_comm.
  Qed.
  
  (** <a, veye i> = a i *)
  Lemma vdot_veye_r : forall {n} (a : vec n) i, <a, veye 0 1 i> = a i.
  Proof.
    intros. apply vsum_unique with (i:=i).
    - rewrite vnth_vmap2. rewrite vnth_veye_eq. rewrite identityRight; auto.
    - intros. rewrite vnth_vmap2. rewrite vnth_veye_neq; auto.
      rewrite ring_mul_0_r; auto.
  Qed.

  (** <veye i, a> = a i *)
  Lemma vdot_veye_l : forall {n} (a : vec n) i, <veye 0 1 i, a> = a i.
  Proof. intros. rewrite vdot_comm. apply vdot_veye_r. Qed.

  (** <vconsT a x, vconsT b y> = <a, b> + x * y *)
  Lemma vdot_vconsT_vconsT : forall {n} (a b : vec n) (x y : A),
      <vconsT a x, vconsT b y> = (<a, b> + x * y)%A.
  Proof.
    intros. unfold vdot.
    rewrite vmap2_vconsT_vconsT.
    rewrite vsum_vconsT. auto.
  Qed.
    
  (* If (@eq A) is decidable *)
  Section AeqDec.
    Context {AeqDec : Dec (@eq A)}.

    (** <a, b> <> 0 -> a <> 0 *)
    Lemma vdot_neq0_imply_neq0_l : forall {n} (a b : vec n), <a, b> <> 0 -> a <> vzero.
    Proof.
      intros. destruct (Aeqdec a vzero); auto. subst. rewrite vdot_0_l in H. easy.
    Qed.
    
    (** <a, b> <> 0 -> b <> 0 *)
    Lemma vdot_neq0_imply_neq0_r : forall {n} (a b : vec n), <a, b> <> 0 -> b <> vzero.
    Proof.
      intros. destruct (Aeqdec b vzero); auto. subst. rewrite vdot_0_r in H. easy.
    Qed.
    
    (** (∀ c, <a, c> = <b, c>) -> a = b *)
    Lemma vdot_cancel_r : forall {n} (a b : vec n),
        (forall c : vec n, <a, c> = <b, c>) -> a = b.
    Proof.
      intros. destruct (Aeqdec a b) as [H1|H1]; auto. exfalso.
      apply vneq_iff_exist_vnth_neq in H1. destruct H1 as [i H1].
      specialize (H (veye 0 1 i)). rewrite !vdot_veye_r in H. easy.
    Qed.
    
    (** (∀ c, <c, a> = <c, b>) -> a = b *)
    Lemma vdot_cancel_l : forall {n} (a b : vec n),
        (forall c : vec n, <c, a> = <c, b>) -> a = b.
    Proof.
      intros. apply vdot_cancel_r. intros. rewrite !(vdot_comm _ c). auto.
    Qed.
    
  End AeqDec.


  (* If equip an ordered-abelian-ring *)
  Section OrderedARing.
    Context `{HOrderedARing : OrderedARing A Aadd Azero Aopp Amul Aone}.
    Infix "<" := Alt.
    Infix "<=" := Ale.
    
    (** 0 <= <a, a> *)
    Lemma vdot_ge0 : forall {n} (a : vec n), 0 <= (<a, a>).
    Proof.
      intros. unfold vdot, vsum, vmap2, v2f. apply seqsum_ge0; intros.
      fin. apply sqr_ge0.
    Qed.

    (** <a, b> ² <= <a, a> * <b, b> *)
    Lemma vdot_sqr_le : forall {n} (a b : vec n), (<a, b> ²) <= <a, a> * <b, b>.
    Proof.
      intros. unfold vdot,vsum,vmap2. destruct n.
      - cbv. apply le_refl.
      - (* Convert dependent "vec" to non-dependent "nat -> A", by "Abstraction" *)
        rewrite seqsum_eq with (f:=v2f 0 (fun i=>a i * b i)) (g:=fun i => a #i * b #i).
        rewrite seqsum_eq with (f:=v2f 0 (fun i=>a i * a i)) (g:=fun i => a #i * a #i).
        rewrite seqsum_eq with (f:=v2f 0 (fun i=>b i * b i)) (g:=fun i => b #i * b #i).
        + apply seqsum_SqrMul_le_MulSqr.
        + intros. erewrite nth_v2f. erewrite nat2finS_eq; auto.
        + intros. erewrite nth_v2f. erewrite nat2finS_eq; auto.
        + intros. erewrite nth_v2f. erewrite nat2finS_eq; auto.
          Unshelve. all: auto.
    Qed.

    (** (v i)² <= <a, a> *)
    Lemma vnth_sqr_le_vdot : forall {n} (a : vec n) (i : fin n), (a i) ² <= <a, a>.
    Proof.
      intros. unfold vdot.
      pose ((fun i => (a.[i]) * (a.[i])) : vec n) as u.
      replace (a i)² with (u i). replace (vmap2 Amul a a) with u.
      apply vsum_ge_any.
      - intros. unfold u. apply sqr_ge0.
      - unfold u. auto.
      - unfold u. auto.
    Qed.
    
  End OrderedARing.

  
  (* If equip an ordered-field and `Dec` *)
  Section OrderedField_Dec.
    Context {AeqDec : Dec (@eq A)}.
    Context `{HOrderedField : OrderedField A Aadd Azero Aopp Amul Aone}.
    Notation "/ a" := (Ainv a).
    Notation Adiv x y := (x * / y).
    Infix "/" := Adiv.
    Infix "<" := Alt.
    Infix "<=" := Ale.
    
    (** a = 0 -> <a, a> = 0 *)
    Lemma vdot_same_eq0_if_vzero : forall {n} (a : vec n), a = vzero -> <a, a> = 0.
    Proof. intros. subst. rewrite vdot_0_l; auto. Qed.
    
    (** <a, a> = 0 -> a = 0 *)
    Lemma vdot_same_eq0_then_vzero : forall {n} (a : vec n), <a, a> = 0 -> a = vzero.
    Proof.
      intros. unfold vdot,vsum in H. apply veq_iff_vnth; intros.
      apply seqsum_eq0_imply_seq0 with (i:=fin2nat i) in H; fin.
      - rewrite nth_v2f with (H:=fin2nat_lt _) in H.
        rewrite nat2fin_fin2nat in H. rewrite vnth_vmap2 in H.
        apply field_sqr_eq0_reg in H; auto.
      - intros. rewrite nth_v2f with (H:=H0). rewrite vnth_vmap2. apply sqr_ge0.
    Qed.
    
    (** a <> vzero -> <a, a> <> 0 *)
    Lemma vdot_same_neq0_if_vnonzero : forall {n} (a : vec n), a <> vzero -> <a, a> <> 0.
    Proof. intros. intro. apply vdot_same_eq0_then_vzero in H0; auto. Qed.
    
    (** <a, a> <> 0 -> a <> vzero *)
    Lemma vdot_same_neq0_then_vnonzero : forall {n} (a : vec n), <a, a> <> 0 -> a <> vzero.
    Proof. intros. intro. apply vdot_same_eq0_if_vzero in H0; auto. Qed.
    
    (** 0 < <a, a> *)
    Lemma vdot_gt0 : forall {n} (a : vec n), a <> vzero -> Azero < (<a, a>).
    Proof.
      intros. apply vdot_same_neq0_if_vnonzero in H. pose proof (vdot_ge0 a).
      apply lt_if_le_and_neq; auto.
    Qed.

    (** <a, b>² / (<a, a> * <b, b>) <= 1. *)
    Lemma vdot_sqr_le_form2 : forall {n} (a b : vec n),
        a <> vzero -> b <> vzero -> <a, b>² / (<a, a> * <b, b>) <= 1.
    Proof.
      intros.
      pose proof (vdot_gt0 a H). pose proof (vdot_gt0 b H0).
      pose proof (vdot_sqr_le a b).
      destruct (Aeqdec (<a, b>) 0) as [H4|H4].
      - rewrite H4. ring_simplify. apply le_0_1.
      - apply le_imply_div_le_1 in H3; auto. apply sqr_gt0. auto.
    Qed.

  End OrderedField_Dec.

End vdot.

Section vdot_extra.
  Context `{HARing : ARing}.
  Add Ring ring_inst : (make_ring_theory HARing).
  Infix "*" := Amul : A_scope.
  Notation vdot := (@vdot _ Aadd Azero Amul).
  
  (** <<a,D>, b> = <a, <D,b> *)
  (* For example:
     (a1,a2,a3) [D11,D12] [b1]  记作 a*D*b，
                [D21,D22] [b2]
                [D31,D32]
     (a*D)*b = <a,col(D,1)> b1 + <a,col(D,2)> b2
             = (a1D11+a2D21+a3D31)b1 + (a1D12+a2D22+a3D32)b2
     a*(D*b) = a1 <row(D,1),b> + a2 <row(D,2),b> + a3 <row(D,3),b>
             = a1(D11b1+D12b2)+a2(D21b1+D22b2)+a3(D31b1+D32b2) *)
  
  Theorem vdot_assoc :
    forall {r c} (a : @vec A c) (D : @vec (@vec A r) c) (b : @vec A r),
      vdot (fun j => vdot a (fun i => D i j)) b = vdot a (fun i => vdot (D i) b).
  Proof.
    intros. unfold vdot. unfold vmap2.
    pose proof (vsum_vsum c r (fun i j => a.[i] * D.[i].[j] * b.[j])).
    match goal with
    | H: ?a1 = ?a2 |- ?b1 = ?b2 => replace b1 with a2; [replace b2 with a1|]; auto
    end.
    - apply vsum_eq; intros. rewrite vsum_cmul_l. apply vsum_eq; intros. ring.
    - apply vsum_eq; intros. rewrite vsum_cmul_r. apply vsum_eq; intros. ring.
  Qed.

End vdot_extra.

(* ======================================================================= *)
(** ** Euclidean norm (L2 norm), Length of vector *)
Section vlen.
  (* Euclidean norm == Euclidean length (distance) = L2 norm == L2 distance *)
  
  Context `{HARing : ARing A Aadd Azero Aopp Amul Aone}.
  Add Ring ring_inst : (make_ring_theory HARing).
  Context `{HConvertToR
      : ConvertToR A Aadd Azero Aopp Amul Aone Ainv Alt Ale Altb Aleb a2r}.

  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero : A_scope.
  Infix "*" := Amul : A_scope.
  (* Notation "a ²" := (a * a) : A_scope. *)
  Notation "1" := Aone : A_scope.
  Notation "| a |" := (@Aabs _ 0 Aopp Aleb a) : A_scope.
  
  Notation vzero := (@vzero _ Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vcmul := (@vcmul _ Amul).
  Notation vdot := (@vdot _ Aadd Azero Amul).
  
  Infix "+" := vadd : vec_scope.
  Notation "- a" := (vopp a) : vec_scope.
  Notation "a - b" := ((a + -b)%V) : vec_scope.
  Infix "\.*" := vcmul : vec_scope.
  Notation "< a , b >" := (vdot a b) : vec_scope.

  (** Length (magnitude) of a vector, is derived by inner-product *)
  Definition vlen {n} (a : vec n) : R := R_sqrt.sqrt (a2r (<a, a>)).
  Notation "|| a ||" := (vlen a) : vec_scope.

  (** ||vzero|| = 0 *)
  Lemma vlen_vzero : forall {n:nat}, @vlen n vzero = 0%R.
  Proof. intros. unfold vlen. rewrite vdot_0_l. rewrite a2r_0 at 1. ra. Qed.
  
  Section OrderedARing.
    Context `{HOrderedARing
        : OrderedARing A Aadd Azero Aopp Amul Aone Alt Ale Altb Aleb}.
    Infix "<" := Alt : A_scope.
    Infix "<=" := Ale : A_scope.
    
    (** 0 <= ||a|| *)
    Lemma vlen_ge0 : forall {n} (a : vec n), (0 <= ||a||)%R.
    Proof. intros. unfold vlen. ra. Qed.
    
    (** ||a|| = ||b|| <-> <a, a> = <b, b> *)
    Lemma vlen_eq_iff_dot_eq : forall {n} (a b : vec n), ||a|| = ||b|| <-> <a, a> = <b, b>.
    Proof.
      intros. unfold vlen. split; intros H; try rewrite H; auto.
      apply sqrt_inj in H.
      rewrite a2r_eq_iff in H; auto.
      apply a2r_ge0_iff; apply vdot_ge0.
      apply a2r_ge0_iff; apply vdot_ge0.
    Qed.

    (** <a, a> = ||a||² *)
    Lemma vdot_same : forall {n} (a : vec n), a2r (<a, a>) = (||a||²)%R.
    Proof.
      intros. unfold vlen. rewrite Rsqr_sqrt; auto.
      apply a2r_ge0_iff. apply vdot_ge0.
    Qed.

    (** |a i| <= ||a|| *)
    Lemma vnth_le_vlen : forall {n} (a : vec n) (i : fin n),
        a <> vzero -> (a2r (|a i|%A) <= ||a||)%R.
    Proof.
      intros. apply Rsqr_incr_0_var.
      - rewrite <- vdot_same. unfold Rsqr. rewrite <- a2r_mul. apply a2r_le_iff.
        replace (|a i| * |a i|) with (a i * a i). apply vnth_sqr_le_vdot.
        rewrite <- Aabs_mul. rewrite Aabs_right; auto. apply sqr_ge0.
      - apply vlen_ge0.
    Qed.

    (** ||a|| = 1 <-> <a, a> = 1 *)
    Lemma vlen_eq1_iff_vdot1 : forall {n} (a : vec n), ||a|| = 1%R <-> <a, a> = 1.
    Proof.
      intros. unfold vlen. rewrite sqrt_eq1_iff. rewrite a2r_eq1_iff. easy.
    Qed.

    (** ||- a|| = ||a|| *)
    Lemma vlen_vopp : forall n (a : vec n), ||- a|| = ||a||.
    Proof.
      intros. unfold vlen. f_equal. f_equal. rewrite vdot_vopp_l,vdot_vopp_r. ring.
    Qed.

    (** ||x .* a|| = |x| * ||a|| *)
    Lemma vlen_vcmul : forall n x (a : vec n), ||x \.* a|| = ((a2r (|x|))%A * ||a||)%R.
    Proof.
      intros. unfold vlen.
      rewrite commutative.
      replace (a2r (|x|)%A) with (|(a2r x)|)%R.
      2:{ rewrite a2r_Aabs. auto. }
      rewrite <- sqrt_square_abs. rewrite <- sqrt_mult_alt.
      - f_equal. rewrite vdot_vcmul_l, vdot_vcmul_r, <- associative.
        rewrite a2r_mul. rewrite commutative. f_equal. rewrite a2r_mul. auto.
      - apply a2r_ge0_iff. apply vdot_ge0.
    Qed.

    (** ||a + b||² = ||a||² + ||a||² + 2 * <a, b> *)
    Lemma vlen_sqr_vadd : forall {n} (a b : vec n),
        ||(a + b)||² = (||a||² + ||b||² + 2 * a2r (<a, b>))%R.
    Proof.
      intros. rewrite <- !vdot_same. rewrite !vdot_vadd_l, !vdot_vadd_r.
      rewrite (vdot_comm b a). rewrite !a2r_add. ring.
    Qed.

    (** ||a - b||² = ||a||² + ||b||² - 2 * <a, b> *)
    Lemma vlen_sqr_vsub : forall {n} (a b : vec n),
        ||(a - b)||² = (||a||² + ||b||² - 2 * a2r (<a, b>))%R.
    Proof.
      intros. rewrite <- !vdot_same.
      rewrite !vdot_vadd_l, !vdot_vadd_r.
      rewrite !vdot_vopp_l, !vdot_vopp_r. rewrite (vdot_comm b a).
      rewrite !a2r_add, !a2r_opp at 1. ring.
    Qed.

    (* 柯西.许西尔兹不等式，Cauchy-Schwarz Inequality *)
    (** |<a, b>| <= ||a|| * ||b|| *)
    Lemma vdot_abs_le : forall {n} (a b : vec n), (|a2r (<a, b>)| <= ||a|| * ||b||)%R.
    Proof.
      intros. pose proof (vdot_sqr_le a b).
      apply a2r_le_iff in H. rewrite !a2r_mul in H.
      rewrite (vdot_same a) in H. rewrite (vdot_same b) in H.
      replace (||a||² * ||b||²)%R with ((||a|| * ||b||)²) in H; [| cbv;ring].
      apply Rsqr_le_abs_0 in H.
      replace (|(||a|| * ||b||)|)%R with (||a|| * ||b||)%R in H; auto.
      rewrite !Rabs_right; auto.
      pose proof (vlen_ge0 a). pose proof (vlen_ge0 b). ra.
    Qed.

    (** <a, b> <= ||a|| * ||b|| *)
    Lemma vdot_le_mul_vlen : forall {n} (a b : vec n), (a2r (<a, b>) <= ||a|| * ||b||)%R.
    Proof. intros. pose proof (vdot_abs_le a b). apply Rabs_le_rev in H. ra. Qed.

    (** - ||a|| * ||b|| <= <a, b> *)
    Lemma vdot_ge_mul_vlen_neg : forall {n} (a b : vec n),
        (- (||a|| * ||b||) <= a2r (<a, b>))%R.
    Proof. intros. pose proof (vdot_abs_le a b). apply Rabs_le_rev in H. ra. Qed.

    (* 任意维度“三角形”的任意一边的长度小于等于两边长度之和 *)
    (** ||a + b|| <= ||a|| + ||a|| *)
    Lemma vlen_le_add : forall {n} (a b : vec n), (||(a + b)%V|| <= ||a|| + ||b||)%R.
    Proof.
      intros. apply Rsqr_incr_0_var.
      2:{ unfold vlen; ra. }
      rewrite Rsqr_plus. rewrite <- !vdot_same.
      replace (a2r (<a + b, a + b>))
        with (a2r (<a, a>) + a2r (<b, b>) + (2 * a2r (<a, b>)))%R.
      2:{ rewrite vdot_vadd_l,!vdot_vadd_r.
          rewrite (vdot_comm b a). rewrite !a2r_add at 1. ra. }
      apply Rplus_le_compat_l.
      rewrite !associative. apply Rmult_le_compat_l; ra.
      pose proof (vdot_abs_le a b). unfold Rabs in H.
      destruct Rcase_abs; ra.
    Qed.

    (* 任意维度“三角形”的任意一边的长度大于等于两边长度之差 *)
    (** ||a|| - ||b|| <= ||a + b|| *)
    Lemma vlen_ge_sub : forall {n} (a b : vec n), ((||a|| - ||b||) <= ||(a + b)%V||)%R.
    Proof.
      intros. apply Rsqr_incr_0_var.
      2:{ unfold vlen; ra. }
      rewrite Rsqr_minus. rewrite <- !vdot_same.
      replace (a2r (<a + b, a + b>))
        with (a2r (<a, a>) + a2r (<b, b>) + (2 * a2r (<a, b>)))%R.
      2:{ rewrite vdot_vadd_l,!vdot_vadd_r.
          rewrite (vdot_comm b a). rewrite !a2r_add at 1. ra. }
      apply Rplus_le_compat_l.
      pose proof (vdot_abs_le a b). unfold Rabs in H.
      destruct Rcase_abs; ra.
    Qed.

  End OrderedARing.

  Section OrderedField_Dec.
    Context `{HOrderedField
        : OrderedField A Aadd Azero Aopp Amul Aone Ainv Alt Ale}.
    Context {AeqDec : Dec (@eq A)}.
    Infix "<=" := Ale : A_scope.
    
    (** ||a|| = 0 <-> v = 0 *)
    Lemma vlen_eq0_iff_eq0 : forall {n} (a : vec n), ||a|| = 0%R <-> a = vzero.
    Proof.
      intros. unfold vlen. split; intros.
      - apply vdot_same_eq0_then_vzero. apply sqrt_eq_0 in H; auto.
        apply a2r_eq0_iff; auto. apply a2r_ge0_iff; apply vdot_ge0.
      - rewrite H. rewrite vdot_0_l. rewrite a2r_0 at 1. ra.
    Qed.
    
    (** ||a|| <> 0 <-> a <> 0 *)
    Lemma vlen_neq0_iff_neq0 : forall {n} (a : vec n), ||a|| <> 0%R <-> a <> vzero.
    Proof. intros. rewrite vlen_eq0_iff_eq0. easy. Qed.

    (** a <> vzero -> 0 < ||a|| *)
    Lemma vlen_gt0 : forall {n} (a : vec n), a <> vzero -> (0 < ||a||)%R.
    Proof. intros. pose proof (vlen_ge0 a). apply vlen_neq0_iff_neq0 in H; ra. Qed.
    
    (** 0 <= <a, a> *)
    Lemma vdot_same_ge0 : forall {n} (a : vec n), (Azero <= <a, a>)%A.
    Proof.
      intros. destruct (Aeqdec a vzero) as [H|H].
      - subst. rewrite vdot_0_l. apply le_refl.
      - apply le_if_lt. apply vdot_gt0; auto.
    Qed.
    
  End OrderedField_Dec.
  
End vlen.

#[export] Hint Resolve vlen_ge0 : vec.


(* ======================================================================= *)
(** ** Unit vector *)

Section vunit.
  Context `{HARing : ARing}.
  Add Ring ring_inst : (make_ring_theory HARing).
  
  Notation "1" := Aone.
  Notation vzero := (vzero Azero).
  Notation vopp := (@vopp _ Aopp).
  Notation vdot := (@vdot _ Aadd Azero Amul).
  Notation "< a , b >" := (vdot a b) : vec_scope.
  
  (** A unit vector `a` is a vector whose length equals one.
      Here, we use the square of length instead of length directly,
      but this is reasonable with the proof of vunit_spec. *)
  Definition vunit {n} (a : vec n) : Prop := <a, a> = 1.
  
  (** vunit a <-> vunit (vopp a). *)
  Lemma vopp_vunit : forall {n} (a : vec n), vunit (vopp a) <-> vunit a.
  Proof.
    intros. unfold vunit. rewrite vdot_vopp_l, vdot_vopp_r.
    rewrite group_opp_opp. easy.
  Qed.

  Section Field.
    Context `{HField : Field A Aadd Azero Aopp Amul Aone Ainv}.
    
    (** The unit vector cannot be zero vector *)
    Lemma vunit_neq0 : forall {n} (a : vec n), vunit a -> a <> vzero.
    Proof.
      intros. intro. rewrite H0 in H. unfold vunit in H.
      rewrite vdot_0_l in H. apply field_1_neq_0. easy.
    Qed.
    
  End Field.

  Section ConvertToR.
    Context `{HConvertToR : ConvertToR A Aadd Azero Aopp Amul Aone Ainv Alt Ale}.

    Notation vlen := (@vlen _ Aadd Azero Amul a2r).
    Notation "|| a ||" := (vlen a) : vec_scope.

    (** Verify the definition is reasonable *)
    Lemma vunit_spec : forall {n} (a : vec n), vunit a <-> ||a|| = 1%R.
    Proof. intros. split; intros; apply vlen_eq1_iff_vdot1; auto. Qed.

  End ConvertToR.

(** If column of a and column of b all are unit, 
    then column of (a * b) is also unit *)
  (*   a : mat 2 2 *)
  (* a1 : vunit (mat2col a 0) *)
  (* a2 : vunit (mat2col a 1) *)
  (* a3 : vorth (mat2col a 0) (mat2col a 1) *)
  (* b1 : vunit (mat2col b 0) *)
  (* b2 : vunit (mat2col b 1) *)
  (* b3 : vorth (mat2col b 0) (mat2col b 1) *)
  (* ============================ *)
  (* vunit (mat2col (a * b) 0) *)
End vunit.


(* ======================================================================= *)
(** ** Orthogonal vectors 正交的两个向量 *)
Section vorth.
  (* Two vectors, u and v, in an inner product space v, are orthogonal (also called 
     perpendicular) if their inner-product is zero. It can be denoted as `u ⟂ v` *)
  
  (* Let's have an Abelian-ring *)
  Context `{HARing : ARing A Aadd Azero Aopp Amul Aone}.
  Add Ring ring_inst : (make_ring_theory HARing).
  
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + (- b))%A.
  Infix "-" := Asub : A_scope.

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vcmul := (@vcmul _ Amul).
  Notation vdot := (@vdot _ Aadd Azero Amul).
  Infix "+" := vadd : vec_scope.
  Notation "- a" := (vopp a) : vec_scope.
  Notation "a - b" := ((a + -b)%V) : vec_scope.
  Infix "\.*" := vcmul : vec_scope.
  Notation "< a , b >" := (vdot a b) : vec_scope.
  
  Definition vorth {n} (a b : vec n) : Prop := <a, b> = Azero.
  Infix "_|_" := vorth : vec_scope.

  (** a _|_ b -> b _|_ a *)
  Lemma vorth_comm : forall {n} (a b : vec n), a _|_ b -> b _|_ a.
  Proof. intros. unfold vorth in *. rewrite vdot_comm; auto. Qed.


  (* If equip a `Dec` and a `Field` *)
  Section Dec_Field.
    Context {AeqDec : Dec (@eq A)}.
    Context `{HField : Field A Aadd Azero Aopp Amul Aone Ainv}.
    
    (** (x .* a) _|_ b <-> a _|_ b *)
    Lemma vorth_vcmul_l : forall {n} x (a b : vec n),
        x <> Azero -> ((x \.* a) _|_ b <-> a _|_ b).
    Proof.
      intros. unfold vorth in *. rewrite vdot_vcmul_l. split; intros.
      - apply field_mul_eq0_iff in H0. destruct H0; auto. easy.
      - rewrite H0. ring.
    Qed.
    
    (** a _|_ (x .* b) <-> a _|_ b *)
    Lemma vorth_vcmul_r : forall {n} x (a b : vec n),
        x <> Azero -> (a _|_ (x \.* b) <-> a _|_ b).
    Proof.
      intros. split; intros.
      - apply vorth_comm in H0. apply vorth_comm. apply vorth_vcmul_l in H0; auto.
      - apply vorth_comm in H0. apply vorth_comm. apply vorth_vcmul_l; auto.
    Qed.
  End Dec_Field.
  
End vorth.



(** ** Projection component of a vector onto another *)
Section vproj.
  
  (* Let's have an field *)
  Context `{F:Field A Aadd Azero Aopp Amul Aone Ainv}.
  Add Field field_inst : (make_field_theory F).
  
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + (- b))%A.
  Infix "-" := Asub : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv a b := (a * (/ b))%A.
  Infix "/" := Adiv : A_scope.

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vcmul := (@vcmul _ Amul).
  Notation vdot := (@vdot _ Aadd Azero Amul).
  Notation vunit := (@vunit _ Aadd Azero Amul Aone).
  Notation vorth := (@vorth _ Aadd Azero Amul).
  Infix "+" := vadd : vec_scope.
  Notation "- a" := (vopp a) : vec_scope.
  Notation "a - b" := ((a + -b)%V) : vec_scope.
  Infix "\.*" := vcmul : vec_scope.
  Notation "< a , b >" := (vdot a b) : vec_scope.
  Infix "_|_" := vorth : vec_scope.
  
  (** The projection component of `a` onto `b` *)
  Definition vproj {n} (a b : vec n) : vec n := (<a, b> / <b, b>) \.* b.

  (** a _|_ b -> vproj a b = vzero *)
  Lemma vorth_imply_vproj_eq0 : forall {n} (a b : vec n), a _|_ b -> vproj a b = vzero.
  Proof.
    intros. unfold vorth in H. unfold vproj. rewrite H.
    replace (Azero * / (<b, b>)) with Azero. apply vcmul_0_l.
    rewrite ring_mul_0_l; auto.
  Qed.

  (** vunit b -> vproj a b = <a, b> .* b *)
  Lemma vproj_vunit : forall {n} (a b : vec n), vunit b -> vproj a b = <a, b> \.* b.
  Proof. intros. unfold vproj. f_equal. rewrite H. field. apply field_1_neq_0. Qed.

  (* If equip a `Field` *)
  Section OrderedField.
    Context `{HOrderedField : OrderedField A Aadd Azero Aopp Amul Aone Ainv}.
    
    (** vproj (a + b) c = vproj a c + vproj b c *)
    Lemma vproj_vadd : forall {n} (a b c : vec n),
        c <> vzero -> (vproj (a + b) c = vproj a c + vproj b c)%V.
    Proof.
      intros. unfold vproj. rewrite vdot_vadd_l. rewrite <- vcmul_add. f_equal.
      field. apply vdot_same_neq0_if_vnonzero; auto.
    Qed.
    
    (** vproj (x .* a) b = x .* (vproj a b) *)
    Lemma vproj_vcmul : forall {n} (a b : vec n) x,
        b <> vzero -> (vproj (x \.* a) b = x \.* (vproj a b))%V.
    Proof.
      intros. unfold vproj. rewrite vdot_vcmul_l. rewrite vcmul_assoc. f_equal.
      field. apply vdot_same_neq0_if_vnonzero; auto.
    Qed.
    
    (** vproj a a = a *)
    Lemma vproj_same : forall {n} (a : vec n), a <> vzero -> vproj a a = a.
    Proof.
      intros. unfold vproj. replace (<a, a> / <a, a>) with Aone; try field.
      apply vcmul_1_l. apply vdot_same_neq0_if_vnonzero; auto.
    Qed.
  End OrderedField.

End vproj.


(* ======================================================================= *)
(** ** Perpendicular component of a vector respect to another *)
Section vperp.
  
  (* Let's have an field *)
  Context `{F:Field A Aadd Azero Aopp Amul Aone Ainv}.
  Add Field field_inst : (make_field_theory F).
  
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + (- b))%A.
  Infix "-" := Asub : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv a b := (a * (/ b))%A.
  Infix "/" := Adiv : A_scope.

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vcmul := (@vcmul _ Amul).
  Notation vdot := (@vdot _ Aadd Azero Amul).
  Notation vproj := (@vproj _ Aadd Azero Amul Ainv).
  Notation vorth := (@vorth _ Aadd Azero Amul).
  Infix "+" := vadd : vec_scope.
  Notation "- a" := (vopp a) : vec_scope.
  Notation "a - b" := ((a + -b)%V) : vec_scope.
  Infix "\.*" := vcmul : vec_scope.
  Notation "< a , b >" := (vdot a b) : vec_scope.
  Infix "_|_" := vorth : vec_scope.
  
  (** The perpendicular component of `a` respect to `b` *)
  Definition vperp {n} (a b : vec n) : vec n := a - vproj a b.

  (** vperp a b = a - vproj a b *)
  Lemma vperp_eq_minus_vproj : forall {n} (a b : vec n), vperp a b = a - vproj a b.
  Proof. auto. Qed.

  (** vproj a b = a - vperp a b *)
  Lemma vproj_eq_minus_vperp : forall {n} (a b : vec n), vproj a b = a - vperp a b.
  Proof.
    intros. unfold vperp. pose proof (vadd_AGroup (A:=A) n). agroup.
  Qed.

  (** (vproj a b) + (vperp a b) = a *)
  Lemma vproj_plus_vperp : forall {n} (a b : vec n), vproj a b + vperp a b = a.
  Proof.
    intros. unfold vperp. pose proof (vadd_AGroup (A:=A) n). agroup.
  Qed.
  
  (** a _|_ b -> vperp a b = a *)
  Lemma vorth_imply_vperp_eq_l : forall {n} (a b : vec n), a _|_ b -> vperp a b = a.
  Proof.
    intros. unfold vperp. pose proof (vadd_AGroup (A:=A) n). agroup.
    rewrite vorth_imply_vproj_eq0; auto.
  Qed.
  
  (* If equip a `OrderedField` *)
  Section OrderedField.
    Context `{HOrderedField : OrderedField A Aadd Azero Aopp Amul Aone Ainv}.

    (** (vproj a b) _|_ (vperp a b) *)
    Lemma vorth_vproj_vperp : forall {n} (a b : vec n),
        b <> vzero -> vproj a b _|_ vperp a b.
    Proof.
      intros. unfold vorth, vperp, vproj.
      rewrite !vdot_vcmul_l. rewrite vdot_vsub_r. rewrite !vdot_vcmul_r.
      rewrite (vdot_comm b a). field_simplify. rewrite ring_mul_0_l; auto.
      apply vdot_same_neq0_if_vnonzero; auto.
    Qed.
    
    (** vperp (a + b) c = vperp a c + vperp b c *)
    Lemma vperp_vadd : forall {n} (a b c : vec n),
        c <> vzero -> (vperp (a + b) c = vperp a c + vperp b c)%V.
    Proof.
      intros. unfold vperp. pose proof (vadd_AGroup (A:=A) n). agroup.
      rewrite vproj_vadd; auto. agroup.
    Qed.

    (** vperp (x .* a) b = x .* (vperp a b) *)
    Lemma vperp_vcmul : forall {n} (x : A) (a b : vec n),
        b <> vzero -> (vperp (x \.* a) b = x \.* (vperp a b))%V.
    Proof.
      intros. unfold vperp. rewrite vproj_vcmul; auto. rewrite vcmul_vsub. auto.
    Qed.

    (** vperp a a = vzero *)
    Lemma vperp_self : forall {n} (a : vec n), a <> vzero -> vperp a a = vzero.
    Proof.
      intros. unfold vperp. rewrite vproj_same; auto; auto. apply vsub_self.
    Qed.
  End OrderedField.
  
End vperp.


(* ======================================================================= *)
(** ** Two vectors are parallel (on vnonzero version) *)

(* 关于零向量的平行和垂直问题
  1. 来自《高等数学》的理论：
  (1) 零向量的起点和终点重合，它的方向可看做是任意的。
  (2) 如果∠a,b = 0 or π，则称它们平行，记做 a//b。
      当两向量平行时，若将起点放在同一点，则终点和公共起点应在同一条直线，故
      两向量平行也称两向量共线。
  (3) 如果∠a,b = π/2，称它们垂直，记做 a⟂b。
  (4) 由于零向量与另一向量的夹角可以是[0,π]中的任意值，可认为零向量与任何向量
      都平行，也可认为零向量与任何向量都垂直。
  2. 网络上的观点
  (1) There are two choices to handling zero-vector
      a. The mainstream approach is that the zero vector is parallel and
         perpendicular to any vector.
      b. Only consider the non-zero vector, one reason of it is that the 
         transitivity is broken after including zero-vector.
         (因为包含了零向量以后，平行的传递性被破坏了）
  (2) https://www.zhihu.com/question/489006373
      a. “平行”或“不平行”是对两个可以被识别的方向的比较，对于零向量，“方向”是不可
         识别的，或说，是不确定的。从这个角度讲，“平行”这个概念不该被用到评价两个
         零向量的关系上的。
      b. 不过，两个零向量是“相等”的，对于向量而言，“相等”这件事包含了大小和方向
         的相等，这么说来，说两个零向量“方向”相等，也就是“平行”或也是说得通的。
  3. 使用向量运算的做法
  (1) 使用向量的运算来定义平行和垂直，这样无须三角函数就能判定。
      两向量点乘为零，则它们垂直；两向量叉乘为零向量，则它们平行。
  (2) 在严格证明中，都加上非零向量这一假设条件。
  4. 本文的做法
  (1) vnonzero 类型：表示非零向量。
      在这个类型上定义平行、垂直、角度等。
      换言之，零向量上未定义几何关系。
 *)

(* 一种方式是使用子类型 `vnonzero` 来实现 `vpara` 的版本。
   这种做法的特点是：
   1. `vpara`成了等价关系（因为排除了非零向量，而且将非零的条件封装到了类型中）
   2. 同时也带来了一些构造上的繁琐性。因为返回该类型的函数必须要证明其满足非零的条件。
   3. 同时也使得其他相关的函数都要使用 vnonzero 版本，可能过于复杂。
   所以，当一个概念特别有应用需求时，才考虑用这种子类型的方式。
 *)
Module demo_vpara_on_vnonzero.
  Context `{HARing : ARing}.
  Notation vcmul := (@vcmul _ Amul).
  Infix "\.*" := vcmul : vec_scope.

  (** Non-zero element *)
  Record Anonzero :=
    mknonzero {
        nonzero :> A;
        cond_nonzero : nonzero <> Azero
      }.
  
  (** Non-zero vector *)
  Record vnonzero n :=
    mkvnonzero {
        vnonzeroV :> @vec A n ;
        vnonzero_cond : vnonzeroV <> vzero Azero
      }.

  (** Two non-zero vectors are parallel, when their components are proportional *)
  Definition vpara {n} (a b : vnonzero n) : Prop :=
    exists x : A, x \.* a = b.

End demo_vpara_on_vnonzero.


(* ======================================================================= *)
(** ** Two vectors are collinear, parallel or antiparallel. *)
(* https://en.wikipedia.org/wiki/Euclidean_vector
   Two vectors are parallel if they have the same direction but not
   necessarily the same magnitude, or antiparallel if they have opposite
   direction but not necessarily the same magnitude *)
Section vcoll_vpara_vantipara.

  (* 
     1. we need order relation to distinguish "x > 0 or x < 0" to define parallel
        and antiparallel
     2. we need to prove the reflexivity of collinear, so need a nonzero coefficient
        x, such as 1, thus need a field.
     3. we need a coefficent x and 1/x to prove the symmetric of collinear, so we 
        need a field.
   *)
  Context `{HOrderedField
      : OrderedField A Aadd Azero Aopp Amul Aone Ainv Alt Ale Altb Aleb}.
  Add Field field_inst : (make_field_theory HOrderedField).
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Infix "<" := Alt : A_scope.
  Infix "<=" := Ale : A_scope.
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + (- b))%A.
  Infix "-" := Asub : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv a b := (a * (/ b))%A.
  Infix "/" := Adiv : A_scope.

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vcmul := (@vcmul _ Amul).
  Infix "+" := vadd : vec_scope.
  Notation "- a" := (vopp a) : vec_scope.
  Notation "a - b" := ((a + -b)%V) : vec_scope.
  Infix "\.*" := vcmul : vec_scope.


  (** *** Colinear *)
  Section vcoll.
    
    (** Two non-zero vectors are collinear, if the components are proportional *)
    (* Note, x <> 0 could be removed, but it need a prove *)
    Definition vcoll {n} (a b : vec n) : Prop :=
      a <> vzero /\ b <> vzero /\ exists x : A, x <> 0 /\ x \.* a = b.
    Infix "//" := vcoll : vec_scope.
    
    (** a // a *)
    Lemma vcoll_refl : forall {n} (a : vec n), a <> vzero -> a // a.
    Proof.
      intros. hnf. repeat split; auto. exists 1. split.
      apply field_1_neq_0. apply vcmul_1_l.
    Qed.
    
    (** a // b -> b // a *)
    Lemma vcoll_sym : forall {n} (a b : vec n), a // b -> b // a.
    Proof.
      intros. hnf in *. destruct H as [H11 [H12 [x [H13 H14]]]].
      repeat split; auto. exists (/x). split; auto.
      apply field_inv_neq0_iff; auto.
      rewrite <- H14. rewrite vcmul_assoc. rewrite field_mulInvL; auto.
      apply vcmul_1_l.
    Qed.

    (** a // b -> b // c -> a // c *)
    Lemma vcoll_trans : forall {n} (a b c : vec n), a // b -> b // c -> a // c.
    Proof.
      intros. hnf in *.
      destruct H as [H11 [H12 [x1 [H13 H14]]]].
      destruct H0 as [H21 [H22 [x2 [H23 H24]]]].
      repeat split; auto. exists (x2 * x1).
      split. apply field_mul_neq0_iff; auto.
      rewrite <- H24, <- H14. rewrite vcmul_assoc. auto.
    Qed.

    (** a // b => ∃! x, x <> 0 /\ x .* a = b *)
    Lemma vcoll_imply_uniqueX : forall {n} (a b : vec n),
        a // b -> (exists ! x, x <> 0 /\ x \.* a = b).
    Proof.
      intros. destruct H as [H1 [H2 [x [H3 H4]]]]. exists x. split; auto.
      intros j [H5 H6]. rewrite <- H4 in H6.
      apply vcmul_sameV_imply_eqX in H6; auto.
    Qed.

    (** a // b -> (x .* a) // b *)
    Lemma vcoll_vcmul_l : forall {n} x (a b : vec n),
        x <> 0 -> a // b -> x \.* a // b.
    Proof.
      intros. hnf in *. destruct H0 as [H1 [H2 [x1 [H3 H4]]]].
      repeat split; auto.
      - intro. apply vcmul_eq0_imply_x0_or_v0 in H0. destruct H0; auto.
      - exists (x1/x); simpl. split.
        apply field_mul_neq0_iff. split; auto. apply field_inv_neq0_iff; auto.
        rewrite <- H4. rewrite vcmul_assoc. f_equal. field. auto.
    Qed.

    (** a // b -> a // (x \.* b) *)
    Lemma vcoll_vcmul_r : forall {n} x (a b : vec n),
        x <> 0 -> a // b -> a // (x \.* b).
    Proof.
      intros. apply vcoll_sym in H0. apply vcoll_sym. apply vcoll_vcmul_l; auto.
    Qed.
    
  End vcoll.
  

  (** *** Properties about //+ *)
  Section vpara.
    
    (** Two non-zero vectors are parallel, if positive proportional *)
    Definition vpara {n} (a b : vec n) : Prop :=
      a <> vzero /\ b <> vzero /\ exists x : A, 0 < x /\ x \.* a = b.
    Infix "//+" := vpara : vec_scope.
    
    (** a //+ a *)
    Lemma vpara_refl : forall {n} (a : vec n), a <> vzero -> a //+ a.
    Proof.
      intros. hnf. repeat split; auto. exists 1. split. apply lt_0_1. apply vcmul_1_l.
    Qed.
    
    (** a //+ b -> b //+ a *)
    Lemma vpara_sym : forall {n} (a b : vec n), a //+ b -> b //+ a.
    Proof.
      intros. hnf in *. destruct H as [H11 [H12 [x [H13 H14]]]].
      repeat split; auto. exists (/x). split; auto. apply inv_gt0; auto.
      rewrite <- H14. rewrite vcmul_assoc. rewrite field_mulInvL; auto.
      apply vcmul_1_l. symmetry. apply lt_not_eq; auto.
    Qed.

    (** a //+ b -> b //+ c -> a //+ c *)
    Lemma vpara_trans : forall {n} (a b c: vec n), a //+ b -> b //+ c -> a //+ c.
    Proof.
      intros. hnf in *.
      destruct H as [H11 [H12 [x1 [H13 H14]]]].
      destruct H0 as [H21 [H22 [x2 [H23 H24]]]].
      repeat split; auto. exists (x2 * x1). split. apply mul_gt0_if_gt0_gt0; auto.
      rewrite <- H24, <- H14. rewrite vcmul_assoc. auto.
    Qed.

    (** a //+ b => ∃! x, 0 < x /\ x .* a = b *)
    Lemma vpara_imply_uniqueX : forall {n} (a b : vec n),
        a //+ b -> (exists ! x, 0 < x /\ x \.* a = b).
    Proof.
      intros. destruct H as [H1 [H2 [x [H3 H4]]]]. exists x. split; auto.
      intros j [H5 H6]. rewrite <- H4 in H6.
      apply vcmul_sameV_imply_eqX in H6; auto.
    Qed.

    (** a //+ b -> (x \.* a) //+ b *)
    Lemma vpara_vcmul_l : forall {n} x (a b : vec n),
        0 < x -> a //+ b -> x \.* a //+ b.
    Proof.
      intros. hnf in *. destruct H0 as [H1 [H2 [x1 [H3 H4]]]].
      repeat split; auto.
      - intro. apply vcmul_eq0_imply_x0_or_v0 in H0. destruct H0; auto.
        apply lt_not_eq in H. rewrite H0 in H. easy.
      - exists (x1/x); simpl. split.
        + apply mul_gt0_if_gt0_gt0; auto. apply inv_gt0; auto.
        + rewrite <- H4. rewrite vcmul_assoc. f_equal. field.
          symmetry. apply lt_not_eq. auto.
    Qed.

    (** a //+ b -> a //+ (x \.* b) *)
    Lemma vpara_vcmul_r : forall {n} x (a b : vec n),
        0 < x -> a //+ b -> a //+ (x \.* b).
    Proof.
      intros. apply vpara_sym in H0. apply vpara_sym. apply vpara_vcmul_l; auto.
    Qed.
    
  End vpara.


  (** *** Properties about //- *)
  Section vantipara.
    
    (** Two non-zero vectors are antiparallel, if negative proportional *)
    Definition vantipara {n} (a b : vec n) : Prop :=
      a <> vzero /\ b <> vzero /\ exists x : A, x < 0 /\ x \.* a = b.
    Infix "//-" := vantipara : vec_scope.
    
    (** a //- a *)
    Lemma vantipara_refl : forall {n} (a : vec n), a <> vzero -> a //- a.
    Proof.
      intros. hnf. repeat split; auto. exists (-(1))%A. split.
      apply gt0_iff_neg. apply lt_0_1.
      (* Note that, this is not true *)
    Abort.
    
    (** a //- b -> b //- a *)
    Lemma vantipara_sym : forall {n} (a b : vec n), a //- b -> b //- a.
    Proof.
      intros. hnf in *. destruct H as [H11 [H12 [x [H13 H14]]]].
      repeat split; auto. exists (/x). split; auto.
      apply inv_lt0; auto.
      rewrite <- H14. rewrite vcmul_assoc. rewrite field_mulInvL; auto.
      apply vcmul_1_l. apply lt_not_eq; auto.
    Qed.

    (** a //- b -> b //- c -> a //- c *)
    Lemma vantipara_trans : forall {n} (a b c: vec n), a //- b -> b //- c -> a //- c.
    Proof.
      intros. hnf in *.
      destruct H as [H11 [H12 [x1 [H13 H14]]]].
      destruct H0 as [H21 [H22 [x2 [H23 H24]]]].
      repeat split; auto. exists (x2 * x1). split.
      2:{ rewrite <- H24, <- H14. rewrite vcmul_assoc. auto. }
      (* Note that, this is not true *)
    Abort.

    (** a //- b => ∃! x, x < 0 /\ x .* a = b *)
    Lemma vantipara_imply_uniqueX : forall {n} (a b : vec n),
        a //- b -> (exists ! x, x < 0 /\ x \.* a = b).
    Proof.
      intros. destruct H as [H1 [H2 [x [H3 H4]]]]. exists x. split; auto.
      intros j [H5 H6]. rewrite <- H4 in H6.
      apply vcmul_sameV_imply_eqX in H6; auto.
    Qed.

    (** a //- b -> (x .* a) //- b *)
    Lemma vantipara_vcmul_l : forall {n} x (a b : vec n),
        0 < x -> a //- b -> x \.* a //- b.
    Proof.
      intros. hnf in *. destruct H0 as [H1 [H2 [x1 [H3 H4]]]].
      repeat split; auto.
      - intro. apply vcmul_eq0_imply_x0_or_v0 in H0. destruct H0; auto.
        apply lt_not_eq in H. rewrite H0 in H. easy.
      - exists (x1/x); simpl. split.
        + apply mul_lt0_if_lt0_gt0; auto. apply inv_gt0; auto.
        + rewrite <- H4. rewrite vcmul_assoc. f_equal. field.
          symmetry. apply lt_not_eq. auto.
    Qed.

    (** a //- b -> a //- (x .* b) *)
    Lemma vantipara_vcmul_r : forall {n} x (a b : vec n),
        0 < x -> a //- b -> a //- (x \.* b).
    Proof.
      intros. apply vantipara_sym in H0. apply vantipara_sym.
      apply vantipara_vcmul_l; auto.
    Qed.
    
  End vantipara.
  
  Infix "//" := vcoll : vec_scope.
  Infix "//+" := vpara : vec_scope.
  Infix "//-" := vantipara : vec_scope.

  
  (** *** Convert between //, //+, and //-  *)
  Section convert.
    
    (** a //+ b -> a // b *)
    Lemma vpara_imply_vcoll : forall {n} (a b : vec n), a //+ b -> a // b.
    Proof.
      intros. hnf in *. destruct H as [H11 [H12 [x [H13 H14]]]].
      repeat split; auto. exists x. split; auto. symmetry. apply lt_imply_neq; auto.
    Qed.
    
    (** a //- b -> a // b *)
    Lemma vantipara_imply_vcoll : forall {n} (a b : vec n), a //- b -> a // b.
    Proof.
      intros. hnf in *. destruct H as [H11 [H12 [x [H13 H14]]]].
      repeat split; auto. exists x. split; auto. apply lt_imply_neq; auto.
    Qed.
    
    (** a //+ b -> (-a) //- b *)
    Lemma vpara_imply_vantipara_opp_l : forall {n} (a b : vec n), a //+ b -> (-a) //- b.
    Proof.
      intros. hnf in *. destruct H as [H11 [H12 [x [H13 H14]]]].
      repeat split; auto. apply group_opp_neq0_iff; auto.
      exists (- x)%A. split. apply gt0_iff_neg; auto.
      rewrite vcmul_opp, vcmul_vopp, <- H14. rewrite vopp_vopp. auto.
    Qed.
    
    (** a //+ b -> a //- (-b)*)
    Lemma vpara_imply_vantipara_opp_r : forall {n} (a b : vec n), a //+ b -> a //- (-b).
    Proof.
      intros. hnf in *. destruct H as [H11 [H12 [x [H13 H14]]]].
      repeat split; auto. apply group_opp_neq0_iff; auto.
      exists (- x)%A. split. apply gt0_iff_neg; auto.
      rewrite vcmul_opp. rewrite H14. auto.
    Qed.
    
    (** a // b -> (a //+ b) \/ (a //- b) *)
    Lemma vpara_imply_vpara_or_vantipara : forall {n} (a b : vec n),
        a // b -> a //+ b \/ a //- b.
    Proof.
      intros. hnf in *. destruct H as [H11 [H12 [x [H13 H14]]]].
      destruct (lt_cases x 0) as [[Hlt|Hgt]|Heq0].
      - right. hnf. repeat split; auto. exists x; auto.
      - left. hnf. repeat split; auto. exists x; auto.
      - easy.
    Qed.
    
  End convert.

End vcoll_vpara_vantipara.
