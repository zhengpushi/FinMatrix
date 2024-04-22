(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix module
  author    : ZhengPu Shi
  date      : 2023.04

  remark    :
  1. use functor to generate many similiar modules, and help the type inference
     at specify domain, so that simplify the coding.
  2. Vector theory is contained in matrix theory, we simply called matrix.
     Note that, an old version has splitted the `vectorModule` and `matrixModule`,
     but later, I found that the `matrixModule` won't reuse the definitions in
     `vectorModule`, making a waste.
  3. The matrix theory is orgainized at several levels
  * BasicMatrixTheory: matrix theory over ElementType.
  * MonoidMatrixTheory, matrix theory over MonoidElementType.
  * RingMatrixTheory: matrix theory over RingElementType.
  * OrderedRingMatrixTheory: `RingMatrixTheory` with order relation.
  * FieldMatrixTheory: matrix theory over FieldElementType.
  * OrderedFieldMatrixTheory, `FieldMatrixTheory` with order relation.
  * NormedOrderedFieldMatrixTheory, `OrderedFieldMatrixTheory` with norm.
 *)


Require Export Matrix.
Require Export MatrixDet.
Require Export MatrixInv.
Require Export MatrixOrth.
Require Export ElementType.


(* ######################################################################### *)
(** * Basic matrix theory *)
Module BasicMatrixTheory (E : ElementType).

  (** import element *)
  Export E.

  (** default scope *)
  Open Scope nat_scope.
  Open Scope A_scope.
  Open Scope vec_scope.

  (* ======================================================================= *)
  (** ** Definition of the vector type *)
  
  (** vector type *)
  Definition vec (n : nat) := @vec A n.
  
  (* ======================================================================= *)
  (** ** Equalities of the vector *)
  
  (** veq is decidable *)
  #[export] Instance veq_dec : forall {n}, Dec (@eq (vec n)).
  Proof. intros. apply veq_dec. Qed.
  
  (** Two vectors are equal, iff, element-wise equal *)
  Lemma veq_iff_vnth : forall {n} (a b : vec n), a = b <-> (forall i, a.[i] = b.[i]).
  Proof. intros. apply veq_iff_vnth. Qed.

  (** Two vectors are not equal, iff, exist one element-wise not equal *)
  Lemma vneq_iff_exist_vnth_neq : forall {n} (a b : vec n), a <> b <-> exists i, a.[i] <> b.[i].
  Proof. intros. apply vneq_iff_exist_vnth_neq. Qed.

  (** Any two 0-D vectors are equal *)
  Lemma v0eq : forall (a b : vec 0), a = b.
  Proof. apply v0eq. Qed.

  (** No two 0-D vectors are unequal *)
  Lemma v0neq : forall (a b : vec 0), a <> b -> False.
  Proof. apply v0neq. Qed.

  (** The equality of 1-D, 2-D, ... vectors *)
  Section veq.
    Lemma v1eq_iff : forall (a b : vec 1), a = b <-> a.1 = b.1.
    Proof. apply v1eq_iff. Qed.

    Lemma v1neq_iff : forall (a b : vec 1), a <> b <-> a.1 <> b.1.
    Proof. apply v1neq_iff. Qed.

    Lemma v2eq_iff : forall (a b : vec 2), a = b <-> a.1 = b.1 /\ a.2 = b.2.
    Proof. apply v2eq_iff. Qed.

    Lemma v2neq_iff : forall (a b : vec 2), a <> b <-> (a.1 <> b.1 \/ a.2 <> b.2).
    Proof. apply v2neq_iff. Qed.

    Lemma v3eq_iff : forall (a b : vec 3),
        a = b <-> a.1 = b.1 /\ a.2 = b.2 /\ a.3 = b.3.
    Proof. apply v3eq_iff. Qed.

    Lemma v3neq_iff : forall (a b : vec 3),
        a <> b <-> (a.1 <> b.1 \/ a.2 <> b.2 \/ a.3 <> b.3).
    Proof. apply v3neq_iff. Qed.

    Lemma v4eq_iff : forall (a b : vec 4),
        a = b <-> a.1 = b.1 /\ a.2 = b.2 /\ a.3 = b.3 /\ a.4 = b.4.
    Proof. apply v4eq_iff. Qed.

    Lemma v4neq_iff : forall (a b : vec 4),
        a <> b <-> (a.1 <> b.1 \/ a.2 <> b.2 \/ a.3 <> b.3 \/ a.4 <> b.4).
    Proof. apply v4neq_iff. Qed.
  End veq.

  (* ======================================================================= *)
  (** ** Convert between vector and function *)
  Definition v2f {n} (a : vec n) : nat -> A := v2f 0 a.
  Definition f2v {n} (f : nat -> A) : vec n := f2v f.

  (** (f2v a).i = a i *)
  Lemma vnth_f2v : forall {n} f i, (@f2v n f).[i] = f (fin2nat i).
  Proof. intros. apply vnth_f2v. Qed.

  Lemma f2v_inj : forall {n} (f g : nat -> A),
      @f2v n f = @f2v n g -> (forall i, i < n -> f i = g i).
  Proof. intros. apply (@f2v_inj _ n); auto. Qed.

  (** (v2f a) i = a.i *)
  Lemma nth_v2f : forall {n} (a : vec n) i (H:i<n), (v2f a) i = a.[Fin i H].
  Proof. intros. apply nth_v2f. Qed.

  Lemma v2f_inj : forall {n} (a b : vec n),
      (forall i, i < n -> (v2f a) i = (v2f b) i) -> a = b.
  Proof. intros. apply (v2f_inj 0); auto. Qed.

  (** f2v (v2f a) = a *)
  Lemma f2v_v2f : forall {n} (a : vec n), (@f2v n (v2f a)) = a.
  Proof. intros. apply f2v_v2f. Qed.

  (** v2f (f2v a) = a *)
  Lemma v2f_f2v : forall {n} (a : nat -> A) i, i < n -> v2f (@f2v n a) i = a i.
  Proof. intros. apply v2f_f2v; auto. Qed.

  (* ======================================================================= *)
  (** ** Convert between vector and list *)
  Definition v2l {n} (a : vec n) : list A := v2l a.
  Definition l2v {n} (l : list A) : vec n := l2v 0 l.

  (** (l2v l).i = nth i l *)
  Lemma vnth_l2v : forall {n} (l : list A) i, (@l2v n l).[i] = nth (fin2nat i) l 0.
  Proof. intros. apply vnth_l2v. Qed.
    
  (** nth i (v2l v) = v.i *)
  Lemma nth_v2l : forall {n} (a : vec n) (i : nat) (H: i < n),
      i < n -> nth i (v2l a) 0 = a (nat2fin i H).
  Proof. intros. apply nth_v2l; auto. Qed.
  
  Lemma v2l_length : forall {n} (a : vec n), length (v2l a) = n.
  Proof. intros. apply v2l_length. Qed.

  Lemma v2l_l2v : forall {n} (l : list A), length l = n -> (v2l (@l2v n l) = l).
  Proof. intros. apply v2l_l2v; auto. Qed.

  Lemma l2v_v2l : forall {n} (a : vec n), @l2v n (v2l a) = a.
  Proof. intros. apply l2v_v2l. Qed.

  Lemma v2l_inj : forall {n} (a b : vec n), v2l a = v2l b -> a = b.
  Proof. intros. apply v2l_inj; auto. Qed.

  (* ======================================================================= *)
  (** ** Make concrete vector *)
  Definition mkvec1 (a1 : A) : vec 1 := mkvec1 (Azero:=0) a1.
  Definition mkvec2 (a1 a2 : A) : vec 2 := mkvec2 (Azero:=0) a1 a2.
  Definition mkvec3 (a1 a2 a3 : A) : vec 3 := mkvec3 (Azero:=0) a1 a2 a3.
  Definition mkvec4 (a1 a2 a3 a4 : A) : vec 4 := mkvec4 (Azero:=0) a1 a2 a3 a4.
  
  (* ======================================================================= *)
  (** ** Mapping of vector *)
  
  Definition vmap {n} (f : A -> A) (a : vec n) : vec n := vmap f a.
  Definition vmap2 {n} (f : A -> A -> A) (a b : vec n) : vec n := vmap2 f a b.
  
  (** (vmap f a).i = f (a.i) *)
  Lemma vnth_vmap : forall {n} (a : vec n) f i, (vmap f a).[i] = f (a.[i]).
  Proof. intros. apply vnth_vmap. Qed.

  (** (vmap2 f a b).i = f (a.i) (b.i) *)
  Lemma vnth_vmap2 : forall {n} (a b : vec n) f i, (vmap2 f a b).[i] = f a.[i] b.[i].
  Proof. intros. apply vnth_vmap2. Qed.

  (** vmap2 f a b = vmap id (fun i => f u.i v.i) *)
  Lemma vmap2_eq_vmap : forall {n} (a b : vec n) f,
      vmap2 f a b = vmap (fun a => a) (fun i => f a.[i] b.[i]).
  Proof. intros. apply vmap2_eq_vmap. Qed.

  (* ======================================================================= *)
  (** ** Constant vector and zero vector *)

  (** Vector with same elements *)
  Definition vrepeat n (a : A) : vec n := vrepeat a.

  (** (repeat a).i = a *)
  Lemma vnth_vrepeat : forall {n} a i, (vrepeat n a).[i] = a.
  Proof. intros. apply vnth_vrepeat. Qed.

  (** Make a zero vector *)
  Definition vzero {n} : vec n := vzero 0.

  (** vzero.i = 0 *)
  Lemma vnth_vzero : forall {n} i, (@vzero n).[i] = 0.
  Proof. intros. apply vnth_vzero. Qed.

  (* ======================================================================= *)
  (** ** Set element of a vector *)

  (** Set i-th element vector `a` with `x` *)
  Definition vset {n} (a : vec n) (i : fin n) (x : A) : vec n := vset a i x.

  (** (vset a i x).i = x *)
  Lemma vnth_vset_eq : forall {n} (a : vec n) (i : fin n) (x : A), (vset a i x).[i] = x.
  Proof. intros. apply vnth_vset_eq. Qed.
  
  (** (vset a i x).j = a.[j] *)
  Lemma vnth_vset_neq : forall {n} (a : vec n) (i j : fin n) (x : A),
      i <> j -> (vset a i x).[j] = a.[j].
  Proof. intros. apply vnth_vset_neq; auto. Qed.

  (* ======================================================================= *)
  (** ** Swap two element of a vector *)
  
  (** Swap the i-th and j-th element of vector `a` *)
  Definition vswap {n} (a : vec n) (i j : fin n) : vec n := vswap a i j.

  Lemma vnth_vswap_i : forall {n} (a : vec n) (i j : fin n), (vswap a i j).[i] = a.[j].
  Proof. intros. apply vnth_vswap_i. Qed.

  Lemma vnth_vswap_j : forall {n} (a : vec n) (i j : fin n), (vswap a i j).[j] = a.[i].
  Proof. intros. apply vnth_vswap_j. Qed.

  Lemma vnth_vswap_other : forall {n} (a : vec n) (i j k : fin n),
      i <> k -> j <> k -> (vswap a i j).[k] = a.[k].
  Proof. intros. apply vnth_vswap_other; auto. Qed.

  Lemma vswap_vswap : forall {n} (a : vec n) (i j : fin n), vswap (vswap a i j) j i = a.
  Proof. intros. apply vswap_vswap. Qed.

  (* ======================================================================= *)
  (** ** Insert element to a vector *)

  Definition vinsert {n} (a : vec n) (i : fin (S n)) (x : A) : vec (S n) :=
    vinsert a i x.

  (** j < i -> (v2f (vinsert a i x)) j = (v2f a) i *)
  Lemma vinsert_spec_lt : forall {n} (a : vec n) (i : fin (S n)) (x : A) (j : nat),
      j < fin2nat i -> v2f (vinsert a i x) j = v2f a j.
  Proof. intros. apply vinsert_spec_lt; auto. Qed.

  (** j = i -> (v2f (vinsert a i x)) j = x *)
  Lemma vinsert_spec_eq : forall {n} (a : vec n) (i : fin (S n)) (x : A),
      v2f (vinsert a i x) (fin2nat i) = x.
  Proof. intros. apply vinsert_spec_eq; auto. Qed.
  
  (** i < j -> j <= n -> (v2f (vinsert a i x)) j = (v2f a) (S i) *)
  Lemma vinsert_spec_gt : forall {n} (a : vec n) (i : fin (S n)) (x : A) (j : nat),
      fin2nat i < j -> 0 < j -> j < S n -> v2f (vinsert a i x) j = v2f a (pred j).
  Proof. intros. apply vinsert_spec_gt; auto. Qed.

  (** j < i -> (vinsert a i x).[j] = a.[j] *)
  Lemma vnth_vinsert_lt :
    forall {n} (a : vec n) (i j : fin (S n)) x (H : fin2nat j < fin2nat i),
      (vinsert a i x).[j] = a.[fin2PredRange j (nat_lt_ltS_lt _ _ _ H (fin2nat_lt _))].
  Proof. intros. apply (@vnth_vinsert_lt _ 0); auto. Qed.

  (** (vinsert a i x).i = a *)
  Lemma vnth_vinsert_eq : forall {n} (a : vec n) (i : fin (S n)) x,
      (vinsert a i x).[i] = x.
  Proof. intros. apply (@vnth_vinsert_eq _ 0). Qed.

  (** 0 < j -> (vinsert a i x).[j] = a.(pred j) *)
  Lemma vnth_vinsert_gt :
    forall {n} (a : vec n) (i j : fin (S n)) x (H : 0 < fin2nat j),
      fin2nat i < fin2nat j -> (vinsert a i x).[j] = a.[fin2PredRangePred j H].
  Proof. intros. apply (@vnth_vinsert_gt _ 0); auto. Qed.

  (** Invert 0 into vzero get vzero *)
  Lemma vinsert_vzero_eq0 : forall {n} i, @vinsert n vzero i 0 = vzero.
  Proof. intros. apply vinsert_vzero_eq0. Qed.

  (** If insert x into vector a get vzero, then x is 0 *)
  Lemma vinsert_eq0_imply_x0 : forall {n} (a : vec n) i x,
      vinsert a i x = vzero -> x = 0.
  Proof. intros. apply (vinsert_eq0_imply_x0 a i x H). Qed.

  (** If insert x into vector _a_ get vzero, then _a_ is vzero *)
  Lemma vinsert_eq0_imply_v0 : forall {n} (a : vec n) i x,
      vinsert a i x = vzero -> a = vzero.
  Proof. intros. apply (vinsert_eq0_imply_v0 a i x H). Qed.

  (** Insert x into vector _a_ get vzero, iff _a_ is vzero and _x_ is 0 *)
  Lemma vinsert_eq0_iff : forall {n} (a : vec n) i x,
      vinsert a i x = vzero <-> (a = vzero /\ x = 0).
  Proof. intros. apply vinsert_eq0_iff. Qed.

  (** Insert x into vector _a_ is not vzero, iff _a_ is not vzero or _x_ is 0 *)
  Lemma vinsert_neq0_iff : forall {n} (a : vec n) i x,
      vinsert a i x <> vzero <-> (a <> vzero \/ x <> 0).
  Proof. intros. apply vinsert_neq0_iff. Qed.


  (* ======================================================================= *)
  (** ** Remove one element *)

  (** Removes i-th element from vector `a` *)
  Definition vremove {n} (a : vec (S n)) (i : fin (S n)) : vec n := vremove a i.

  (** j < i -> (v2f (vremove a i)) j = (v2f a) j *)
  Lemma vremove_spec_lt : forall {n} (a : vec (S n)) (i : fin (S n)) (j : nat),
      j < fin2nat i -> v2f (vremove a i) j = v2f a j.
  Proof. intros. apply vremove_spec_lt; auto. Qed.

  (** i <= j -> j < n -> (v2f (vremove a i)) j = (v2f a) (S j) *)
  Lemma vremove_spec_ge : forall {n} (a : vec (S n)) (i : fin (S n)) (j : nat),
      fin2nat i <= j -> j < n -> v2f (vremove a i) j = v2f a (S j).
  Proof. intros. apply vremove_spec_ge; auto. Qed.

  (** j < i -> (vremove a i).[j] = a.[j] *)
  Lemma vnth_vremove_lt : forall {n} (a : vec (S n)) (i : fin (S n)) (j : fin n),
      fin2nat j < fin2nat i -> (vremove a i).[j] = v2f a (fin2nat j).
  Proof. intros. apply vnth_vremove_lt; auto. Qed.
  
  (** i <= j -> j < n -> (vremove a i).j = a.(S j) *)
  Lemma vnth_vremove_ge : forall {n} (a : vec (S n)) (i : fin (S n)) (j : fin n),
      fin2nat i <= fin2nat j -> fin2nat j < n ->
      (vremove a i).[j] = v2f a (S (fin2nat j)).
  Proof. intros. apply vnth_vremove_ge; auto. Qed.

  (** vremove (vinsert a i x) i = a *)
  Lemma vremove_vinsert : forall {n} (a : vec n) (i : fin (S n)) (x : A),
      vremove (vinsert a i x) i = a.
  Proof. intros. apply (@vremove_vinsert _ 0). Qed.
  
  (** vinsert (vremove a i) (a.[i]) = a *)
  Lemma vinsert_vremove : forall {n} (a : vec (S n)) (i : fin (S n)),
      vinsert (vremove a i) i (a.[i]) = a.
  Proof. intros. apply (@vinsert_vremove _ 0). Qed.

  (** vmap f (vremove a i) = vremove (vmap f v) i *)
  Lemma vmap_vremove : forall {n} (a : vec (S n)) f i,
      vmap f (vremove a i) = vremove (vmap f a) i.
  Proof. intros. apply (@vmap_vremove _ _ 0 0). Qed.

  (** vmap2 f (vremove a i) (vremove b i) = vremove (vmap2 a b) i *)
  Lemma vmap2_vremove_vremove : forall {n} (a b : vec (S n)) f i,
      vmap2 f (vremove a i) (vremove b i) = vremove (vmap2 f a b) i.
  Proof. intros. apply (@vmap2_vremove_vremove _ _ _ 0 0 0). Qed.

  (* ======================================================================= *)
  (** ** Get head or tail element *)

  (** Get head element *)
  Definition vhead {n} (a : vec (S n)) : A := vhead a.
  
  (** Get tail element *)
  Definition vtail {n} (a : vec (S n)) : A := a.[#n].

  (** vhead a = (v2f a) 0 *)
  Lemma vhead_spec : forall {n} (a : vec (S n)), vhead a = (v2f a) 0.
  Proof. intros. apply vhead_spec. Qed.

  (** vhead a = a.[0] *)
  Lemma vhead_eq : forall {n} (a : vec (S n)), vhead a = a.[fin0].
  Proof. intros. apply vhead_eq. Qed.

  (** vtail a = a.(n - 1) *)
  Lemma vtail_spec : forall {n} (a : vec (S n)), vtail a = (v2f a) n.
  Proof. intros. apply vtail_spec. Qed.

  (** vtail a = a $ (n - 1) *)
  Lemma vtail_eq : forall {n} (a : vec (S n)), vtail a = a.[#n].
  Proof. intros. apply vtail_eq. Qed.

  (* ======================================================================= *)
  (** ** Get head or tail elements *)

  (** Get head elements *)
  Definition vheadN {m n} (a : vec (m + n)) : vec m := vheadN a.

  (** Get tail elements *)
  Definition vtailN {m n} (a : vec (m + n)) : vec n := vtailN a.

  (** i < m -> (vheadN a).i = (v2f a).i *)
  Lemma vheadN_spec : forall {m n} (a : vec (m + n)) i,
      i < m -> v2f (vheadN a) i = (v2f a) i.
  Proof. intros. apply vheadN_spec; auto. Qed.

  (** (vheadN a).i = a.i *)
  Lemma vnth_vheadN : forall {m n} (a : vec (m + n)) i,
      (vheadN a).[i] = a.[fin2AddRangeR i].
  Proof. intros. apply vnth_vheadN. Qed.

  (** i < n -> (vtailN a).i = (v2f a).(m + i) *)
  Lemma vtailN_spec : forall {m n} (a : vec (m + n)) i,
      i < n -> v2f (vtailN a) i = (v2f a) (m + i).
  Proof. intros. apply vtailN_spec; auto. Qed.

  (** (vtailN a).i = a.(n + i) *)
  Lemma vnth_vtailN : forall {m n} (a : vec (m + n)) i,
      (vtailN a).[i] = a.[fin2AddRangeAddL i].
  Proof. intros. apply vnth_vtailN. Qed.

  (* ======================================================================= *)
  (** ** Remove exact one element at head or tail *)

  (** Remove head element *)
  Definition vremoveH {n} (a : vec (S n)) : vec n := vremoveH a.

  (** Remove tail element *)
  Definition vremoveT {n} (a : vec (S n)) : vec n := vremoveT a.

  (** i < n -> (vremoveH a).i = v.(S i) *)
  Lemma vremoveH_spec : forall {n} (a : vec (S n)) (i : nat),
      i < n -> v2f (vremoveH a) i = v2f a (S i).
  Proof. intros. apply vremoveH_spec; auto. Qed.
  
  (** (vremoveH a).i = a.(S i) *)
  Lemma vnth_vremoveH : forall {n} (a : vec (S n)) (i : fin n),
      (vremoveH a).[i] = a.[fin2SuccRangeSucc i].
  Proof. intros. apply vnth_vremoveH; auto. Qed.
  
  (** a <> 0 -> vhead a = 0 -> vremoveH a <> 0 *)
  Lemma vremoveH_neq0_if : forall {n} (a : vec (S n)),
      a <> vzero -> vhead a = 0 -> vremoveH a <> vzero.
  Proof. intros. apply vremoveH_neq0_if; auto. Qed.

  (** vremoveH also hold, if hold for all elements *)
  Lemma vremoveH_hold : forall {n} (a : vec (S n)) (P : A -> Prop),
      (forall i, P (a.[i])) -> (forall i, P ((vremoveH a).[i])).
  Proof. intros. apply vremoveH_hold; auto. Qed.

  (** i < n -> (vremoveT a).i = a.i *)
  Lemma vremoveT_spec : forall {n} (a : vec (S n)) (i : nat),
      i < n -> v2f (vremoveT a) i = v2f a i.
  Proof. intros. apply vremoveT_spec; auto. Qed.
  
  (** (vremoveT a).i = a.i *)
  Lemma vnth_vremoveT : forall {n} (a : vec (S n)) (i : fin n),
      (vremoveT a).[i] = a.[fin2SuccRange i].
  Proof. intros. apply vnth_vremoveT; auto. Qed.
  
  (** v <> 0 -> vtail v = 0 -> vremoveT v <> 0 *)
  Lemma vremoveT_neq0_if : forall {n} (a : vec (S n)),
      a <> vzero -> vtail a = 0 -> vremoveT a <> vzero.
  Proof. intros. apply vremoveT_neq0_if; auto. Qed.

  (** vremoveT also hold, if hold for all elements *)
  Lemma vremoveT_hold : forall {n} (a : vec (S n)) (P : A -> Prop),
      (forall i, P (a.[i])) -> (forall i, P ((vremoveT a).[i])).
  Proof. intros. apply vremoveT_hold; auto. Qed.

  (* ======================================================================= *)
  (** ** Remove some elements at head or tail *)

  (** Remove some head elements *)
  Definition vremoveHN {m n} (a : vec (m + n)) : vec n := vremoveHN a.
  
  (** Remove some tail elements *)
  Definition vremoveTN {m n} (a : vec (m + n)) : vec m := vremoveTN a.

  (** i < n -> (vremoveHN a).i = a.(m + i) *)
  Lemma vremoveHN_spec : forall {m n} (a : vec (m + n)) (i : nat),
      i < n -> v2f (vremoveHN a) i = v2f a (m + i).
  Proof. intros. apply vremoveHN_spec; auto. Qed.
  
  (** (vremoveHN a).i = a.(m + i) *)
  Lemma vnth_vremoveHN : forall {m n} (a : vec (m + n)) (i : fin n),
      (vremoveHN a).[i] = a.[fin2AddRangeAddL i].
  Proof. intros. apply vnth_vremoveHN; auto. Qed.
  
  (** a <> 0 -> vheadN v = 0 -> vremoveHN a <> 0 *)
  Lemma vremoveHN_neq0_if : forall {m n} (a : vec (m + n)),
      a <> vzero -> vheadN a = vzero -> vremoveHN a <> vzero.
  Proof. intros. apply vremoveHN_neq0_if; auto. Qed.

  (** i < n -> (vremoveTN a).i = a.i *)
  Lemma vremoveTN_spec : forall {m n} (a : vec (m + n)) (i : nat),
      i < m -> v2f (vremoveTN a) i = v2f a i.
  Proof. intros. apply vremoveTN_spec; auto. Qed.
  
  (** (vremoveTN a).i = a.i *)
  Lemma vnth_vremoveTN : forall {m n} (a : vec (m + n)) (i : fin m),
      (vremoveTN a).[i] = a.[fin2AddRangeR i].
  Proof. intros. apply vnth_vremoveTN; auto. Qed.
  
  (** a <> 0 -> vtailN v = 0 -> vremoveTN a <> 0 *)
  Lemma vremoveTN_neq0_if : forall {m n} (a : vec (m + n)),
      a <> vzero -> vtailN a = vzero -> vremoveTN a <> vzero.
  Proof. intros. apply vremoveTN_neq0_if; auto. Qed.

  (* ======================================================================= *)
  (** ** Construct vector with one element at the head or tail position *)

  (** cons at head: [x; a] *)
  Definition vconsH {n} (x : A) (a : vec n) : vec (S n) := vconsH x a.

  (** cons at tail: [a; x] *)
  Definition vconsT {n} (a : vec n) (x : A) : vec (S n) := vconsT a x.

  (** i = 0 -> (v2f [x; a]) i = a *)
  Lemma vconsH_spec_0 : forall {n} x (a : vec n) (i : nat),
      i = 0%nat -> v2f (vconsH x a) i = x.
  Proof. intros. apply vconsH_spec_0; auto. Qed.

  (** 0 < i -> i < n -> [x; a].i = a.(pred i) *)
  Lemma vconsH_spec_gt0 : forall {n} x (a : vec n) (i : nat),
      0 < i -> i < n -> v2f (vconsH x a) i = v2f a (pred i).
  Proof. intros. apply vconsH_spec_gt0; auto. Qed.

  (** i = 0 -> [x; a].i = a *)
  Lemma vnth_vconsH_0 : forall {n} x (a : vec n) i,
      i = fin0 -> (vconsH x a).[i] = x.
  Proof. intros. apply vnth_vconsH_0; auto. Qed.
  
  (** 0 < i -> [x; a].i = a.(pred i)  *)
  Lemma vnth_vconsH_gt0 : forall {n} x (a : vec n) i (H: 0 < fin2nat i),
      (vconsH x a).[i] = a.[fin2PredRangePred i H].
  Proof. intros. apply vnth_vconsH_gt0; auto. Qed.

  (** [x; a] = 0 <-> x = 0 /\ v = 0 *)
  Lemma vconsH_eq0_iff : forall {n} x (a : vec n),
      vconsH x a = vzero <-> x = 0 /\ a = vzero.
  Proof. intros. apply vconsH_eq0_iff; auto. Qed.
  
  (** [x; a] <> 0 <-> x <> 0 \/ a <> 0 *)
  Lemma vconsH_neq0_iff : forall {n} x (a : vec n),
      vconsH x a <> vzero <-> x <> 0 \/ a <> vzero.
  Proof. intros. apply vconsH_neq0_iff; auto. Qed.

  (** vconsH (vhead a) (vremoveH a) = a *)
  Lemma vconsH_vhead_vremoveH : forall {n} (a : vec (S n)),
      vconsH (vhead a) (vremoveH a) = a.
  Proof. intros. apply vconsH_vhead_vremoveH; auto. Qed.

  (** vremoveH (vconsH a x) = a *)
  Lemma vremoveH_vconsH : forall {n} x (a : vec n), vremoveH (vconsH x a) = a.
  Proof. intros. apply vremoveH_vconsH; auto. Qed.
  
  (** vhead (vconsH a x) = x *)
  Lemma vhead_vconsH : forall {n} (a : vec n) x, vhead (vconsH x a) = x.
  Proof. intros. apply vhead_vconsH; auto. Qed.

  (** [0; vzero] = vzero *)
  Lemma vconsH_0_vzero : forall {n}, @vconsH n 0 vzero = vzero.
  Proof. intros. apply vconsH_0_vzero; auto. Qed.
  
  (** i = n -> (v2f [a; x]) i = a *)
  Lemma vconsT_spec_n : forall {n} x (a : vec n) (i : nat),
      i = n -> v2f (vconsT a x) i = x.
  Proof. intros. apply vconsT_spec_n; auto. Qed.

  (** i < n -> (v2f [a; x]) i = a.(pred i) *)
  Lemma vconsT_spec_lt : forall {n} x (a : vec n) (i : nat),
      i < n -> v2f (vconsT a x) i = v2f a i.
  Proof. intros. apply vconsT_spec_lt; auto. Qed.

  (** i = n -> [a; x].i = a *)
  Lemma vnth_vconsT_n : forall {n} x (a : vec n) i,
      fin2nat i = n -> (vconsT a x).[i] = x.
  Proof. intros. apply vnth_vconsT_n; auto. Qed.

  (** i < n -> [a; x].i = a.(pred i) *)
  Lemma vnth_vconsT_lt : forall {n} x (a : vec n) i (H: fin2nat i < n),
      (vconsT a x).[i] = a (fin2PredRange i H).
  Proof. intros. apply vnth_vconsT_lt; auto. Qed.

  (** [a; x] = 0 <-> a = 0 /\ x = 0*)
  Lemma vconsT_eq0_iff : forall {n} (a : vec n) x,
      vconsT a x = vzero <-> a = vzero /\ x = 0.
  Proof. intros. apply vconsT_eq0_iff; auto. Qed.
  
  (** [a; x] <> 0 <-> a <> 0 \/ x <> 0*)
  Lemma vconsT_neq0_iff : forall {n} (a : vec n) x,
      vconsT a x <> vzero <-> a <> vzero \/ x <> 0.
  Proof. intros. apply vconsT_neq0_iff; auto. Qed.

  (** vconsT (vremoveT a) (vtail a) = a *)
  Lemma vconsT_vremoveT_vtail : forall {n} (a : vec (S n)),
      vconsT (vremoveT a) (vtail a) = a.
  Proof. intros. apply vconsT_vremoveT_vtail; auto. Qed.

  (** vremoveT (vconsT a x) = a *)
  Lemma vremoveT_vconsT : forall {n} (a : vec n) x, vremoveT (vconsT a x) = a.
  Proof. intros. apply vremoveT_vconsT; auto. Qed.

  (** vtail (vconsT a x) = x *)
  Lemma vtail_vconsT : forall {n} (a : vec n) x, vtail (vconsT a x) = x.
  Proof. intros. apply vtail_vconsT; auto. Qed.

  (** [vzero; 0] = vzero *)
  Lemma vconsT_vzero_eq0 : forall {n}, @vconsT n vzero Azero = vzero.
  Proof. intros. apply vconsT_vzero_eq0; auto. Qed.

  (* ======================================================================= *)
  (** ** Construct vector with two vectors *)

  (** Append two vectors, denoted with a@b *)
  Definition vapp {m n} (a : vec m) (b : vec n) : vec (m + n) := vapp a b.
  
  (** i < m -> a@b.i = u.i *)
  Lemma vapp_spec_L : forall {m n} (a : vec m) (b : vec n) (i : nat),
      i < m -> v2f (vapp a b) i = v2f a i.
  Proof. intros. apply vapp_spec_L; auto. Qed.
  
  (** m <= i -> i < m + n -> a&b.i = a.(i - m) *)
  Lemma vapp_spec_R : forall {m n} (a : vec m) (b : vec n) (i : nat),
      m <= i -> i < m + n -> v2f (vapp a b) i = v2f b (i - m).
  Proof. intros. apply vapp_spec_R; auto. Qed.
  
  (** i < m -> a&b.i = a.i *)
  Lemma vnth_vapp_L : forall {m n} (a : vec m) (b : vec n) i (H: fin2nat i < m),
      (vapp a b).[i] = a.[fin2AddRangeR' i H].
  Proof. intros. apply vnth_vapp_L. Qed.
  
  (** m <= i -> a&b.i = b.i *)
  Lemma vnth_vapp_R : forall {m n} (a : vec m) (b : vec n) i (H : m <= fin2nat i),
      (vapp a b).[i] = b.[fin2AddRangeAddL' i H].
  Proof. intros. apply vnth_vapp_R. Qed.

  (** a@b = 0 <-> a = 0 /\ b = 0 *)
  Lemma vapp_eq0_iff : forall {m n} (a : vec m) (b : vec n),
      vapp a b = vzero <-> a = vzero /\ b = vzero.
  Proof. intros. apply vapp_eq0_iff; auto. Qed.
  
  (** vapp (vheadN a) (vtailN a) = a *)
  Lemma vapp_vheadN_vtailN : forall {m n} (a : vec (m + n)),
      vapp (vheadN a) (vtailN a) = a.
  Proof. intros. apply vapp_vheadN_vtailN; auto. Qed.

  (* ======================================================================= *)
  (** ** A proposition which all elements of the vector hold *)

  (** Every element of `a` satisfy the `P` *)
  Definition vforall {n} (a : vec n) (P : A -> Prop) : Prop := vforall a P.

  (* ======================================================================= *)
  (** ** A proposition which at least one element of the vector holds *)

  (** There exist element of `v` satisfy the `P` *)
  Definition vexist {n} (a : vec n) (P : A -> Prop) : Prop := vexist a P.

  (* ======================================================================= *)
  (** ** An element belongs to the vector *)

  (** x ∈ a : Element `x` belongs to the vector `a` *)
  Definition vmem {n} (a : vec n) (x : A) : Prop := vmem a x.

  Lemma vmem_vnth : forall {n} (a : vec n) (i : fin n), vmem a (a.[i]).
  Proof. intros. apply vmem_vnth. Qed.

  (** {x ∈ a} + {x ∉ a} *)
  Lemma vmem_dec : forall {n} (a : vec n) (x : A), {vmem a x} + {~vmem a x}.
  Proof. intros. apply vmem_dec; auto. Qed.
  
  (* ======================================================================= *)
  (** ** An vector belongs to another vector *)

  (** a ⊆ b : Every element of vector `a` belongs to vector `b` *)
  Definition vmems {r s} (a : vec r) (b : vec s) : Prop := vmems a b.

  Lemma vmems_refl : forall {n} (a : vec n), vmems a a.
  Proof. intros. apply vmems_refl. Qed.

  Lemma vmems_trans : forall {r s t} (a : vec r) (b : vec s) (c : vec t),
      vmems a b -> vmems b c -> vmems a c.
  Proof. intros. apply vmems_trans with b; auto. Qed.

  (** {a ⊆ b} + {~(a ⊆ b)} *)
  Lemma vmems_dec : forall {r s} (a : vec r) (b : vec s), {vmems a b} + {~vmems a b}.
  Proof. intros. apply vmems_dec. Qed.
  
  (* ======================================================================= *)
  (** ** Two vectors are equivalent (i.e., contain each other) *)

  (** Two vectors are equivalent (i.e., contain each other) *)
  Definition vequiv {r s} (a : vec r) (b : vec s) : Prop := vequiv a b.

  Lemma vequiv_refl : forall {n} (a : vec n), vequiv a a.
  Proof. intros. apply vequiv_refl. Qed.
  
  Lemma vequiv_syms : forall {r s} (a : vec r) (b : vec s), vequiv a b -> vequiv b a.
  Proof. intros. apply vequiv_syms; auto. Qed.
  
  Lemma vequiv_trans : forall {r s t} (a : vec r) (b : vec s) (c : vec t),
      vequiv a b -> vequiv b c -> vequiv a c.
  Proof. intros. apply vequiv_trans with b; auto. Qed.

  (** {a ∼ b} + {~(a ∼ b)} *)
  Lemma vequiv_dec : forall {r s} (a : vec r) (b : vec s), {vequiv a b} + {~ vequiv a b}.
  Proof. intros. apply vequiv_dec; auto. Qed.

  (* ======================================================================= *)
  (** ** Folding of a vector *)
  (* Context {A B : Type} {Azero : A} {Bzero : B}.  *)

  (** ((x + a.1) + a.2) + ... *)
  Definition vfoldl {B} {n} (a : vec n) (x : B) (f : B -> A -> B) : B :=
    @vfoldl _ _ 0 _ a x f.
  
  (** ... + (v.(n-1) + (v.n + x)) *)
  Definition vfoldr {B} {n} (a : vec n) (x : B) (f : A -> B -> B) : B :=
    @vfoldr _ _ 0 _ a x f.

  (** Convert `vfoldl` to `seqfoldl` *)
  Lemma vfoldl_eq_seqfoldl :
    forall {B} {n} (a : vec n) (x : B) (f : B -> A -> B) (s : nat -> A),
      (forall i, a.[i] = s (fin2nat i)) -> vfoldl a x f = seqfoldl s n x f.
  Proof. intros. apply vfoldl_eq_seqfoldl; auto. Qed.

  (* ======================================================================= *)
  (** ** Automation for vector equality proofs *)

  (** Convert equality of two vectors to point-wise element equalities *)
  Ltac veq :=
    apply v2l_inj; cbv; list_eq.
    
  Open Scope mat_scope.
  
  (* ======================================================================= *)
  (** ** Definition of the matrix type *)
  
  (** matrix type *)
  Definition mat r c : Type := @mat A r c.
  
  (** square matrix type *)
  Notation smat n := (mat n n).

  (** row vector type *)
  Notation rvec n := (mat 1 n).

  (** column vector type *)
  Notation cvec n := (mat n 1).
  
  (* ======================================================================= *)
  (** ** Equalities of the matrix *)

  (** Two matrices are equal, iff, element-wise equal *)
  Lemma meq_iff_mnth : forall {r c : nat} (M N : mat r c),
      M = N <-> (forall i j, M.[i].[j] = N.[i].[j]).
  Proof. intros. apply meq_iff_mnth. Qed.
    
  (** Two matrices are not equal, iff, exist one element-wise not equal *)
  Lemma mneq_iff_exist_mnth_neq : forall {r c} (M N : mat r c),
      M <> N <-> (exists i j, M.[i].[j] <> N.[i].[j]).
  Proof. intros. apply mneq_iff_exist_mnth_neq. Qed.

  (* ======================================================================= *)
  (** ** Convert between cvec and vec *)

  Definition cv2v {n} (M : cvec n) : vec n := cv2v M.
  Definition v2cv {n} (a : vec n) : cvec n := v2cv a.
  
  Lemma cv2v_spec : forall {n} (M : cvec n) i, M.[i].[fin0] = (cv2v M).[i].
  Proof. intros. apply (cv2v_spec M). Qed.

  Lemma v2cv_spec : forall {n} (a : vec n) i, a.[i] = (v2cv a).[i].[fin0].
  Proof. intros. apply v2cv_spec. Qed.
  
  Lemma cv2v_v2cv : forall {n} (a : vec n), cv2v (v2cv a) = a.
  Proof. intros. apply cv2v_v2cv. Qed.
  
  Lemma v2cv_cv2v : forall {n} (M : cvec n), v2cv (cv2v M) = M.
  Proof. intros. apply v2cv_cv2v. Qed.

  Lemma cv2v_inj : forall {n} (M N : cvec n), cv2v M = cv2v N -> M = N.
  Proof. intros. apply cv2v_inj; auto. Qed.
  
  Lemma v2cv_inj : forall {n} (a b : vec n), v2cv a = v2cv b -> a = b.
  Proof. intros. apply v2cv_inj; auto. Qed.

  Lemma vnth_v2cv : forall {n} (a : vec n) i j, (v2cv a).[i].[j]  = a.[i].
  Proof. intros. apply vnth_v2cv. Qed.
  
  (* ======================================================================= *)
  (** ** Convert between rvec and vec *)
  
  Definition rv2v {n} (M : rvec n) : vec n := rv2v M.
  Definition v2rv {n} (a : vec n) : rvec n := v2rv a.

  Lemma rv2v_spec : forall {n} (M : rvec n) i, M.[fin0].[i] = (rv2v M).[i].
  Proof. intros. apply rv2v_spec. Qed.

  Lemma v2rv_spec : forall {n} (a : vec n) i, a.[i] = (v2rv a).[fin0].[i].
  Proof. intros. apply v2rv_spec. Qed.

  Lemma rv2v_v2rv : forall {n} (a : vec n), rv2v (v2rv a) = a.
  Proof. intros. apply cv2v_v2cv. Qed.

  Lemma v2rv_rv2v : forall {n} (M : rvec n), v2rv (rv2v M) = M.
  Proof. intros. apply v2rv_rv2v. Qed.
  
  Lemma vnth_v2rv : forall {n} (a : vec n) i, (v2rv a).[i]  = a.
  Proof. intros. apply vnth_v2rv. Qed.

  (* ======================================================================= *)
  (** ** Convert between matrix and function *)

  Definition f2m {r c} (f : nat -> nat -> A) : mat r c := f2m f.
  Definition m2f {r c} (M : mat r c) : nat -> nat -> A := m2f 0 M.

  Lemma f2m_inj : forall {r c} (f g : nat -> nat -> A),
      @f2m r c f = @f2m r c g -> (forall i j, i < r -> j < c -> f i j = g i j).
  Proof. intros. apply (@f2m_inj _ r c); auto. Qed.

  (** (f2m f).[i].[j] = f (fin2nat i) (fin2nat j) *)
  Lemma mnth_f2m : forall {r c} (f : nat -> nat -> A) i j,
      (@f2m r c f) i j = f (fin2nat i) (fin2nat j).
  Proof. intros. apply mnth_f2m. Qed.
    
  (** (f2m f).[i] = f2v (f (fin2nat i)) *)
  Lemma vnth_f2m : forall {r c} (f : nat -> nat -> A) i,
      (@f2m r c f).[i] = f2v (f (fin2nat i)).
  Proof. intros. apply vnth_f2m. Qed.

  (** (m2f M) i j = M[nat2fin i].[nat2fin j] *)
  Lemma nth_m2f : forall {r c} (M : mat r c) (i j : nat) (Hi : i < r)(Hj : j < c),
      (m2f M) i j = M.[nat2fin i Hi].[nat2fin j Hj].
  Proof. intros. apply nth_m2f. Qed.
  
  (** (m2f M i j) = M[#i,#j] *)
  Lemma nth_m2f_nat2finS : forall {r c} (M : mat (S r) (S c)) i j,
      i < S r -> j < S c -> (m2f M) i j = M.[#i].[#j].
  Proof. intros. apply nth_m2f_nat2finS; auto. Qed.

  Lemma m2f_inj : forall {r c} (M1 M2 : mat r c),
      (forall i j, i < r -> j < c -> (m2f M1) i j = (m2f M2) i j) -> M1 = M2.
  Proof. intros. apply m2f_inj in H; auto. Qed.

  Lemma f2m_m2f : forall {r c} (M : mat r c), f2m (m2f M) = M.
  Proof. intros. apply f2m_m2f. Qed.

  Lemma m2f_f2m : forall {r c} (f : nat -> nat -> A),
    forall i j, i < r -> j < c -> m2f (@f2m r c f) i j = f i j.
  Proof. intros. apply m2f_f2m; auto. Qed.

  (* ======================================================================= *)
  (** ** Convert between matrix and list *)

  Definition l2m {r c} (dl : dlist A) : mat r c := l2m 0 dl.

  Definition m2l {r c} (M : mat r c) : dlist A := m2l M.

  Lemma l2m_inj : forall {r c} (d1 d2 : dlist A),
      length d1 = r -> width d1 c -> length d2 = r -> width d2 c ->
      @l2m r c d1 = l2m d2 -> d1 = d2.
  Proof. intros. apply l2m_inj in H3; auto. Qed.
  
  Lemma l2m_surj : forall {r c} (M : mat r c), (exists d, l2m d = M).
  Proof. intros. apply l2m_surj. Qed.

  Lemma m2l_length : forall {r c} (M : mat r c), length (m2l M) = r.
  Proof. intros. apply m2l_length. Qed.
  
  Lemma m2l_width : forall {r c} (M : mat r c), width (m2l M) c.
  Proof. intros. apply m2l_width. Qed.
  
  Lemma m2l_inj : forall {r c} (m1 m2 : mat r c), m2l m1 = m2l m2 -> m1 = m2.
  Proof. intros. apply m2l_inj; auto. Qed.
  
  Lemma m2l_surj : forall {r c} (d : dlist A),
      length d = r -> width d c -> (exists M : mat r c, m2l M = d).
  Proof. intros. apply (m2l_surj 0); auto. Qed.

  Lemma l2m_m2l : forall {r c} (M : mat r c), @l2m r c (m2l M) = M.
  Proof. intros. apply l2m_m2l. Qed.

  Lemma m2l_l2m : forall {r c} (dl : dlist A),
      length dl = r -> width dl c -> m2l (@l2m r c dl) = dl.
  Proof. intros. apply m2l_l2m; auto. Qed.

  (* ======================================================================= *)
  (** ** Convert between `list of vectors` and mat *)

  (** mat to `list of row vectors` *)
  Definition m2rvl {r c} (M : mat r c) : list (vec c) := m2rvl M.

  (** `list of row vectors` to mat *)
  Definition rvl2m {r c} (l : list (vec c)) : mat r c := rvl2m 0 l.

  Lemma m2rvl_rvl2m : forall {r c} (l : list (vec c)),
      length l = r -> @m2rvl r c (rvl2m l) = l.
  Proof. apply m2rvl_rvl2m. Qed.
  
  Lemma rvl2m_m2rvl : forall {r c} (M : mat r c), rvl2m (m2rvl M) = M.
  Proof. apply rvl2m_m2rvl. Qed.

  (** mat to `list of column vectors` *)
  Definition m2cvl {r c} (M : mat r c) : list (vec r) := m2cvl M.
  
  (** `list of column vectors` to mat *)
  Definition cvl2m {r c} (l : list (vec r)) : mat r c := cvl2m 0 l.
  
  Lemma m2cvl_cvl2m : forall {r c} (l : list (vec r)),
      length l = c -> @m2cvl r c (cvl2m l) = l.
  Proof. apply m2cvl_cvl2m. Qed.
  
  Lemma cvl2m_m2cvl : forall {r c} (M : mat r c), cvl2m (m2cvl M) = M.
  Proof. apply cvl2m_m2cvl. Qed.
  
  (* ======================================================================= *)
  (** ** Make concrete matrix *)

  Definition mkmat_0_c c : mat 0 c := mkmat_0_c c (Azero:=0).
  Definition mkmat_r_0 r : mat r 0 := mkmat_r_0 r (Azero:=0).
  
  Definition mkmat_1_1 a11 : mat 1 1 := mkmat_1_1 a11 (Azero:=0).
  Definition mkmat_1_c c (a : vec c) : mat 1 c := mkmat_1_c c a.
  Definition mkmat_r_1 r (a : vec r) : mat r 1 := mkmat_r_1 r a.
  
  Definition mkmat_1_2 a11 a12 : mat 1 2 := mkmat_1_2 a11 a12 (Azero:=0).
  Definition mkmat_2_1 a11 a21 : mat 2 1 := mkmat_2_1 a11 a21 (Azero:=0).
  Definition mkmat_2_2 a11 a12 a21 a22 : mat 2 2 :=
    mkmat_2_2 a11 a12 a21 a22 (Azero:=0).
  
  Definition mkmat_1_3 a11 a12 a13 : mat 1 3 :=
    mkmat_1_3 a11 a12 a13 (Azero:=0).
  Definition mkmat_3_1 a11 a21 a31 : mat 3 1 :=
    mkmat_3_1 a11 a21 a31 (Azero:=0).
  Definition mkmat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33 : mat 3 3 :=
    mkmat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33 (Azero:=0).
  
  Definition mkmat_1_4 a11 a12 a13 a14 : mat 1 4 :=
    mkmat_1_4 a11 a12 a13 a14 (Azero:=0).
  Definition mkmat_4_1 a11 a21 a31 a41 : mat 4 1 :=
    mkmat_4_1 a11 a21 a31 a41 (Azero:=0).
  Definition mkmat_4_4 a11 a12 a13 a14 a21 a22 a23 a24
    a31 a32 a33 a34 a41 a42 a43 a44 : mat 4 4 :=
    mkmat_4_4
      a11 a12 a13 a14 a21 a22 a23 a24
      a31 a32 a33 a34 a41 a42 a43 a44 (Azero:=0).

  (* ======================================================================= *)
  (** ** Get row and column of a matrix *)

  Definition mrow {r c} (M : mat r c) (i : fin r) : vec c := mrow M i.
  Definition mcol {r c} (M : mat r c) (j : fin c) : vec r := mcol M j.

  Notation "M &1" := (mcol M #0) : mat_scope.
  Notation "M &2" := (mcol M #1) : mat_scope.
  Notation "M &3" := (mcol M #2) : mat_scope.
  Notation "M &4" := (mcol M #3) : mat_scope.

  (** (mrow M i).j = M.i.j *)
  Lemma vnth_mrow : forall {r c} (M : mat r c) (i : fin r) (j : fin c),
      (mrow M i).[j] = M.[i].[j].
  Proof. intros. apply vnth_mrow. Qed.

  (** (mcol M j).i = M.i.j *)
  Lemma vnth_mcol : forall {r c} (M : mat r c) (i : fin r) (j : fin c),
      (mcol M j).[i] = M.[i].[j].
  Proof. intros. apply vnth_mcol. Qed.

  Lemma mcol_mtrans_eq_mrow : forall {r c} (M : mat r c) (i : fin r),
      mcol (M\T) i = mrow M i.
  Proof. intros. apply mcol_mtrans_eq_mrow. Qed.

  Lemma mrow_mtrans_eq_mcol : forall {r c} (M : mat r c) (j : fin c),
      mrow (M\T) j = mcol M j.
  Proof. intros. apply mrow_mtrans_eq_mcol. Qed.

  (* ======================================================================= *)
  (** ** Construct matrix with two matrices *)
  
  (** Append matrix by row *)
  Definition mappr {r1 r2 c} (M : mat r1 c) (N : mat r2 c) : mat (r1 + r2) c :=
    mappr (Azero:=0) M N.

  (** Append matrix by column *)
  Definition mappc {r c1 c2} (M : mat r c1) (N : mat r c2) : mat r (c1 + c2) :=
    mappc (Azero:=0) M N.

  (* ======================================================================= *)
  (** ** Get head or tail column *)

  (** Get head column *)
  Definition mheadc {r c} (M : mat r (S c)) : vec r := mheadc M.

  (** Get tail column *)
  Definition mtailc {r c} (M : mat r (S c)) : vec r := mtailc M.
  
  (** (mheadc M).i = M.i.0 *)
  Lemma vnth_mheadc : forall {r c} (M : mat r (S c)) i, (mheadc M).[i] = M.[i].[fin0].
  Proof. intros. apply vnth_mheadc; auto. Qed.

  (** (mtailc M).i = M.i.(n-1) *)
  Lemma vnth_mtailc : forall {r c} (M : mat r (S c)) i, (mtailc M).[i] = M.[i].[#c].
  Proof. intros. apply vnth_mtailc; auto. Qed.

  (* ======================================================================= *)
  (** ** Remove exact one column at head or tail *)

  (** Remove head column *)
  Definition mremovecH {r c} (M : mat r (S c)) : mat r c := mremovecH M.
  
  (** Remove tail column *)
  Definition mremovecT {r c} (M : mat r (S c)) : mat r c := mremovecT M.
  
  (** (mremovecH M).i.j = M.i.(S j) *)
  Lemma mnth_mremovecH : forall {r c} (M : mat r (S c)) i j,
      (mremovecH M).[i].[j] = M.[i].[fin2SuccRangeSucc j].
  Proof. intros. apply mnth_mremovecH; auto. Qed.
  
  (** (mremovecT M).i.j = M.i.j *)
  Lemma mnth_mremovecT : forall {r c} (M : mat r (S c)) i j,
      (mremovecT M).[i].[j] = M.[i].[fin2SuccRange j].
  Proof. intros. apply mnth_mremovecT; auto. Qed.

  (* ======================================================================= *)
  (** ** Construct matrix from vector and matrix *)

  (** Construct a matrix with a row vector and a matrix *)
  Definition mconsrH {r c} (a : vec c) (M : mat r c) : mat (S r) c := mconsrH a M.

  (** Construct a matrix with a matrix and a row vector *)
  Definition mconsrT {r c} (M : mat r c) (a : vec c) : mat (S r) c := mconsrT M a.

  (** Construct a matrix with a column vector and a matrix *)
  Definition mconscH {r c} (a : vec r) (M : mat r c) : mat r (S c) := mconscH a M.

  (** Construct a matrix with a matrix and a column vector *)
  Definition mconscT {r c} (M : mat r c) (a : vec r) : mat r (S c) := mconscT M a.

  Lemma mnth_mconsrH_0 : forall {r c} (a : vec c) (M : mat r c) j,
      (mconsrH a M).[fin0].[j] = a.[j].
  Proof. intros. apply mnth_mconsrH_0; auto. Qed.

  Lemma mnth_mconsrH_gt0 :
    forall {r c} (a : vec c) (M : mat r c) i j (H : 0 < fin2nat i),
      (mconsrH a M).[i].[j] = M.[fin2PredRangePred i H].[j].
  Proof. intros. apply mnth_mconsrH_gt0; auto. Qed.

  Lemma mconsrH_spec : forall {r c} (a : vec c) (M : mat r c),
      let fa := v2f a in
      let fM := m2f M in
      let faM := m2f (mconsrH a M) in
      (forall j, j < c -> faM O j = fa j) /\
        (forall i j, 0 < i < r -> j < c -> faM i j = fM (i - 1) j).
  Proof. intros. apply mconsrH_spec. Qed.

  Lemma mnth_mconsrT_n : forall {r c} (M : mat r c) (a : vec c) i j,
      i = #r -> (mconsrT M a).[i].[j] = a.[j].
  Proof. intros. apply mnth_mconsrT_n; auto. Qed.

  Lemma mnth_mconsrT_lt :
    forall {r c} (M : mat r c) (a : vec c) i j (E : fin2nat i < r),
      (mconsrT M a).[i].[j] = M.[fin2PredRange i E].[j].
  Proof. intros. apply mnth_mconsrT_lt; auto. Qed.

  Lemma vnth_mconscH : forall {r c} (M : mat (S r) c) (a : vec (S r)) (i : fin (S r)),
      (mconscH a M).[i] = vconsH (a.[i]) (M.[i]).
  Proof. intros; apply vnth_mconscH; auto. Qed.
  
  Lemma mnth_mconscH_0 : forall {r c} (a : vec r) (M : mat r c) i,
      (mconscH a M).[i].[fin0] = a.[i].
  Proof. intros. apply mnth_mconscH_0; auto. Qed.

  Lemma mnth_mconscH_gt0 :
    forall {r c} (M : mat r c) (a : vec r) i j (E : 0 < fin2nat j),
      (mconscH a M).[i].[j] = M.[i].[fin2PredRangePred j E].
  Proof. intros. apply mnth_mconscH_gt0; auto. Qed.

  (** mconscH (mheadc M) (mremovecH M) = M *)
  Lemma mconscH_mheadc_mremovecH : forall {r c} (M : mat r (S c)),
      mconscH (mheadc M) (mremovecH M) = M.
  Proof. intros. apply mconscH_mheadc_mremovecH; auto. Qed.

  (** mconscH (vconsT a x) (vconsT M b) = vconsT (mconscH a M) (vconsH x b) *)
  Lemma mconscH_vconsT_vconsT_eq_vconsT_mconscH_vconsH :
    forall {r c} (a : vec r) (x : A) (M : mat r c) (b : vec c),
      mconscH (vconsT a x) (Vector.vconsT M b) =
        Vector.vconsT (mconscH a M) (vconsH x b).
  Proof. intros. apply mconscH_vconsT_vconsT_eq_vconsT_mconscH_vconsH. Qed.
  
  Lemma mnth_mconscT_n : forall {r c} (M : mat r c) (a : vec r) i j,
      j = nat2finS c -> (mconscT M a).[i].[j] = a.[i].
  Proof. intros. apply mnth_mconscT_n; auto. fin. Qed.

  Lemma mnth_mconscT_lt :
    forall {r c} (M : mat r c) (a : vec r) i j (H : fin2nat j < c),
      (mconscT M a).[i].[j] = M.[i].[fin2PredRange j H].
  Proof. intros. apply mnth_mconscT_lt; auto. Qed.

  Lemma vnth_mconscT : forall {r c} (M : mat r c) (a : vec r) i,
      (mconscT M a).[i] = vconsT M.[i] a.[i].
  Proof. intros. apply vnth_mconscT; auto. Qed.

  (** mconscT (mremovecT M) (mtailc M) = M *)
  Lemma mconscT_mremovecT_mtailc : forall {r c} (M : mat r (S c)),
      mconscT (mremovecT M) (mtailc M) = M.
  Proof. intros. apply mconscT_mremovecT_mtailc; auto. Qed.
  
  (* ======================================================================= *)
  (** ** Mapping of matrix *)

  Definition mmap {r c} (f : A -> A) (M : mat r c) : mat r c := mmap f M.
  Definition mmap2 {r c} (f : A -> A -> A) (M N : mat r c) : mat r c := mmap2 f M N.

  Lemma mmap2_comm :
    forall {r c} (f : A -> A -> A) (M N : mat r c) {Comm : Commutative f}, 
      mmap2 f M N = mmap2 f N M.
  Proof. intros. apply mmap2_comm; auto. Qed.
  
  Lemma mmap2_assoc :
    forall {r c} (f : A -> A -> A) (M N O : mat r c) {Assoc : Associative f}, 
      mmap2 f (mmap2 f M N) O = mmap2 f M (mmap2 f N O).
  Proof. intros. apply mmap2_assoc; auto. Qed.

  (* ======================================================================= *)
  (** ** matrix set row / column *)

  (** set row *)
  Definition msetr {r c} (M : mat r c) (a : vec c) (i0 : fin r) : mat r c :=
    msetr M a i0.

  (** set column *)
  Definition msetc {r c} (M : mat r c) (a : vec r) (j0 : fin c) : mat r c :=
    msetc M a j0.

  Lemma mnth_msetr_same : forall {r c} (M : mat r c) (a : vec c) (i0 : fin r) i j,
      i = i0 -> (msetr M a i0).[i].[j] = a.[j].
  Proof. intros. apply mnth_msetr_same; auto. Qed.

  Lemma mnth_msetr_diff : forall {r c} (M : mat r c) (a : vec c) (i0 : fin r) i j,
      i <> i0 -> (msetr M a i0).[i].[j] = M.[i].[j].
  Proof. intros. apply mnth_msetr_diff; auto. Qed.

  Lemma mnth_msetc_same : forall {r c} (M : mat r c) (a : vec r) (j0:fin c) i j,
      j = j0 -> (msetc M a j0).[i].[j] = a.[i].
  Proof. intros. apply mnth_msetc_same; auto. Qed.

  Lemma mnth_msetc_diff : forall {r c} (M : mat r c) (a : vec r) (j0:fin c) i j,
      j <> j0 -> (msetc M a j0).[i].[j] = M.[i].[j].
  Proof. intros. apply mnth_msetc_diff; auto. Qed.
  
  (* ======================================================================= *)
  (** ** Matrix transposition *)

  Definition mtrans {r c} (M : mat r c): mat c r := mtrans M.
  Notation "M \T" := (mtrans M) : mat_scope.

  (** Transpose twice keep unchanged. *)
  Lemma mtrans_mtrans : forall {r c} (M : mat r c), M \T \T = M.
  Proof. intros. apply mtrans_mtrans. Qed.
  
  (* ======================================================================= *)
  (** ** Diagonal Matrix *)
  
  (** A matrix is a diagonal matrix *)
  Definition mdiag {n} (M : smat n) : Prop := mdiag 0 M.

  (** Construct a diagonal matrix *)
  Definition mdiagMk {n} (a : vec n) : smat n := mdiagMk 0 a.

  (** Transpose of a diagonal matrix keep unchanged *)
  Lemma mtrans_diag : forall {n} (M : smat n), mdiag M -> M\T = M.
  Proof. intros. apply mtrans_diag in H; auto. Qed.

  (** mdiagMk is correct *)
  Lemma mdiagMk_spec : forall {n} (a : vec n), mdiag (mdiagMk a).
  Proof. intros. apply mdiagMk_spec. Qed.

  (** (mdiagMk a)[i,i] = l[i] *)
  Lemma mnth_mdiagMk_same : forall {n} (a : vec n) i, (mdiagMk a).[i].[i] = a.[i].
  Proof. intros. apply mnth_mdiagMk_same. Qed.

  (** (mdiagMk a)[i,j] = 0 *)
  Lemma mnth_mdiagMk_diff : forall {n} (a : vec n) i j, i <> j -> (mdiagMk a).[i].[j] = 0.
  Proof. intros. apply mnth_mdiagMk_diff; auto. Qed.
  
  (* ======================================================================= *)
  (** ** Zero matrix *)

  (** zero matrix *)
  Definition mat0 {r c} : mat r c := @mat0 _ 0 r c.

  (** mat0\T = mat0 *)
  Lemma mtrans_mat0 : forall {r c : nat}, (@mat0 r c)\T = mat0.
  Proof. intros. apply mtrans_mat0. Qed.

  (** mat0[i,j] = 0 *)
  Lemma mnth_mat0 : forall {r c} i j, (@mat0 r c).[i].[j] = 0.
  Proof. intros. apply mnth_mat0. Qed.

  (** row mat0 i = vzero *)
  Lemma mrow_mat0 : forall {r c} i, (@mat0 r c).[i] = vzero.
  Proof. intros. apply mrow_mat0. Qed.

  (** col mat0 i = vzero *)
  Lemma mcol_mat0 : forall {r c} j, (fun k => (@mat0 r c).[k].[j]) = vzero.
  Proof. intros. apply mcol_mat0 with (j:=j). Qed.

  (* ======================================================================= *)
  (** ** Automation for matrix equality proofs *)

  (** Convert equality of two matrices to point-wise element equalities *)
  Ltac meq :=
    apply m2l_inj; cbv; list_eq.

End BasicMatrixTheory.


(* ######################################################################### *)
(** * Monoid matrix theory *)
Module MonoidMatrixTheory (E : MonoidElementType).

  Include (BasicMatrixTheory E).

  Open Scope vec_scope.

  (* ======================================================================= *)
  (** ** Sum of a vector *)
  Definition vsum {n} (a : vec n) := @vsum _ Aadd 0 _ a.
  
  (** (∀ i, a.i = b.i) -> Σa = Σb *)
  Lemma vsum_eq : forall {n} (a b : vec n), (forall i, a.[i] = b.[i]) -> vsum a = vsum b.
  Proof. intros. apply vsum_eq; intros; auto. Qed.

  (** (∀ i, a.i = 0) -> Σa = 0 *)
  Lemma vsum_eq0 : forall {n} (a : vec n), (forall i, a.[i] = 0) -> vsum a = 0.
  Proof. intros. apply vsum_eq0; auto. Qed.

  (** Convert `vsum` to `seqsum` *)
  Lemma vsum_eq_seqsum : forall {n} (a : vec n),
      vsum a = @seqsum _ Aadd 0 n (fun i => v2f a i).
  Proof. intros. apply vsum_eq_seqsum. Qed.

  (* (** Convert `vsum` to `seqsum` (succ form) *) *)
  (* Lemma vsum_eq_seqsum_succ : forall {n} (a : vec (S n)), *)
  (*     vsum a = ((@seqsum _ Aadd 0 (fun i => a $ (nat2finS i)) n) *)
  (*               + a $ (nat2finS n))%A. *)
  (* Proof. intros. apply vsum_eq_seqsum_succ. Qed. *)
  
  (** `vsum` of (S n) elements, equal to addition of Sum and tail *)
  Lemma vsumS_tail : forall {n} (a : vec (S n)),
      vsum a = (vsum (fun i => a.[fin2SuccRange i]) + a.[nat2finS n])%A.
  Proof. intros. apply vsumS_tail; auto. Qed.

  (** `vsum` of (S n) elements, equal to addition of head and Sum *)
  Lemma vsumS_head : forall {n} (a : vec (S n)),
      vsum a = (a.[nat2finS 0] + vsum (fun i => a.[fin2SuccRangeSucc i]))%A.
  Proof. intros. apply vsumS_head; auto. Qed.

  (** Σa + Σb = Σ(fun i => a.[i] + b.[i]) *)
  Lemma vsum_add : forall {n} (a b : vec n),
      (vsum a + vsum b)%A = vsum (fun i => a.[i] + b.[i])%A.
  Proof. intros. apply vsum_add; auto. Qed.
  
  (** `vsum` which only one item is nonzero, then got this item. *)
  Lemma vsum_unique : forall {n} (a : vec n) (x : A) i,
      a.[i] = x -> (forall j, i <> j -> a.[j] = 0) -> vsum a = x.
  Proof. intros. apply vsum_unique with (i:=i); auto. Qed.

  (** `vsum` of the m+n elements equal to plus of two parts.
      Σ[0,(m+n)] a = Σ[0,m](fun i=>a[i]) + Σ[m,m+n] (fun i=>a[m+i]) *)
  Lemma vsum_plusIdx : forall m n (a : vec (m + n)),
      vsum a = (vsum (fun i => a.[fin2AddRangeR i]) +
                 vsum (fun i => a.[fin2AddRangeAddL i]))%A.
  Proof. intros. apply vsum_plusIdx; auto. Qed.

  (** The order of two nested summations can be exchanged.
      ∑[i,0,r](∑[j,0,c] a.ij) = 
      a00 + a01 + ... + a0c + 
      a10 + a11 + ... + a1c + 
      ...
      ar0 + ar1 + ... + arc = 
      ∑[j,0,c](∑[i,0,r] a.ij) *)
  Lemma vsum_vsum : forall r c (a : @Vector.vec (vec c) r),
      vsum (fun i => vsum (fun j => a.[i].[j])) =
        vsum (fun j => vsum (fun i => a.[i].[j])).
  Proof. intros. apply vsum_vsum. Qed.

  (* ======================================================================= *)
  (** ** Vector addition *)
  
  Definition vadd {n} (a b : vec n) : vec n := vadd a b (Aadd:=Aadd).
  Infix "+" := vadd : vec_scope.

  (** (a + b) + c = a + (b + c) *)
  Lemma vadd_assoc : forall {n} (a b c : vec n), (a + b) + c = a + (b + c).
  Proof. intros. apply vadd_assoc. Qed.

  (** a + b = b + a *)
  Lemma vadd_comm : forall {n} (a b : vec n), a + b = b + a.
  Proof. intros. apply vadd_comm. Qed.

  (** 0 + a = a *)
  Lemma vadd_0_l : forall {n} (a : vec n), vzero + a = a.
  Proof. intros. apply vadd_0_l. Qed.

  (** a + 0 = a *)
  Lemma vadd_0_r : forall {n} (a : vec n), a + vzero = a.
  Proof. intros. apply vadd_0_r. Qed.

  #[export] Instance vadd_AMonoid : forall n, AMonoid (@vadd n) vzero.
  Proof. apply vadd_AMonoid. Qed.

  Open Scope mat_scope.
  
  (* ======================================================================= *)
  (** ** Matrix addition *)

  Definition madd {r c} (M N : mat r c) : mat r c := madd M N (Aadd:=Aadd).
  Infix "+" := madd : mat_scope.
  
  (** (M+N)[i,j] = M[i,j] + N[i,j] *)
  Lemma mnth_madd : forall {r c} (M N : mat r c) i j,
      (M + N).[i].[j] = (M.[i].[j] + N.[i].[j])%A.
  Proof. intros. unfold madd. apply mnth_madd. Qed.

  (** cv2v (M + N) = cv2v M + cv2v N *)
  Lemma cv2v_madd : forall {n} (M N : cvec n), cv2v (M + N) = (cv2v M + cv2v N)%V.
  Proof. intros. apply cv2v_madd. Qed.

  (** M + N = N + M *)
  Lemma madd_comm : forall {r c} (M N : mat r c), M + N = (N + M).
  Proof. intros. apply madd_comm. Qed.

  (** (M + N) + O = M + (N + O) *)
  Lemma madd_assoc : forall {r c} (M N O : mat r c), (M + N) + O = M + (N + O).
  Proof. intros. apply madd_assoc. Qed.

  (** (M + N) + O = (M + O) + N *)
  Lemma madd_perm : forall {r c} (M N O : mat r c), (M + N) + O = (M + O) + N.
  Proof. intros. apply madd_perm. Qed.

  (** mat0 + M = M *)
  Lemma madd_0_l : forall {r c} (M : mat r c), mat0 + M = M. 
  Proof. intros. apply madd_0_l. Qed.

  (** M + mat0 = M *)
  Lemma madd_0_r : forall {r c} (M : mat r c), M + mat0 = M. 
  Proof. intros. apply madd_0_r. Qed.

  (** (M + N) \T = M \T + N \T *)
  Lemma mtrans_madd : forall {r c} (M N : mat r c), (M + N) \T = M \T + N \T.
  Proof. intros. apply mtrans_madd. Qed.

End MonoidMatrixTheory.


(* ######################################################################### *)
(** * Ring matrix theory *)
Module RingMatrixTheory (E : RingElementType).
  
  Include (MonoidMatrixTheory E).

  Open Scope vec_scope.

  (* ======================================================================= *)
  (** ** 自然基的基向量 *)

  Definition veye {n} (i : fin n) : vec n := veye 0 1 i.

  (** (veye i).i = 1 *)
  Lemma vnth_veye_eq : forall {n} i, (@veye n i).[i] = 1.
  Proof. intros. apply vnth_veye_eq. Qed.

  (** (veye i).j = 0 *)
  Lemma vnth_veye_neq : forall {n} i j, i <> j -> (@veye n i).[j] = 0.
  Proof. intros. apply vnth_veye_neq; auto. Qed.

  (* ======================================================================= *)
  (** ** natural basis, 自然基（最常见的一种标准正交基) *)
  
  Definition veyes (n : nat) : @Vector.vec (@Vector.vec A n) n := veyes 0 1 n.

  (** veyes.ii = 1 *)
  Lemma vnth_veyes_eq : forall {n} i, (veyes n).[i].[i] = 1.
  Proof. intros. apply vnth_veyes_eq. Qed.

  (** veyes.ij = 0 *)
  Lemma vnth_veyes_neq : forall {n} i j, i <> j -> (veyes n).[i].[j] = 0.
  Proof. intros. apply vnth_veyes_neq; auto. Qed.

  (* ======================================================================= *)
  (** ** Vector opposition *)

  Definition vopp {n} (a : vec n) : vec n := vopp (Aopp:=Aopp) a.
  Notation "- a" := (vopp a) : vec_scope.

  (** - a + a = 0 *)
  Lemma vadd_vopp_l : forall {n} (a : vec n), (- a) + a = vzero.
  Proof. intros. apply vadd_vopp_l. Qed.
  
  (** a + - a = 0 *)
  Lemma vadd_vopp_r : forall {n} (a : vec n), a + (- a) = vzero.
  Proof. intros. apply vadd_vopp_r. Qed.

  #[export] Instance vadd_AGroup : forall n, AGroup (@vadd n) vzero vopp.
  Proof. intros. apply vadd_AGroup. Qed.

  (** - (- a) = a *)
  Lemma vopp_vopp : forall {n} (a : vec n), - (- a) = a.
  Proof. intros. apply vopp_vopp. Qed.

  (** a = - b <-> - a = b *)
  Lemma vopp_exchange : forall {n} (a b : vec n), a = - b <-> - a = b.
  Proof. intros. apply vopp_exchange. Qed.

  (** - (vzero) = vzero *)
  Lemma vopp_vzero : forall {n}, - (@vzero n) = vzero.
  Proof. intros. apply vopp_vzero. Qed.

  (** - (a + b) = (- a) + (- b) *)
  Lemma vopp_vadd : forall {n} (a b : vec n), - (a + b) = (- a) + (- b).
  Proof. intros. apply vopp_vadd. Qed.

  (* ======================================================================= *)
  (** ** Vector subtraction *)

  (* Definition vsub {n} (a b : vec n) : vec n := a + (- b). *)
  Notation "a - b" := ((a + -b)%V) : vec_scope.

  Lemma vsub_self : forall (n : nat) (a : vec n), a - a = (@vzero n).
  Proof. intros. apply vsub_self. Qed.
  
  Lemma vsub_0_l : forall (n : nat) (a : vec n), (@vzero n) - a = - a.
  Proof. intros. apply vsub_0_l. Qed.
  
  Lemma vsub_comm : forall (n : nat) (a b : vec n), a - b = - (b - a).
  Proof. intros. apply vsub_comm. Qed.
    
  Lemma vsub_assoc : forall (n : nat) (a b c : vec n), (a - b) - c = a - (b + c).
  Proof. intros. apply vsub_assoc. Qed.
    
  Lemma vsub_assoc1 : forall (n : nat) (a b c : vec n), (a + b) - c = a + (b - c).
  Proof. intros. apply vsub_assoc1. Qed.
    
  Lemma vsub_assoc2 : forall (n : nat) (a b c : vec n), (a - b) - c = (a - c) - b.
  Proof. intros. apply vsub_assoc2. Qed.

  (** ** Vector scalar multiplication *)

  Definition vcmul {n} (x : A) (a : vec n) : vec n := vcmul (Amul:=Amul) x a.
  Infix "\.*" := vcmul : vec_scope.

  (** (x .* a)[i] = x .* a[i] *)
  Lemma vnth_vcmul : forall {n} (a : vec n) x i, (x \.* a).[i] = x * (a.[i]).
  Proof. intros. cbv. auto. Qed.

  (** x .* (y .* a) = (x * y) .* a *)
  Lemma vcmul_assoc : forall {n} (x y : A) (a : vec n),
      x \.* (y \.* a) = (x * y)%A \.* a.
  Proof. intros. apply vcmul_assoc. Qed.

  (** x .* (y .* a) = y .* (x .* a) *)
  Lemma vcmul_perm : forall {n} (x y : A) (a : vec n),
      x \.* (y \.* a) = y \.* (x \.* a).
  Proof. intros. apply vcmul_perm. Qed.

  (** (x + y) .* a = (x .* a) + (y .* a) *)
  Lemma vcmul_add : forall {n} (x y : A) (a : vec n),
      (x + y)%A \.* a = (x \.* a) + (y \.* a).
  Proof. intros. apply vcmul_add. Qed.

  (** x .* (a + b) = (x .* a) + (x .* b) *)
  Lemma vcmul_vadd : forall {n} x (a b : vec n),
      x \.* (a + b) = (x \.* a) + (x \.* b).
  Proof. intros. apply vcmul_vadd. Qed.

  (** 1 .* a = a *)
  Lemma vcmul_1_l : forall {n} (a : vec n), 1 \.* a = a.
  Proof. intros. apply vcmul_1_l. Qed.

  (** 0 .* a = 0 *)
  Lemma vcmul_0_l : forall {n} (a : vec n), 0 \.* a = vzero.
  Proof. intros. apply vcmul_0_l. Qed.

  (** x .* 0 = 0 *)
  Lemma vcmul_0_r : forall {n} x, x \.* (@vzero n) = vzero.
  Proof. intros. apply vcmul_0_r. Qed.
  
  (** (-x) .* a = - (x .* a) *)
  Lemma vcmul_opp : forall {n} x (a : vec n), (- x)%A \.* a = - (x \.* a).
  Proof. intros. apply vcmul_opp. Qed.
  
  (** x .* (- a) = - (x .* a) *)
  Lemma vcmul_vopp : forall {n} x (a : vec n), x \.* (- a) = - (x \.* a).
  Proof. intros. apply vcmul_vopp. Qed.

  (** (-x) .* (- a) = x .* a *)
  Lemma vcmul_opp_vopp : forall {n} x (a : vec n), (- x)%A \.* (- a) = x \.* a.
  Proof. intros. apply vcmul_opp_vopp. Qed.

  (** x .* (a - b) = (x .* a) - (x .* b) *)
  Lemma vcmul_vsub : forall {n} x (a b : vec n),
      x \.* (a - b) = (x \.* a) - (x \.* b).
  Proof. intros. apply vcmul_vsub. Qed.

  (** a <> 0 -> b <> 0 -> x .* a = b -> x <> 0 *)
  Lemma vcmul_eq_imply_x_neq0 : forall {n} (a b : vec n) x,
      a <> vzero -> b <> vzero -> x \.* a = b -> x <> 0.
  Proof. intros. apply vcmul_eq_imply_x_neq0 in H1; auto. Qed.

  (* ======================================================================= *)
  (** ** Vector dot product *)

  Definition vdot {n : nat} (a b : vec n) : A := @vdot _ Aadd 0 Amul _ a b.
  Notation "< a , b >" := (vdot a b) : vec_scope.

  (** <a, b> = <b, a> *)
  Lemma vdot_comm : forall {n} (a b : vec n), <a, b> = <b, a>.
  Proof. intros. apply vdot_comm. Qed.

  (** <vzero, a> = 0 *)
  Lemma vdot_0_l : forall {n} (a : vec n), <vzero, a> = 0.
  Proof. intros. apply vdot_0_l. Qed.

  (** <a, vzero> = 0 *)
  Lemma vdot_0_r : forall {n} (a : vec n), <a, vzero> = 0.
  Proof. intros. apply vdot_0_r. Qed.

  (** <a + b, c> = <a, c> + <b, c> *)
  Lemma vdot_vadd_l : forall {n} (a b c : vec n), <a + b, c> = (<a, c> + <b, c>)%A.
  Proof. intros. apply vdot_vadd_l. Qed.

  (** <a, b + c> = <a, b> + <a, c> *)
  Lemma vdot_vadd_r : forall {n} (a b c : vec n), <a, b + c> = (<a, b> + <a, c>)%A.
  Proof. intros. apply vdot_vadd_r. Qed.

  (** <- a, b> = - <a, b> *)
  Lemma vdot_vopp_l : forall {n} (a b : vec n), < - a, b> = (- <a, b>)%A.
  Proof. intros. apply vdot_vopp_l. Qed.

  (** <a, - b> = - <a, b> *)
  Lemma vdot_vopp_r : forall {n} (a b : vec n), <a, - b> = (- <a, b>)%A.
  Proof. intros. apply vdot_vopp_r. Qed.

  (** <a - b, c> = <a, c> - <b, c> *)
  Lemma vdot_vsub_l : forall {n} (a b c : vec n), <a - b, c> = (<a, c> - <b, c>)%A.
  Proof. intros. apply vdot_vsub_l. Qed.

  (** <a, a - c> = <a, b> - <a, c> *)
  Lemma vdot_vsub_r : forall {n} (a b c : vec n), <a, b - c> = (<a, b> - <a, c>)%A.
  Proof. intros. apply vdot_vsub_r. Qed.

  (** <x .* a, b> = x * <a, b> *)
  Lemma vdot_vcmul_l : forall {n} (a b : vec n) (x : A), <x \.* a, b> = x * <a, b>.
  Proof. intros. apply vdot_vcmul_l. Qed.

  (** <a, x .* b> = x * <a, b> *)
  Lemma vdot_vcmul_r : forall {n} (a b : vec n) (x : A), <a, x \.* b> = x * <a, b>.
  Proof. intros. apply vdot_vcmul_r. Qed.

  (** <a, veye i> = a i *)
  Lemma vdot_veye_r : forall {n} (a : vec n) i, <a, veye i> = a i.
  Proof. intros. apply vdot_veye_r. Qed.

  (** <veye i, a> = a i *)
  Lemma vdot_veye_l : forall {n} (a : vec n) i, <veye i, a> = a i.
  Proof. intros. apply vdot_veye_l. Qed.
  
  (** <a, b> <> 0 -> a <> 0 *)
  Lemma vdot_neq0_imply_neq0_l : forall {n} (a b : vec n), <a, b> <> 0 -> a <> vzero.
  Proof. intros. apply vdot_neq0_imply_neq0_l in H; auto. Qed.

  (** <a, b> <> 0 -> b <> 0 *)
  Lemma vdot_neq0_imply_neq0_r : forall {n} (a b : vec n), <a, b> <> 0 -> b <> vzero.
  Proof. intros. apply vdot_neq0_imply_neq0_r in H; auto. Qed.

  (** (∀ c, <a, c> = <b, c>) -> a = b *)
  Lemma vdot_cancel_r : forall {n} (a b : vec n),
      (forall c : vec n, <a, c> = <b, c>) -> a = b.
  Proof. intros. apply vdot_cancel_r in H; auto. Qed.
  
  (** (∀ c, <c, a> = <c, b>) -> a = b *)
  Lemma vdot_cancel_l : forall {n} (a b : vec n),
      (forall c : vec n, <c, a> = <c, b>) -> a = b.
  Proof. intros. apply vdot_cancel_l in H; auto. Qed.

  (* ======================================================================= *)
  (** ** Properties of vsum *)
  
  (** - Σa = Σ(fun i => -a.[i]) *)
  Lemma vsum_opp : forall {n} (a : vec n),
        (- vsum a)%A = vsum (fun i => - a.[i])%A.
  Proof. intros. apply vsum_opp; auto. Qed.

  (** x * Σa = Σ(fun i -> x * a.[i]) *)
  Lemma vsum_cmul_l : forall {n} (a : vec n) x,
      x * vsum a = vsum (fun i => x * a.[i]).
  Proof. intros. apply vsum_cmul_l. Qed.

  (** Σa * x = Σ(fun i -> a.[i] * x) *)
  Lemma vsum_cmul_r : forall {n} (a : vec n) x,
      vsum a * x = vsum (fun i => a.[i] * x).
  Proof. intros. apply vsum_cmul_r. Qed.

  (* ======================================================================= *)
  (** ** Unit vector *)
  
  (** A unit vector u is a vector whose length equals one.
      Here, we use the square of length instead of length directly,
      but this is reasonable with the proof of vunit_spec. *)
  Definition vunit {n} (a : vec n) : Prop := @vunit _ Aadd 0 Amul 1 _ a.

  (** vunit a <-> vunit (vopp a). *)
  Lemma vopp_vunit : forall {n} (a : vec n), vunit (vopp a) <-> vunit a.
  Proof. intros. apply vopp_vunit. Qed.

  (* ======================================================================= *)
  (** ** Orthogonal vectors *)

  (* Two vectors, u and v, in an inner product space v, are orthogonal (also called 
     perpendicular) if their inner-product is zero. It can be denoted as `u ⟂ v` *)
  
  Definition vorth {n} (a b : vec n) : Prop := <a, b> = 0.
  Infix "_|_" := vorth (at level 50).

  (** a _|_ b -> b _|_ a *)
  Lemma vorth_comm : forall {n} (a b : vec n), a _|_ b -> b _|_ a.
  Proof. intros. apply vorth_comm; auto. Qed.

  Open Scope mat_scope.

  (* ======================================================================= *)
  (** ** Identity matrix *)

  (** Identity matrix *)
  Definition mat1 {n : nat} : mat n n := @mat1 _ 0 1 _.

  (** mat1 is diagonal matrix *)
  Lemma mat1_diag : forall {n : nat}, mdiag (@mat1 n).
  Proof. intros. apply mat1_diag. Qed.
  
  (** mat1 \T = mat1 *)
  Lemma mtrans_mat1 : forall {n : nat}, (@mat1 n) \T = mat1.
  Proof. intros. apply mtrans_mat1. Qed.

  (** mat1[i,i] = 1 *)
  Lemma mnth_mat1_same : forall {n} i, (@mat1 n).[i].[i] = 1.
  Proof. intros. apply mnth_mat1_same; auto. Qed.

  (** mat1[i,j] = 0 *)
  Lemma mnth_mat1_diff : forall {n} i j, i <> j -> (@mat1 n).[i].[j] = 0.
  Proof. intros. apply mnth_mat1_diff; auto. Qed.

  (* ======================================================================= *)
  (** ** Matrix trace *)
  Definition mtrace {n : nat} (M : smat n) : A := @mtrace _ Aadd 0 _ M.
  Notation "'tr' M" := (mtrace M) : mat_scope.

  (** tr(M \T) = tr(M) *)
  Lemma mtrace_mtrans : forall {n} (M : smat n), tr (M \T) = tr(M).
  Proof. intros. apply mtrace_mtrans. Qed.

  (** tr(M + N) = tr(M) + tr(N) *)
  Lemma mtrace_madd : forall {n} (M N : smat n), tr (M + N) = (tr M + tr N)%A.
  Proof. intros. apply mtrace_madd. Qed.
  
  (* ======================================================================= *)
  (** ** Monoid structure over {madd,mat0,meq} *)
  #[export] Instance madd_AMonoid : forall r c, AMonoid (@madd r c) mat0.
  Proof. apply madd_AMonoid. Qed.
  
  (* ======================================================================= *)
  (** ** Matrix opposition *)
  
  Definition mopp {r c} (M : mat r c) : mat r c := mopp M (Aopp:=Aopp).
  Notation "- a" := (mopp a) : mat_scope.

  (** - (M + N) = (- M) + (- N) *)
  Lemma mopp_madd : forall {r c : nat} (M N : mat r c), - (M + N) = (- M) + (- N).
  Proof. intros. apply mopp_madd. Qed.

  (** (- M) + M = mat0 *)
  Lemma madd_mopp_l : forall r c (M : mat r c), (- M) + M = mat0.
  Proof. intros. apply madd_opp_l. Qed.

  (** M + (-M) = mat0 *)
  Lemma madd_mopp_r : forall r c (M : mat r c), M + (- M) = mat0.
  Proof. intros. apply madd_opp_r. Qed.

  (** - (- M) = M *)
  Lemma mopp_mopp : forall {r c} (M : mat r c), - (- M) = M.
  Proof. intros. apply mopp_mopp. Qed.

  (** - mat0 = mat0 *)
  Lemma mopp_0 : forall {r c}, - (@mat0 r c) = mat0.
  Proof. intros. apply mopp_mat0. Qed.

  (** (- M) \T = - (M \T) *)
  Lemma mtrans_mopp : forall {r c} (M : mat r c), (- M) \T = - (M \T).
  Proof. intros. apply mtrans_mopp. Qed.

  (** tr(- M) = - (tr(M)) *)
  Lemma mtrace_mopp : forall {n} (M : smat n), tr (- M) = (- tr M)%A.
  Proof. intros. apply mtrace_mopp. Qed.
  
  (* ======================================================================= *)
  (** ** Matrix subtraction *)
  
  (* Definition msub {r c} (M N : mat r c) : mat r c := @msub _ Aadd Aopp _ _ M N. *)
  Notation "M - N" := ((M + -N)%M) : mat_scope.

  (** M - N = M + (- N) *)
  Lemma msub_rw : forall {r c} (M N : mat r c), M - N = M + (- N).
  Proof. intros. reflexivity. Qed.

  (** M - N = - (N - M) *)
  Lemma msub_comm : forall {r c} (M N : mat r c), M - N = - (N - M).
  Proof. intros. apply msub_comm. Qed.

  (** (M - N) - O = M - (N + O) *)
  Lemma msub_assoc : forall {r c} (M N O : mat r c), (M - N) - O = M - (N + O).
  Proof. intros. apply msub_assoc. Qed.

  (** (M + N) - O = M + (N - O) *)
  Lemma msub_assoc1 : forall {r c} (M N O : mat r c), (M + N) - O = M + (N - O).
  Proof. intros. apply msub_assoc1. Qed.

  (** (M - N) - O = M - (O - N) *)
  Lemma msub_assoc2 : forall {r c} (M N O : mat r c), (M - N) - O = (M - O) - N.
  Proof. intros. apply msub_assoc2. Qed.

  (** mat0 - M = - M *)
  Lemma msub_0_l : forall {r c} (M : mat r c), mat0 - M = - M.
  Proof. intros. apply msub_0_l. Qed.

  (** M - mat0 = M *)
  Lemma msub_0_r : forall {r c} (M : mat r c), M - mat0 = M.
  Proof. intros. apply msub_0_r. Qed.

  (** M - M = mat0 *)
  Lemma msub_self : forall {r c} (M : mat r c), M - M = mat0.
  Proof. intros. apply msub_self. Qed.

  (** (M - N) \T = M \T - N \T *)
  Lemma mtrans_msub : forall {r c} (M N : mat r c), (M - N) \T = M \T - N \T.
  Proof. intros. apply mtrans_msub. Qed.

  (** tr(M - N) = tr(M) - tr(N) *)
  Lemma mtrace_msub : forall {n} (M N : smat n), tr (M - N) = (tr M - tr N)%A.
  Proof. intros. apply mtrace_msub. Qed.

  (* ======================================================================= *)
  (** ** Abelian group structure over {madd,mat0,mopp} *)
  #[export] Instance madd_AGroup : forall r c, AGroup (@madd r c) mat0 mopp.
  Proof. apply madd_AGroup. Qed.

  (* ======================================================================= *)
  (** ** Scalar multiplication of matrix *)

  (** Scalar multiplication of matrix *)
  Definition mcmul {r c} (x : A) (M : mat r c) : mat r c := mcmul x M (Amul:=Amul).
  Infix "\.*" := mcmul : mat_scope.

  (** (x .* M)[i,j] = x * M[i,j] *)
  Lemma mnth_mcmul : forall {r c} (M : mat r c) x i j,
      (x \.* M).[i].[j] = x * (M.[i].[j]).
  Proof. intros. unfold mcmul. apply mnth_mcmul. Qed.

  (** cv2v (x .* M) = x .* (cv2v M) *)
  Lemma cv2v_mcmul : forall {n} (x : A) (M : cvec n),
      cv2v (x \.* M) = (x \.* (cv2v M))%V.
  Proof. intros. apply cv2v_mcmul. Qed.

  (** 0 .* M = mat0 *)
  Lemma mcmul_0_l : forall {r c} (M : mat r c), 0 \.* M = mat0.
  Proof. intros. apply mcmul_0_l. Qed.

  (** x .* mat0 = mat0 *)
  Lemma mcmul_0_r : forall {r c} x, x \.* (@mat0 r c) = mat0.
  Proof. intros. apply mcmul_0_r. Qed.

  (** 1 .* M = M *)
  Lemma mcmul_1_l : forall {r c} (M : mat r c), 1 \.* M = M.
  Proof. intros. apply mcmul_1_l. Qed.

  (** x .* mat1 = mdiag([a,a,...]) *)
  Lemma mcmul_1_r : forall {n} x, x \.* mat1 = mdiagMk (vrepeat n x).
  Proof. intros. apply mcmul_1_r. Qed.

  (** x .* (y .* M) = (x * y) .* M *)
  Lemma mcmul_assoc : forall {r c} (x y : A) (M : mat r c),
      x \.* (y \.* M) = (x * y) \.* M.
  Proof. intros. apply mcmul_assoc. Qed.

  (** x .* (y .* M) = y .* (x .* M) *)
  Lemma mcmul_perm : forall {r c} (x y : A) (M : mat r c),
      x \.* (y \.* M) = y \.* (x \.* M).
  Proof. intros. apply mcmul_perm. Qed.

  (** (x + y) .* M = (x .* M) + (y .* M) *)
  Lemma mcmul_add_distr : forall {r c} (x y : A) (M : mat r c), 
      (x + y)%A \.* M = (x \.* M) + (y \.* M).
  Proof. intros. apply mcmul_add_distr. Qed.

  (** x \.* (M + N) = (x \.* M) + (x \.* N) *)
  Lemma mcmul_madd_distr : forall {r c} (x : A) (M N : mat r c), 
      x \.* (M + N) = (x \.* M) + (x \.* N).
  Proof. intros. apply mcmul_madd_distr. Qed.
  
  (** (-x) .* M  = - (x .* M) *)
  Lemma mcmul_opp : forall {r c} x (M : mat r c), (- x)%A \.* M = - (x \.* M).
  Proof. intros. apply mcmul_opp. Qed.
  
  (** x \.* (- M)  = - (x \.* M) *)
  Lemma mcmul_mopp : forall {r c} x (M : mat r c), x \.* (- M) = - (x \.* M).
  Proof. intros. apply mcmul_mopp. Qed.

  (** x \.* (M - N) = (x \.* M) - (x \.* N) *)
  Lemma mcmul_msub : forall {r c} x (M N : mat r c),
      x \.* (M - N) = (x \.* M) - (x \.* N).
  Proof. intros. apply mcmul_msub. Qed.

  (** (x \.* M) \T = x \.* (M \T) *)
  Lemma mtrans_mcmul : forall {r c} (x : A) (M : mat r c), (x \.* M) \T = x \.* (M \T).
  Proof. intros. apply mtrans_mcmul. Qed.

  (** tr (x \.* M) = a * tr (m) *)
  Lemma mtrace_mcmul : forall {n} (x : A) (M : smat n), tr (x \.* M) = (x * tr M)%A.
  Proof. intros. apply mtrace_mcmul. Qed.

  (** M <> 0 -> N <> 0 -> x .* M = N -> x <> 0 *)
  Lemma mcmul_eq_imply_not_x0 : forall {r c} (M N : mat r c) x,
      M <> mat0 -> N <> mat0 -> x \.* M = N -> x <> 0.
  Proof. intros. apply mcmul_eq_imply_not_x0 in H1; auto. Qed.

  (* ======================================================================= *)
  (** ** Matrix multiplication *)
  Definition mmul {r c s : nat} (M : mat r c) (N : mat c s) : mat r s :=
    mmul M N (Amul:=Amul)(Azero:=0)(Aadd:=Aadd).
  Infix "*" := mmul : mat_scope.

  (** (M * N)[i,j] = <row M i, col N j> *)
  Lemma mnth_mmul : forall {r c t} (M : mat r c) (N : mat c t) i j,
      (M * N).[i].[j] = <M.[i], (fun k => N.[k].[j])>.
  Proof. intros. auto. Qed.

  (** (M * N)[i] = <row M i, col N j> *)
  Lemma vnth_mmul : forall {r c t} (M : mat r c) (N : mat c t) i,
      (M * N).[i] = Vector.vmap (fun a => <M.[i], a>) (N\T).
  Proof. intros. auto. Qed.

  (** N is cvec -> M * N = fun i => (vdot N) (M.[i]) *)
  Lemma mmul_cvec : forall {r c} (M : mat r c) (N : cvec c),
      M * N = fun i j => <cv2v N, M.[i]>.
  Proof. intros. apply mmul_cvec. Qed.

  (** M is rvec -> M * N = fun i j => (vdot M) (mcol N j) *)
  Lemma mmul_rvec : forall {r c} (M : rvec r) (N : mat r c),
      M * N = fun i j => <rv2v M, mcol N j>.
  Proof. intros. apply mmul_rvec. Qed.

  (** <row(M,i), col(N,j)> = [M * N].ij *)
  Lemma vdot_row_col : forall {r c s} (M : mat r c) (N : mat c s) i j,
      <mrow M i, mcol N j> = (M * N).[i].[j].
  Proof. intros. apply vdot_row_col. Qed.

  (** <col(M,i), col(N,j)> = (M\T * N)[i,j] *)
  Lemma vdot_col_col : forall {n} (M N : smat n) i j,
      <mcol M i, mcol N j> = (M\T * N).[i].[j].
  Proof. intros. apply vdot_col_col. Qed.

  (** <row(M,i), row(N,j)> = (M * N\T)[i,j] *)
  Lemma vdot_row_row : forall {n} (M N : smat n) i j,
      <mrow M i, mrow N j> = (M * N\T).[i].[j].
  Proof. intros. apply vdot_row_row. Qed.

  (** <a, b> = (a\T * b).11 *)
  Lemma vdot_eq_mmul : forall {n} (a b : vec n), <a, b> = (v2rv a * v2cv b).11.
  Proof. intros. apply vdot_eq_mmul. Qed.

  (** (M * N) * O = M * (N * O) *)
  Lemma mmul_assoc : forall {r c s t : nat} (M : mat r c) (N : mat c s) (O : mat s t), 
      (M * N) * O = M * (N * O).
  Proof. intros. apply mmul_assoc. Qed.

  (** M * (N + O) = M * N + M * O *)
  Lemma mmul_madd_distr_l : forall {r c s : nat} (M : mat r c) (N O : mat c s), 
      M * (N + O) = M * N + M * O.
  Proof. intros. apply mmul_madd_distr_l. Qed.
  
  (** (M + N) * O = M * O + N * O *)
  Lemma mmul_madd_distr_r : forall {r c s : nat} (M N : mat r c) (O : mat c s),
      (M + N) * O = M * O + N * O.
  Proof. intros. apply mmul_madd_distr_r. Qed.

  (** M * (N - O) = M * N - M * O *)
  Lemma mmul_msub_distr_l : forall {r c s : nat} (M : mat r c) (N O : mat c s), 
      M * (N - O) = M * N - M * O.
  Proof. intros. apply mmul_msub_distr_l. Qed.
  
  (** (M - N) * O = M * O - N * O *)
  Lemma mmul_msub_distr_r : forall {r c s : nat} (M N : mat r c) (O : mat c s),
      (M - N) * O = M * O - N * O.
  Proof. intros. apply mmul_msub_distr_r. Qed.

  (** - (M * N) = (- M) * N *)
  Lemma mmul_mopp_l : forall {r c s : nat} (M : mat r c) (N : mat c s),
      - (M * N) = (- M) * N.
  Proof. intros. apply mmul_mopp_l. Qed.

  (** - (M * N) = M * (- N) *)
  Lemma mmul_mopp_r : forall {r c s : nat} (M : mat r c) (N : mat c s),
      - (M * N) = M * (- N).
  Proof. intros. apply mmul_mopp_r. Qed.

  (** mat0 * M = mat0 *)
  Lemma mmul_0_l : forall {r c s} (M : mat c s), (@mat0 r c) * M = mat0.
  Proof. intros. apply mmul_0_l. Qed.

  (** M * mat0 = mat0 *)
  Lemma mmul_0_r : forall {r c s} (M : mat r c), M * (@mat0 c s) = mat0.
  Proof. intros. apply mmul_0_r. Qed.

  (** mat1 * M = M *)
  Lemma mmul_1_l : forall {r c : nat} (M : mat r c), mat1 * M = M.
  Proof. intros. apply mmul_1_l. Qed.

  (** M * mat1 = M *)
  Lemma mmul_1_r : forall {r c : nat} (M : mat r c), M * mat1 = M.
  Proof. intros. apply mmul_1_r. Qed.

  (** x \.* (M * N) = (x \.* M) * N. *)
  Lemma mmul_mcmul_l : forall {r c s} (x : A) (M : mat r c) (N : mat c s), 
      (x \.* M) * N = x \.* (M * N).
  Proof. intros. apply mmul_mcmul_l. Qed.
  
  (** x \.* (M * N) = M * (x \.* N) *)
  Lemma mmul_mcmul_r : forall {r c s} (x : A) (M : mat r c) (N : mat c s), 
      M * (x \.* N) = x \.* (M * N).
  Proof. intros. apply mmul_mcmul_r. Qed.
  
  (** (M * N) \T = N \T * M \T *)
  Lemma mtrans_mmul : forall {r c s} (M : mat r c) (N : mat c s),
      (M * N) \T = N \T * M \T.
  Proof. intros. apply mtrans_mmul. Qed.

  (** tr (M * N) = tr (N * M) *)
  Lemma mtrace_mmul : forall {r c} (M : mat r c) (N : mat c r), tr (M * N) = tr (N * M).
  Proof. intros. apply mtrace_mmul. Qed.
  
  (* ======================================================================= *)
  (** ** Matrix multiply vector (treat vector as column vector) *)

  Definition mmulv {r c : nat} (M : mat r c) (a : vec c) : vec r :=
    @mmulv _ Aadd 0 Amul _ _ M a.
  Infix "*v" := mmulv : mat_scope.

  (** (M *v a)[i] = <row M i, a> *)
  Lemma vnth_mmulv : forall {r c} (M : mat r c) (a : vec c) i,
      (M *v a).[i] = <M.[i], a>.
  Proof. intros. apply vnth_mmulv. Qed.

  (** (M * N) *v a = M *v (N *v a) *)
  Lemma mmulv_assoc : forall {m n r} (M : mat m n) (N : mat n r) (a : vec r),
      (M * N) *v a = M *v (N *v a).
  Proof. intros. apply mmulv_assoc. Qed.

  (** M *v (a + b) = M *v a + M *v b *)
  Lemma mmulv_vadd : forall {r c} (M : mat r c) (a b : vec c),
      M *v (a + b)%V = (M *v a + M *v b)%V.
  Proof. intros. apply mmulv_vadd. Qed.
  
  (** (M + N) *v a = M *v a + N *v a *)
  Lemma mmulv_madd : forall {r c} (M N : mat r c) (a : vec c),
      (M + N) *v a = (M *v a + N *v a)%V.
  Proof. intros. apply mmulv_madd. Qed.

  (** (- M) *v a = - (M *v a) *)
  Lemma mmulv_mopp : forall {r c} (M : mat r c) (a : vec c),
      (- M) *v a = (- (M *v a))%V.
  Proof. intros. apply mmulv_mopp. Qed.

  (** M *v (- a) = - (M *v a) *)
  Lemma mmulv_vopp : forall {r c} (M : mat r c) (a : vec c),
      M *v (- a)%V = (- (M *v a))%V.
  Proof. intros. apply mmulv_vopp. Qed.

  (** M *v (a - b) = M *v a - M *v b *)
  Lemma mmulv_vsub : forall {r c} (M : mat r c) (a b : vec c),
      M *v (a - b)%V = (M *v a - M *v b)%V.
  Proof. intros. apply mmulv_vsub. Qed.
  
  (** (M - N) *v a = M *v a - N *v a *)
  Lemma mmulv_msub : forall {r c} (M N : mat r c) (a : vec c),
      (M - N) *v a = (M *v a - N *v a)%V.
  Proof. intros. apply mmulv_msub. Qed.
  
  (** 0 *v a = 0 *)
  Lemma mmulv_0_l : forall {r c} (a : vec c), (@mat0 r c) *v a = vzero.
  Proof. intros. apply mmulv_0_l. Qed.
  
  (** M *v 0 = 0 *)
  Lemma mmulv_0_r : forall {r c} (M : mat r c), M *v vzero = vzero.
  Proof. intros. apply mmulv_0_r. Qed.
  
  (** 1 *v a = a *)
  Lemma mmulv_1_l : forall {n} (a : vec n), mat1 *v a = a.
  Proof. intros. apply mmulv_1_l. Qed.

  (** (x .* M) *v a = x .* (M *v a) *)
  Lemma mmulv_mcmul : forall {r c} (x : A) (M : mat r c) (a : vec c), 
      (x \.* M) *v a = (x \.* (M *v a))%V.
  Proof. intros. apply mmulv_mcmul. Qed.
  
  (** M *v (x .* a) = x .* (M *v a) *)
  Lemma mmulv_vcmul : forall {r c} (x : A) (M : mat r c) (a : vec c), 
      M *v (x \.* a)%V = (x \.* (M *v a))%V.
  Proof. intros. apply mmulv_vcmul. Qed.

  (** <a, b> = (a\T *v b).1 *)
  Lemma vdot_eq_mmulv : forall {n} (a b : vec n), <a, b> = (v2rv a *v b).1.
  Proof. intros. apply vdot_eq_mmulv. Qed.
  
  (** v2cv (M *v a) = M * v2cv a *)
  Lemma v2cv_mmulv : forall {r c} (M : mat r c) (a : vec c),
      v2cv (M *v a) = (M * v2cv a).
  Proof. intros. apply v2cv_mmulv. Qed.

  (** v2rv (M *v a) = (v2rv a) * M\T *)
  Lemma v2rv_mmulv : forall {r c} (M : mat r c) (a : vec c),
      v2rv (M *v a) = (v2rv a * M\T).
  Proof. intros. apply v2rv_mmulv. Qed.

  (* ======================================================================= *)
  (** ** Vector multiply matrix (treat vector as row vector) *)

  Definition mvmul {r c : nat} (a : vec r) (M : mat r c) : vec c :=
    @mvmul _ Aadd 0 Amul _ _ a M.
  Infix "v*" := mvmul : mat_scope.

  (** (M v* a)[i] = <row M i, a> *)
  Lemma vnth_mvmul : forall {r c} (a : vec r) (M : mat r c) i,
      (a v* M).[i] = <a, M&[i]>.
  Proof. intros. apply vnth_mvmul. Qed.

  (** a v* (M * N) = (a v* M) v* N *)
  Lemma mvmul_assoc : forall {r c s} (a : vec r) (M : mat r c) (N : mat c s),
      a v* (M * N) = (a v* M) v* N.
  Proof. intros. apply mvmul_assoc. Qed.

  (** (a + b) v* M = a v* M + b v* M *)
  Lemma mvmul_vadd : forall {r c} (a b : vec r) (M : mat r c),
      (a + b)%V v* M = (a v* M + b v* M)%V.
  Proof. intros. apply mvmul_vadd. Qed.
  
  (** a v* (M + N) = a v* M + N v* a *)
  Lemma mvmul_madd : forall {r c} (a : vec r) (M N : mat r c),
      a v* (M + N) = (a v* M + a v* N)%V.
  Proof. intros. apply mvmul_madd. Qed.

  (** a v* (- M) = - (a v* M) *)
  Lemma mvmul_mopp : forall {r c} (a : vec r) (M : mat r c),
      a v* (- M) = (- (a v* M))%V.
  Proof. intros. apply mvmul_mopp. Qed.

  (** (- a) v* M = - (a v* M) *)
  Lemma mvmul_vopp : forall {r c} (a : vec r) (M : mat r c),
      (- a)%V v* M = (- (a v* M))%V.
  Proof. intros. apply mvmul_vopp. Qed.

  (** (a - b) v* M = a v* M - b v* M *)
  Lemma mvmul_vsub : forall {r c} (a b : vec r) (M : mat r c),
      (a - b)%V v* M = (a v* M - b v* M)%V.
  Proof. intros. apply mvmul_vsub. Qed.
  
  (** a v* (M - N) = a v* M - a v* N *)
  Lemma mvmul_msub : forall {r c} (a : vec r) (M N : mat r c),
      a v* (M - N) = (a v* M - a v* N)%V.
  Proof. intros. apply mvmul_msub. Qed.
  
  (** 0 v* M = 0 *)
  Lemma mvmul_0_l : forall {r c} (M : mat r c), vzero v* M = vzero.
  Proof. intros. apply mvmul_0_l. Qed.
  
  (** a v* 0 = 0 *)
  Lemma mvmul_0_r : forall {r c} (a : vec r), a v* (@mat0 r c) = vzero.
  Proof. intros. apply mvmul_0_r. Qed.
  
  (** a v* mat1 = a *)
  Lemma mvmul_1_r : forall {n} (a : vec n), a v* mat1 = a.
  Proof. intros. apply mvmul_1_r. Qed.

  (** a v* (x .* M) = x .* (a v* M) *)
  Lemma mvmul_mcmul : forall {r c} (a : vec r) (x : A) (M : mat r c), 
      a v* (x \.* M) = (x \.* (a v* M))%V.
  Proof. intros. apply mvmul_mcmul. Qed.
  
  (** (x .* a) v* M  = x .* (a v* M) *)
  Lemma mvmul_vcmul : forall {r c} (a : vec r) (x : A) (M : mat r c), 
      (x \.* a)%V v* M = (x \.* (a v* M))%V.
  Proof. intros. apply mvmul_vcmul. Qed.

  (** <a, b> = (a v* v2cv b).1 *)
  Lemma vdot_eq_mvmul : forall {n} (a b : vec n), <a, b> = (a v* v2cv b).1.
  Proof. intros. apply vdot_eq_mvmul. Qed.

  (** v2cv (a v* M) = v2rv a * M *)
  Lemma v2cv_mvmul : forall {r c} (a : vec r) (M : mat r c),
      v2cv (a v* M) = M\T * v2cv a.
  Proof. intros. apply v2cv_mvmul. Qed.

  (** v2rv (a v* M) = (v2rv a) * M *)
  Lemma v2rv_mvmul : forall {r c} (a : vec r) (M : mat r c),
      v2rv (a v* M) = v2rv a * M.
  Proof. intros. apply v2rv_mvmul. Qed.

  (* ======================================================================= *)
  (** ** Mixed properties about mmul, mmulv, mvmul  *)
  (*
       x x x               xy xy | bx
       x x x   y y | b     xy xy | bx
       ----- * y y | b  =  ------ ---
       a a a   y y | b     ay ay | ab
   *)
  Lemma mmul_mconsrT_mconscT_eq_mconscT :
    forall {r c s} (M1 : mat r c) (v1 : vec c) (M2 : mat c s) (v2 : vec c),
      mconsrT M1 v1 * mconscT M2 v2 =
        mconscT (mconsrT (M1 * M2) (v1 v* M2)) (vconsT (M1 *v v2) (<v1,v2>)).
  Proof. intros. apply mmul_mconsrT_mconscT_eq_mconscT. Qed.

  Lemma mmul_mconsrT_mconscT_eq_mconsrT :
    forall {r c s} (M1 : mat r c) (v1 : vec c) (M2 : mat c s) (v2 : vec c),
      mconsrT M1 v1 * mconscT M2 v2 =
        mconsrT (mconscT (M1 * M2) (M1 *v v2)) (vconsT (v1 v* M2) (<v1,v2>)).
  Proof. intros. apply mmul_mconsrT_mconscT_eq_mconsrT. Qed.
  
  
  (* ======================================================================= *)
  (** ** Skew-symmetric matrix *)
  
  (** Given matrix is skew-symmetric matrices *)
  Definition skewP {n} (M : smat n) : Prop := - M = M\T.

  (** Make suere skewP is equal to Matrix.skewP  *)
  Lemma skewP_eq : forall {n} (M : smat n), skewP M = @Matrix.skewP _ Aopp _ M.
  Proof. intros. auto. Qed.

  (* ======================================================================= *)
  (** ** Hardmard product *)

  (** Hardmard product (also known as the element-wise product, entrywise product 
      or Schur product).
      It is a binary operation that takes two matrices of the same dimensions and 
      produces another matrix of the same dimension as the operandds, where each 
      element i,j is the product of elements i,j of the original two matrices.

      The hardmard product is associative, distribute and commutative *)
  (* Definition mhp {n : nat} (M N : smat n) : smat n := mhp m1 m2 (Amul:=Amul). *)
  (* Infix "⦿" := mhp : mat_scope. *)

  (* ======================================================================= *)
  (** ** Determinant of a matrix over a ring *)

  (** Determinant of a square matrix *)
  Definition mdet {n} (M : smat n) : A := @mdet _ Aadd 0 Aopp Amul 1 _ M.
  Notation "| M |" := (mdet M) : mat_scope.

  (** |M \T| = |M| *)
  Lemma mdet_mtrans : forall {n} (M : smat n), |M \T| = |M|.
  Proof. intros. apply mdet_mtrans. Qed.

  (** |M * N| = |M| * |N| *)
  Lemma mdet_mmul : forall {n} (M N : smat n), |M * N| = (|M| * |N|)%A.
  Proof. intros. apply mdet_mmul. Qed.

  (** |mat1| = 1 *)
  Lemma mdet_mat1 : forall {n}, |@mat1 n| = 1.
  Proof. intros. apply mdet_mat1. Qed.

  (* ======================================================================= *)
  (** ** Determinant on matrix of 1-,2-, or 3-dim*)

  (** Determinant of a matrix of given dimension *)
  Definition mdet1 (M : smat 1) := mdet1 M.
  Definition mdet2 (M : smat 2) := @mdet2 _ Aadd Aopp Amul M.
  Definition mdet3 (M : smat 3) := @mdet3 _ Aadd Aopp Amul M.

  (** mdet1 M = |M| *)
  Lemma mdet1_eq_mdet : forall M, mdet1 M = |M|.
  Proof. intros. apply mdet1_eq_mdet. Qed.
  
  (** |M| <> 0 <-> mdet_exp <> 0 *)
  Lemma mdet1_neq0_iff : forall (M : smat 1), |M| <> 0 <-> M.11 <> 0.
  Proof. intros. apply mdet1_neq0_iff. Qed.

  (** mdet2 M = |M| *)
  Lemma mdet2_eq_mdet : forall M, mdet2 M = |M|.
  Proof. intros. apply mdet2_eq_mdet. Qed.

  (** |M| <> 0 <-> mdet_exp <> 0 *)
  Lemma mdet2_neq0_iff : forall (M : smat 2),
      |M| <> 0 <-> (M.11*M.22 - M.12*M.21)%A <> 0.
  Proof. intros. apply mdet2_neq0_iff. Qed.

  (** mdet3 M = |M| *)
  Lemma mdet3_eq_mdet : forall M, mdet3 M = |M|.
  Proof. intros. apply mdet3_eq_mdet. Qed.
  
  (** |M| <> 0 <-> mdet_exp <> 0 *)
  Lemma mdet3_neq0_iff : forall (M : smat 3),
      |M| <> 0 <->
         (M.11 * M.22 * M.33 - M.11 * M.23 * M.32 - 
            M.12 * M.21 * M.33 + M.12 * M.23 * M.31 + 
            M.13 * M.21 * M.32 - M.13 * M.22 * M.31)%A <> 0.
  Proof. intros. apply mdet3_neq0_iff. Qed.
  
  (* ======================================================================= *)
  (** ** Adjoint matrix (Adjugate matrix, adj(A), A* ) *)
  
  (** Adjoint matrix: adj(A)[i,j] = algebraic remainder of A[i,j]. *)
  Definition madj {n} (M : smat n) : smat n :=
    @madj _ Aadd 0 Aopp Amul 1 _ M.
  Notation "M \A" := (madj M) : mat_scope.

  (* ======================================================================= *)
  (** ** Invertible matrix *)

  (** A square matrix is invertible, if exists an inverse matrix *)
  Definition minvtble {n} (M : smat n) : Prop := @minvtble _ Aadd 0 Amul 1 _ M.

  (** The matrix `M` has a left inverse under matrix multiplication *)
  Definition minvtbleL {n} (M : smat n) : Prop := @minvtbleL _ Aadd 0 Amul 1 _ M.

  (** The matrix `M` has a right inverse under matrix multiplication *)
  Definition minvtbleR {n} (M : smat n) : Prop := @minvtbleR _ Aadd 0 Amul 1 _ M.
  
  (** The matrix `M` is singular (degenerate, not invertible) *)
  Definition msingular {n} (M : smat n) : Prop := ~(minvtble M).

  (** matrix `M` is invertible, imply `M` is left invertible *)
  Lemma minvtble_imply_minvtbleL : forall {n} (M : smat n),
      minvtble M -> minvtbleL M.
  Proof. intros. apply minvtble_imply_minvtbleL; auto. Qed.

  (** matrix `M` is invertible, imply `M` is right invertible *)
  Lemma minvtble_imply_minvtbleR : forall {n} (M : smat n),
      minvtble M -> minvtbleR M.
  Proof. intros. apply minvtble_imply_minvtbleR; auto. Qed.

  
End RingMatrixTheory.


(* ######################################################################### *)
(** * Ordered ring matrix theory *)
Module OrderedRingMatrixTheory (E : OrderedRingElementType).

  Include (RingMatrixTheory E).

  Open Scope vec_scope.
  
  (** 0 <= <a, a> *)
  Lemma vdot_ge0 : forall {n} (a : vec n), 0 <= (<a, a>).
  Proof. intros. apply vdot_ge0. Qed.
  
  (** <a, b>² <= <a, b> * <a, a> *)
  Lemma vdot_sqr_le : forall {n} (a b : vec n), (<a, b>²) <= (<a, a> * <b, b>)%A.
  Proof. intros. apply vdot_sqr_le. Qed.

  (** (a i)² <= <a, a> *)
  Lemma vnth_sqr_le_vdot : forall {n} (a : vec n) (i : fin n), (a i) ² <= <a, a>.
  Proof. intros. apply vnth_sqr_le_vdot. Qed.

  (** (∀ i, 0 <= a.i) -> a.i <= ∑a *)
  Lemma vsum_ge_any : forall {n} (a : vec n) i, (forall i, 0 <= a.[i]) -> a.[i] <= vsum a.
  Proof. intros. apply vsum_ge_any; auto. Qed.
  
  (** (∀ i, 0 <= a.i) -> 0 <= ∑a *)
  Lemma vsum_ge0 : forall {n} (a : vec n), (forall i, 0 <= a.[i]) -> 0 <= vsum a.
  Proof. intros. apply vsum_ge0; auto. Qed.
  
  (** (∀ i, 0 <= a.i) -> (∃ i, a.i <> 0) -> 0 < ∑a *)
  Lemma vsum_gt0 : forall {n} (a : vec n),
      (forall i, 0 <= a.[i]) -> (exists i, a.[i] <> 0) -> 0 < vsum a.
  Proof. intros. apply vsum_gt0; auto. Qed.

End OrderedRingMatrixTheory.


(* ######################################################################### *)
(** * Field matrix theory *)

Module FieldMatrixTheory (E : FieldElementType).
  
  Include (RingMatrixTheory E).
  
  Module AM := MinvMoreAM E.
  Module GE := MinvMoreGE E.
  Module OrthAM := MatrixOrth E.
  Import OrthAM.

  Open Scope vec_scope.

  (* ======================================================================= *)
  (** ** Properties about veye *)
    
  (** veye <> 0 *)
  Lemma veye_neq0 : forall {n} i, @veye n i <> vzero.
  Proof. intros. apply veye_neq0. apply field_1_neq_0. Qed.


  (* ======================================================================= *)
  (** ** Properties about vcmul *)
  
  (** x .* a = 0 -> (k = 0) \/ (v = 0) *)
  Lemma vcmul_eq0_imply_x0_or_v0 : forall {n} x (a : vec n),
      x \.* a = vzero -> (x = 0) \/ (a = vzero).
  Proof. intros. apply vcmul_eq0_imply_x0_or_v0; auto. Qed.

  (** x .* a = 0 -> a <> 0 -> x = 0 *)
  Lemma vcmul_eq0_imply_x0 : forall {n} (x : A) (a : vec n),
      x \.* a = vzero -> a <> vzero -> x = 0.
  Proof. intros. apply (vcmul_eq0_imply_x0 x a); auto. Qed.

  (** x .* a = 0 -> x <> 0 -> a = 0 *)
  Lemma vcmul_eq0_imply_v0 : forall {n} (x : A) (a : vec n),
      x \.* a = vzero -> x <> 0 -> a = vzero.
  Proof. intros. apply (vcmul_eq0_imply_v0 x a); auto. Qed.
  
  (** x .* a = a -> x = 1 \/ a = 0 *)
  Lemma vcmul_same_imply_x1_or_v0 : forall {n} (x : A) (a : vec n),
      x \.* a = a -> (x = 1 \/ a = vzero).
  Proof. intros. apply vcmul_same_imply_x1_or_v0; auto. Qed.
  
  (** x = 1 \/ a = 0 -> x .* a = a *)
  Lemma vcmul_same_if_x1_or_v0 : forall {n} (x : A) (a : vec n),
      (x = 1 \/ a = vzero) -> x \.* a = a.
  Proof. intros. apply vcmul_same_if_x1_or_v0; auto. Qed.
  
  (** x .* a = a -> a <> 0 -> x = 1 *)
  Lemma vcmul_same_imply_x1 : forall {n} (x : A) (a : vec n),
      x \.* a = a -> a <> vzero -> x = 1.
  Proof. intros. apply (vcmul_same_imply_x1 x a); auto. Qed.
  
  (** x .* a = a -> x <> 1 -> a = 0 *)
  Lemma vcmul_same_imply_v0 : forall {n} (x : A) (a : vec n),
      x \.* a = a -> x <> 1 -> a = vzero.
  Proof. intros. apply (vcmul_same_imply_v0 x a); auto. Qed.

  (** x .* a = y .* a -> (x = y \/ a = 0) *)
  Lemma vcmul_sameV_imply_eqX_or_v0 : forall {n} (x y : A) (a : vec n), 
      x \.* a = y \.* a -> (x = y \/ a = vzero).
  Proof. intros. apply vcmul_sameV_imply_eqX_or_v0; auto. Qed.

  (** x .* a = y .* a -> a <> 0 -> x = y *)
  Lemma vcmul_sameV_imply_eqX : forall {n} (x y : A) (a : vec n), 
      x \.* a = y \.* a -> a <> vzero -> x = y.
  Proof. intros. apply vcmul_sameV_imply_eqX in H; auto. Qed.

  (** x .* a = y .* a -> x <> y -> a = 0 *)
  Lemma vcmul_sameV_imply_v0 : forall {n} (x y : A) (a : vec n), 
      x \.* a = y \.* a -> x <> y -> a = vzero.
  Proof. intros. apply vcmul_sameV_imply_v0 in H; auto. Qed.

  (** (x .* a) _|_ b <-> a _|_ b *)
  Lemma vorth_vcmul_l : forall {n} x (a b : vec n),
      x <> 0 -> ((x \.* a) _|_ b <-> a _|_ b).
  Proof. intros. apply vorth_vcmul_l; auto. Qed.
  
  (** a _|_ (x .* b) <-> a _|_ b *)
  Lemma vorth_vcmul_r : forall {n} x (a b : vec n),
      x <> 0 -> (a _|_ (x \.* b) <-> a _|_ b).
  Proof. intros. apply vorth_vcmul_r; auto. Qed.

  (* ======================================================================= *)
  (** ** Projection component of a vector onto another *)
  
  (** The projection component of a onto b *)
  Definition vproj {n} (a b : vec n) : vec n := @vproj _ Aadd 0 Amul Ainv _ a b.

  (** a _|_ b -> vproj a b = vzero *)
  Lemma vorth_imply_vproj_eq0 : forall {n} (a b : vec n), a _|_ b -> vproj a b = vzero.
  Proof. intros. apply vorth_imply_vproj_eq0; auto. Qed.

  (** vunit b -> vproj a b = <a, b> \.* b *)
  Lemma vproj_vunit : forall {n} (a b : vec n), vunit b -> vproj a b = <a, b> \.* b.
  Proof. intros. apply vproj_vunit; auto. Qed.
  
  (* ======================================================================= *)
  (** ** Perpendicular component of a vector respect to another *)
  
  (** The perpendicular component of b respect to a *)
  Definition vperp {n} (a b : vec n) : vec n :=
    @vperp _ Aadd 0 Aopp Amul Ainv _ a b.

  (** vperp a b = a - vproj a b *)
  Lemma vperp_eq_minus_vproj : forall {n} (a b : vec n), vperp a b = a - vproj a b.
  Proof. intros; apply vperp_eq_minus_vproj. Qed.

  (** vproj a b = a - vperp a b *)
  Lemma vproj_eq_minus_vperp : forall {n} (a b : vec n), vproj a b = a - vperp a b.
  Proof. intros; apply vproj_eq_minus_vperp. Qed.

  (** (vproj a b) + (vperp a b) = a *)
  Lemma vproj_plus_vperp : forall {n} (a b : vec n), vproj a b + vperp a b = a.
  Proof. intros; apply vproj_plus_vperp. Qed.

  (** a _|_ b -> vperp a b = a *)
  Lemma vorth_imply_vperp_eq_l : forall {n} (a b : vec n), a _|_ b -> vperp a b = a.
  Proof. intros. apply vorth_imply_vperp_eq_l; auto. Qed.
  
  (* ======================================================================= *)
  (** ** un-sorted properties about vector *)

  (** The unit vector cannot be zero vector *)
  Lemma vunit_neq0 : forall {n} (a : vec n), vunit a -> a <> vzero.
  Proof. intros. apply vunit_neq0; auto. Qed.

  
  Open Scope mat_scope.
  
  (* ======================================================================= *)
  (** ** Properties about zero or non-zero matrices *)

  (** x .* M = 0 -> (x = 0) \/ (M = 0) *)
  Lemma mcmul_eq0_imply_x0_or_m0 : forall {r c} (M : mat r c) x,
      x \.* M = mat0 -> x = 0 \/ (M = mat0).
  Proof. intros. apply mcmul_eq0_imply_x0_or_m0; auto. Qed.

  (** (M <> 0 /\ x .* M = 0) -> M = 0 *)
  Lemma mcmul_mnonzero_eq0_imply_x0 : forall {r c} (M : mat r c) x,
      M <> mat0 -> x \.* M = mat0 -> x = 0.
  Proof. intros. apply mcmul_mnonzero_eq0_imply_x0 with (M:=M); auto. Qed.

  (** x .* M = M -> x = 1 \/ M = 0 *)
  Lemma mcmul_same_imply_x1_or_m0 : forall {r c} x (M : mat r c),
      x \.* M = M -> x = 1 \/ (M = mat0).
  Proof. intros. apply mcmul_same_imply_x1_or_m0; auto. Qed.

  (* ======================================================================= *)
  (** ** Determinant of a matrix over a field *)

  (** M * N = mat1 -> |M| <> 0 *)
  Lemma mmul_eq1_imply_mdet_neq0_l : forall {n} (M N : smat n),
      M * N = mat1 -> |M| <> 0.
  Proof. intros. apply mmul_eq1_imply_mdet_neq0_l in H; auto. Qed.
    
  (** M * N = mat1 -> |N| <> 0 *)
  Lemma mmul_eq1_imply_mdet_neq0_r : forall {n} (M N : smat n),
      M * N = mat1 -> |N| <> 0.
  Proof. intros. apply mmul_eq1_imply_mdet_neq0_r in H; auto. Qed.

  (* ======================================================================= *)
  (** ** Cramer rule *)
  
  (** Cramer rule, which can solve the equation with the form of C*x=b.
      Note, the result is valid only when |C| is not zero *)
  Definition cramerRule {n} (C : smat n) (b : vec n) : vec n :=
    @cramerRule _ Aadd 0 Aopp Amul 1 Ainv n C b.

  (** C *v (cramerRule C b) = b *)
  Lemma cramerRule_spec : forall {n} (C : smat n) (b : vec n),
  |C| <> 0 -> C *v (cramerRule C b) = b.
  Proof. intros. apply cramerRule_spec; auto. Qed.

  (** Cramer rule over list *)
  Definition cramerRuleList (n : nat) (lC : dlist A) (lb : list A) : list A :=
    @cramerRuleList _ Aadd 0 Aopp Amul 1 Ainv n lC lb.

  (** {cramerRuleList lC lb} = cramerRule {lC} {lb} *)
  Lemma cramerRuleList_spec : forall n (lC : dlist A) (lb : list A),
      let C : smat n := l2m lC in
      let b : vec n := l2v lb in
      l2v (cramerRuleList n lC lb) = cramerRule C b.
  Proof. intros. apply cramerRuleList_spec. Qed.
  
  (* ======================================================================= *)
  (** ** Invertible matrix *)

  (** matrix `M` is left invertible, if and only if the determinant is not zero *)
  Lemma minvtbleL_iff_mdet_neq0 : forall {n} (M : smat n), minvtbleL M <-> |M| <> 0.
  Proof. intros. apply minvtbleL_iff_mdet_neq0. Qed.

  (** matrix `M` is right invertible, if and only if the determinant is not zero *)
  Lemma minvtbleR_iff_mdet_neq0 : forall {n} (M : smat n), minvtbleR M <-> |M| <> 0.
  Proof. intros. apply minvtbleR_iff_mdet_neq0. Qed.

  (** A matrix `M` is invertible, if and only if the determinant is not zero *)
  Lemma minvtble_iff_mdet_neq0 : forall {n} (M : smat n), minvtble M <-> |M| <> 0.
  Proof. intros. apply minvtble_iff_mdet_neq0. Qed.

  (** matrix `M` is left invertible, imply `M` is invertible *)
  Lemma minvtbleL_imply_minvtble : forall {n} (M : smat n),
      minvtbleL M -> minvtble M.
  Proof. intros. apply minvtbleL_imply_minvtble; auto. Qed.

  (** matrix `M` is right invertible, imply `M` is invertible *)
  Lemma minvtbleR_imply_minvtble : forall {n} (M : smat n),
      minvtbleR M -> minvtble M.
  Proof. intros. apply minvtbleR_imply_minvtble; auto. Qed.

  (** matrix `M` is invertible, if and only if `M` is left invertible *)
  Lemma minvtble_iff_minvtbleL : forall {n} (M : smat n),
      minvtble M <-> minvtbleL M.
  Proof. intros. apply minvtble_iff_minvtbleL. Qed.

  (** matrix `M` is invertible, if and only if `M` is right invertible *)
  Lemma minvtble_iff_minvtbleR : forall {n} (M : smat n),
      minvtble M <-> minvtbleR M.
  Proof. intros. apply minvtble_iff_minvtbleR. Qed.

  (** matrix `M` is left invertible, if and only if `M` is right invertible *)
  Lemma minvtbleL_iff_minvtbleR : forall {n} (M : smat n),
      minvtbleL M <-> minvtbleR M.
  Proof. intros. apply minvtbleL_iff_minvtbleR. Qed.

  (** `M * N = mat1` imply `M` is invertible *)
  Lemma mmul_eq1_imply_minvtble_l : forall {n} (M N : smat n),
      M * N = mat1 -> minvtble M.
  Proof. intros. apply mmul_eq1_imply_minvtble_l in H; auto. Qed.

  (** `M * N = mat1` imply `N` is invertible *)
  Lemma mmul_eq1_imply_minvtble_r : forall {n} (M N : smat n),
      M * N = mat1 -> minvtble N.
  Proof. intros. apply mmul_eq1_imply_minvtble_r in H; auto. Qed.

  (** Transpose preserve `invertible` property *)
  Lemma mtrans_minvtble : forall n (M : smat n),
      minvtble M -> minvtble (M\T).
  Proof. intros. apply mtrans_minvtble; auto. Qed.

  (** Multiplication preserve `invertible` property *)
  Lemma mmul_minvtble: forall {n} (M N : smat n), 
      minvtble M -> minvtble N -> minvtble (M * N).
  Proof. intros. apply mmul_minvtble; auto. Qed.

  (** mat1 is invertible *)
  Lemma mat1_minvtble : forall {n}, minvtble (@mat1 n).
  Proof. intros. apply mat1_minvtble; auto. Qed.

  (** Left cancellation law of matrix multiplication *)
  Lemma mmul_cancel_l : forall {r c} (M : smat r) (N1 N2 : mat r c) ,
      minvtble M -> M * N1 = M * N2 -> N1 = N2.
  Proof. intros. apply mmul_cancel_l in H0; auto. Qed.

  (** Right cancellation law of matrix multiplication *)
  Lemma mmul_cancel_r : forall {r c} (M : smat c) (N1 N2 : mat r c) ,
      minvtble M -> N1 * M = N2 * M -> N1 = N2.
  Proof. intros. apply mmul_cancel_r in H0; auto. Qed.

  (** Cancellation law of matrix multiply vector *)
  Lemma mmulv_cancel : forall {n} (M : smat n) (a b : vec n),
      minvtble M -> M *v a = M *v b -> a = b.
  Proof. intros. apply mmulv_cancel in H0; auto. Qed.

  (** Cancellation law of vector multipliy matrix *)
  Lemma mvmul_cancel : forall {n} (M : smat n) (a b : vec n),
      minvtble M -> a v* M = b v* M -> a = b.
  Proof. intros. apply mvmul_cancel in H0; auto. Qed.

  (** N1 * M = mat1 -> N2 * M = mat1 -> N1 = N2 *)
  Lemma mmul_eq1_uniq_l : forall {n} (M N1 N2 : smat n),
      N1 * M = mat1 -> N2 * M = mat1 -> N1 = N2.
  Proof. intros. apply mmul_eq1_uniq_l with (M:=M); auto. Qed.

  (** M * N1 = mat1 -> M * N2 = mat1 -> N1 = N2 *)
  Lemma mmul_eq1_uniq_r : forall {n} (M N1 N2 : smat n),
      M * N1 = mat1 -> M * N2 = mat1 -> N1 = N2.
  Proof. intros. apply mmul_eq1_uniq_r with (M:=M); auto. Qed.

  (** M * N = mat1 -> M = /|N| .* N\A *)
  Lemma mmul_eq1_imply_det_cmul_adj_l : forall {n} (M N : smat n),
      M * N = mat1 -> M = /|N| \.* N\A.
  Proof. intros. apply mmul_eq1_imply_det_cmul_adj_l; auto. Qed.

  (** M * N = mat1 -> N = /|M| .* M\A *)
  Lemma mmul_eq1_imply_det_cmul_adj_r : forall {n} (M N : smat n),
      M * N = mat1 -> N = /|M| \.* M\A.
  Proof. intros. apply mmul_eq1_imply_det_cmul_adj_r; auto. Qed.
    
  (** M1 * M2 = mat1 -> M2 * M1 = mat1 *)
  Lemma mmul_eq1_comm : forall {n} (M1 M2 : smat n),
      M1 * M2 = mat1 -> M2 * M1 = mat1.
  Proof. intros. apply mmul_eq1_comm; auto. Qed.

  (* ======================================================================= *)
  (** ** Matrix inversion by GE (Gauss Elimination) *)
  Import GE.

  (** Check the invertibility of matrix `M` *)
  Definition minvtblebGE {n} (M : smat n) : bool := minvtbleb M.

  (** minvtble M <-> minvtblebGE M = true *)
  Lemma minvtble_iff_minvtblebGE_true : forall {n} (M : smat n),
      minvtble M <-> minvtblebGE M = true.
  Proof. intros. apply minvtble_iff_minvtbleb_true. Qed.
  
  (** msingular M <-> minvtblebGE M = false *)
  Lemma msingular_iff_minvtblebGE_false : forall {n} (M : smat n),
      msingular M <-> minvtblebGE M = false.
  Proof. intros. apply msingular_iff_minvtbleb_false. Qed.

  (** Inverse matrix (option version) *)
  Definition minvoGE {n} (M : smat n) : option (smat n) := minvo M.

  (** `minvoGE` return `Some`, iff M is invertible *)
  Lemma minvoGE_Some_iff_minvtble : forall {n} (M : smat n),
      (exists M', minvoGE M = Some M') <-> minvtble M.
  Proof. intros. apply minvo_Some_iff_minvtble. Qed.

  (** `minvoGE` return `None`, iff M is singular *)
  Lemma minvoGE_None_iff_msingular : forall {n} (M : smat n),
      minvoGE M = None <-> msingular M.
  Proof. intros. apply minvo_None_iff_msingular. Qed.

  (** If `minvoGE M` return `Some M'`, then `M' * M = mat1` *)
  Lemma minvoGE_Some_imply_eq1_l : forall {n} (M M' : smat n),
      minvoGE M = Some M' -> M' * M = mat1.
  Proof. intros. apply minvo_Some_imply_eq1_l; auto. Qed.

  (** If `minvoGE M` return `Some M'`, then `M * M' = mat1` *)
  Lemma minvoGE_Some_imply_eq1_r : forall {n} (M M' : smat n),
      minvoGE M = Some M' -> M * M' = mat1.
  Proof. intros. apply minvo_Some_imply_eq1_r; auto. Qed.

  (** Inverse matrix (with identity matrix as default value) *)
  Definition minvGE {n} (M : smat n) : smat n := minv M.

  Module MinvGENotations.
    Notation "M \-1" := (minvGE M) : mat_scope.
  End MinvGENotations.

  (** If `minvoGE M` return `Some N`, then `M\-1` equal to `N` *)
  Lemma minvoGE_Some_imply_minvGE : forall {n} (M N : smat n),
      minvoGE M = Some N -> M\-1 = N.
  Proof. intros. apply minvo_Some_imply_minv; auto. Qed.

  (** If `minvoGE M` return `None`, then `M\-1` equal to `mat1` *)
  Lemma minvoGE_None_imply_minv : forall {n} (M  : smat n),
      minvoGE M = None -> M\-1 = mat1.
  Proof. intros. apply minvo_None_imply_minv; auto. Qed.
  
  (** M\-1 * M = mat1 *)
  Lemma mmul_minvGE_l : forall {n} (M : smat n), minvtble M -> M\-1 * M = mat1.
  Proof. intros. apply mmul_minv_l; auto. Qed.


  (** M * N = mat1 -> minvtblebGE M = true *)
  Lemma mmul_eq1_imply_minvtblebGE_true_l : forall {n} (M N : smat n),
      M * N = mat1 -> minvtblebGE M = true.
  Proof. intros. apply mmul_eq1_imply_minvtbleb_true_l in H; auto. Qed.

  (** M * N = mat1 -> minvtblebGE N = true. *)
  Lemma mmul_eq1_imply_minvtblebGE_true_r : forall {n} (M N : smat n),
      M * N = mat1 -> minvtblebGE N = true.
  Proof. intros. apply mmul_eq1_imply_minvtbleb_true_r in H; auto. Qed.

  (** minvtble M -> minvtble (M \-1) *)
  Lemma minvGE_minvtble : forall {n} (M : smat n),
      minvtble M -> minvtble (M\-1).
  Proof. intros. apply minv_minvtble; auto. Qed.
  
  (** M * M\-1 = mat1 *)
  Lemma mmul_minvGE_r : forall {n} (M : smat n), minvtble M -> M * M\-1 = mat1.
  Proof. intros. apply mmul_minv_r; auto. Qed.
  
  (** M * N = mat1 -> M \-1 = N *)
  Lemma mmul_eq1_imply_minvGE_l : forall {n} (M N : smat n), M * N = mat1 -> M\-1 = N.
  Proof. intros. apply mmul_eq1_imply_minv_l; auto. Qed.

  (** M * N = mat1 -> N \-1 = M *)
  Lemma mmul_eq1_imply_minvGE_r : forall {n} (M N : smat n), M * N = mat1 -> N\-1 = M.
  Proof. intros. apply mmul_eq1_imply_minv_r; auto. Qed.

  (** mat1 \-1 = mat1 *)
  Lemma minvGE_mat1 : forall n, @minv n mat1 = mat1.
  Proof. intros. apply minv_mat1. Qed.

  (** minvtble M -> M \-1 \-1 = M *)
  Lemma minvGE_minvGE : forall n (M : smat n), minvtble M -> M \-1 \-1 = M.
  Proof. intros. apply minv_minv; auto. Qed.

  (** (M * N)\-1 = (N\-1) * (M\-1) *)
  Lemma minvGE_mmul : forall n (M N : smat n),
      minvtble M -> minvtble N -> (M * N)\-1 = N\-1 * M\-1.
  Proof. intros. apply minv_mmul; auto. Qed.

  (** (M \T) \-1 = (M \-1) \T *)
  Lemma minvGE_mtrans : forall n (M : smat n),
      minvtble M -> (M \T) \-1 = (M \-1) \T.
  Proof. intros. apply minv_mtrans; auto. Qed.

  (** |M \-1| = / |M| *)
  Lemma mdet_minvGE : forall {n} (M : smat n), minvtble M -> |M\-1| = / |M|.
  Proof. intros. apply mdet_minv; auto. Qed.
  
  (** Check matrix invertibility with lists as input *)
  Definition minvtblebListGE (n : nat) (dl : dlist A) : bool :=
    minvtblebList n dl.

  (** Inverse matrix with lists for input and output *)
  Definition minvListGE (n : nat) (dl : dlist A) : dlist A :=
    minvList n dl.

  (** `minvtblebListGE` is equal to `minvtblebGE`, by definition *)
  Lemma minvtblebListGE_spec : forall (n : nat) (dl : dlist A),
      minvtblebListGE n dl = @minvtblebGE n (l2m dl).
  Proof. intros. apply minvtblebList_spec. Qed.

  (** The matrix of [minvListGE dl] is the inverse of the matrix of [dl] *)
  Lemma minvListGE_spec : forall (n : nat) (dl : dlist A),
      let M : smat n := l2m dl in
      let M' : smat n := l2m (minvListGE n dl) in
      minvtblebListGE n dl = true ->
      M' * M = mat1.
  Proof. intros. apply minvList_spec; auto. Qed.

  (** Solve the equation with the form of C*x=b. *)
  Definition solveEqGE {n} (C : smat n) (b : vec n) : vec n := solveEq C b.

  (** C *v (solveEqGE C b) = b *)
  Lemma solveEqGE_spec : forall {n} (C : smat n) (b : vec n),
      minvtble C -> C *v (solveEqGE C b) = b.
  Proof. intros. apply solveEq_spec; auto. Qed.

  (** Solve the equation with the form of C*x=b over list *)
  Definition solveEqListGE (n : nat) (lC : dlist A) (lb : list A) : list A :=
    solveEqList n lC lb.

  (** {solveEqListGE lC lb} = solveEq {lC} {lb} *)
  Lemma solveEqListGE_spec : forall n (lC : dlist A) (lb : list A),
      let C : smat n := l2m lC in
      let b : vec n := l2v lb in
      l2v (solveEqList n lC lb) = solveEqGE C b.
  Proof. intros. apply solveEqList_spec. Qed.

  (* ======================================================================= *)
  (** ** Matrix Inversion by AM *)
  Import AM.
  
  (** Check the invertibility of matrix `M` *)
  Definition minvtblebAM {n} (M : smat n) : bool := minvtbleb M.

  (** minvtble M <-> minvtblebAM M = true *)
  Lemma minvtble_iff_minvtblebAM_true : forall {n} (M : smat n),
      minvtble M <-> minvtblebAM M = true.
  Proof. intros. apply minvtble_iff_minvtbleb_true. Qed.
  
  (** msingular M <-> minvtblebAM M = false *)
  Lemma msingular_iff_minvtblebAM_false : forall {n} (M : smat n),
      msingular M <-> minvtblebAM M = false.
  Proof. intros. apply msingular_iff_minvtbleb_false. Qed.

  (** Inverse matrix (option version) *)
  Definition minvoAM {n} (M : smat n) : option (smat n) := minvo M.

  (** `minvoAM` return `Some`, iff M is invertible *)
  Lemma minvoAM_Some_iff_minvtble : forall {n} (M : smat n),
      (exists M', minvoAM M = Some M') <-> minvtble M.
  Proof. intros. apply minvo_Some_iff_minvtble. Qed.

  (** `minvoAM` return `None`, iff M is singular *)
  Lemma minvoAM_None_iff_msingular : forall {n} (M : smat n),
      minvoAM M = None <-> msingular M.
  Proof. intros. apply minvo_None_iff_msingular. Qed.

  (** If `minvoAM M` return `Some M'`, then `M' * M = mat1` *)
  Lemma minvoAM_Some_imply_eq1_l : forall {n} (M M' : smat n),
      minvoAM M = Some M' -> M' * M = mat1.
  Proof. intros. apply minvo_Some_imply_eq1_l; auto. Qed.

  (** If `minvoAM M` return `Some M'`, then `M * M' = mat1` *)
  Lemma minvoAM_Some_imply_eq1_r : forall {n} (M M' : smat n),
      minvoAM M = Some M' -> M * M' = mat1.
  Proof. intros. apply minvo_Some_imply_eq1_r; auto. Qed.

  (** Inverse matrix (with identity matrix as default value) *)
  Definition minvAM {n} (M : smat n) : smat n := minv M.

  Module Export MinvAMNotations.
    Notation "M \-1" := (minvAM M) : mat_scope.
  End MinvAMNotations.

  (** If `minvoAM M` return `Some N`, then `M\-1` equal to `N` *)
  Lemma minvoAM_Some_imply_minvAM : forall {n} (M N : smat n),
      minvoAM M = Some N -> M\-1 = N.
  Proof. intros. apply minvo_Some_imply_minv; auto. Qed.

  (** If `minvoAM M` return `None`, then `M\-1` equal to `mat1` *)
  Lemma minvoAM_None_imply_minv : forall {n} (M  : smat n),
      minvoAM M = None -> M\-1 = mat1.
  Proof. intros. apply minvo_None_imply_minv; auto. Qed.
  
  (** M\-1 * M = mat1 *)
  Lemma mmul_minvAM_l : forall {n} (M : smat n), minvtble M -> M\-1 * M = mat1.
  Proof. intros. apply mmul_minv_l; auto. Qed.

  
  (** Formula of inversion matrix on dimension-1 *)
  Definition minvAM1 (M : smat 1) : smat 1 := minv1 M.

  (** minvtble M -> minvAM1 M = M\-1 *)
  Lemma minvAM1_eq_minvAM : forall M, minvtble M -> minvAM1 M = M\-1.
  Proof. intros. apply minv1_eq_minv; auto. Qed.

  (** Formula of inversion matrix on dimension-2 *)
  Definition minvAM2 (M : smat 2) : smat 2 := minv2 M.

  (** minvtble M -> minv2 M = M\-1 *)
  Lemma minvAM2_eq_minvAM : forall M, minvtble M -> minvAM2 M = M\-1.
  Proof. intros. apply minv2_eq_minv; auto. Qed.
  
  (** Formula of inversion matrix on dimension-3 *)
  Definition minvAM3 (M : smat 3) : smat 3 := minv3 M.
  
  (** minvtble M -> minv3 M = M\-1 *)
  Lemma minvAM3_eq_minvAM : forall M, minvtble M -> minvAM3 M = M\-1.
  Proof. intros. apply minv3_eq_minv; auto. Qed.

  (** Formula of inversion matrix on dimension-4 *)
  Definition minvAM4 (M : smat 4) : smat 4 := minv4 M.
  
  (** minvtble M -> minv4 M = M\-1 *)
  Lemma minvAM4_eq_minvAM : forall M, minvtble M -> minvAM4 M = M\-1.
  Proof. intros. apply minv4_eq_minv; auto. Qed.


  (** M * N = mat1 -> minvtblebAM M = true *)
  Lemma mmul_eq1_imply_minvtblebAM_true_l : forall {n} (M N : smat n),
      M * N = mat1 -> minvtblebAM M = true.
  Proof. intros. apply mmul_eq1_imply_minvtbleb_true_l in H; auto. Qed.

  (** M * N = mat1 -> minvtblebAM N = true. *)
  Lemma mmul_eq1_imply_minvtblebAM_true_r : forall {n} (M N : smat n),
      M * N = mat1 -> minvtblebAM N = true.
  Proof. intros. apply mmul_eq1_imply_minvtbleb_true_r in H; auto. Qed.

  (** minvtble M -> minvtble (M \-1) *)
  Lemma minvAM_minvtble : forall {n} (M : smat n),
      minvtble M -> minvtble (M\-1).
  Proof. intros. apply minv_minvtble; auto. Qed.
  
  (** M * M\-1 = mat1 *)
  Lemma mmul_minvAM_r : forall {n} (M : smat n), minvtble M -> M * M\-1 = mat1.
  Proof. intros. apply mmul_minv_r; auto. Qed.
  
  (** M * N = mat1 -> M \-1 = N *)
  Lemma mmul_eq1_imply_minvAM_l : forall {n} (M N : smat n), M * N = mat1 -> M\-1 = N.
  Proof. intros. apply mmul_eq1_imply_minv_l; auto. Qed.

  (** M * N = mat1 -> N \-1 = M *)
  Lemma mmul_eq1_imply_minvAM_r : forall {n} (M N : smat n), M * N = mat1 -> N\-1 = M.
  Proof. intros. apply mmul_eq1_imply_minv_r; auto. Qed.

  (** mat1 \-1 = mat1 *)
  Lemma minvAM_mat1 : forall n, @minv n mat1 = mat1.
  Proof. intros. apply minv_mat1. Qed.

  (** minvtble M -> M \-1 \-1 = M *)
  Lemma minvAM_minvAM : forall n (M : smat n), minvtble M -> M \-1 \-1 = M.
  Proof. intros. apply minv_minv; auto. Qed.

  (** (M * N)\-1 = (N\-1) * (M\-1) *)
  Lemma minvAM_mmul : forall n (M N : smat n),
      minvtble M -> minvtble N -> (M * N)\-1 = N\-1 * M\-1.
  Proof. intros. apply minv_mmul; auto. Qed.

  (** (M \T) \-1 = (M \-1) \T *)
  Lemma minvAM_mtrans : forall n (M : smat n),
      minvtble M -> (M \T) \-1 = (M \-1) \T.
  Proof. intros. apply minv_mtrans; auto. Qed.

  (** |M \-1| = / |M| *)
  Lemma mdet_minvAM : forall {n} (M : smat n), minvtble M -> |M\-1| = / |M|.
  Proof. intros. apply mdet_minv; auto. Qed.
  
  (** Check matrix invertibility with lists as input *)
  Definition minvtblebListAM (n : nat) (dl : dlist A) : bool :=
    minvtblebList n dl.

  (** Inverse matrix with lists for input and output *)
  Definition minvListAM (n : nat) (dl : dlist A) : dlist A :=
    minvList n dl.

  (** `minvtblebListAM` is equal to `minvtblebAM`, by definition *)
  Lemma minvtblebListAM_spec : forall (n : nat) (dl : dlist A),
      minvtblebListAM n dl = @minvtblebAM n (l2m dl).
  Proof. intros. apply minvtblebList_spec. Qed.

  (** The matrix of [minvListAM dl] is the inverse of the matrix of [dl] *)
  Lemma minvListAM_spec : forall (n : nat) (dl : dlist A),
      let M : smat n := l2m dl in
      let M' : smat n := l2m (minvListAM n dl) in
      minvtblebListAM n dl = true ->
      M' * M = mat1.
  Proof. intros. apply minvList_spec; auto. Qed.

  (** Solve the equation with the form of C*x=b. *)
  Definition solveEqAM {n} (C : smat n) (b : vec n) : vec n := solveEq C b.

  (** C *v (solveEqAM C b) = b *)
  Lemma solveEqAM_spec : forall {n} (C : smat n) (b : vec n),
      minvtble C -> C *v (solveEqAM C b) = b.
  Proof. intros. apply solveEq_spec; auto. Qed.

  (** Solve the equation with the form of C*x=b over list *)
  Definition solveEqListAM (n : nat) (lC : dlist A) (lb : list A) : list A :=
    solveEqList n lC lb.

  (** {solveEqListAM lC lb} = solveEq {lC} {lb} *)
  Lemma solveEqListAM_spec : forall n (lC : dlist A) (lb : list A),
      let C : smat n := l2m lC in
      let b : vec n := l2v lb in
      l2v (solveEqList n lC lb) = solveEqAM C b.
  Proof. intros. apply solveEqList_spec. Qed.

  
  (** Inverse matrix (won't check the inversibility) *)
  Definition minvNoCheckAM {n} (M : smat n) : smat n := minvNoCheck M.

  (** If `M` is invertible, then [minvNoCheckAM] is equivalent to [minvAM] *)
  Lemma minvNoCheckAM_spec : forall {n} (M : smat n),
      minvtble M -> minvNoCheckAM M = M\-1.
  Proof. intros. apply minvNoCheck_spec; auto. Qed.

  (** Solve the equation with the form of C*x=b, but without check the inversibility. *)
  Definition solveEqNoCheckAM {n} (C : smat n) (b : vec n) : vec n :=
    (minvNoCheckAM C) *v b.

  (** minvtble C -> solveEqNoCheckAM C b = solveEqAM C b *)
  Theorem solveEqNoCheckAM_spec : forall {n} (C : smat n) (b : vec n),
      minvtble C -> solveEqNoCheckAM C b = solveEqAM C b.
  Proof. intros. apply solveEqNoCheck_spec; auto. Qed.

  (** Solve the equation with the form of C*x=b over list, but without check the 
      inversibility *)
  Definition solveEqListNoCheckAM (n : nat) (lC : dlist A) (lb : list A) : list A :=
    solveEqListNoCheck n lC lb.

  (** minvtble {lC} -> {solveEqListNoCheckAM lC lb} = solveEqListAM {lC} {lb} *)
  Theorem solveEqListNoCheckAM_spec : forall n (lC : dlist A) (lb : list A),
      let C : smat n := l2m lC in
      minvtble C -> solveEqListNoCheckAM n lC lb = solveEqListAM n lC lb.
  Proof. intros. apply solveEqListNoCheck_spec; auto. Qed.
  

  (* ======================================================================= *)
  (** ** Matrix Inversion (default method, JUST IS Notaiton of AM) *)
  Import AM.
  Import MinvAMNotations.

  Notation minvtbleb := minvtblebAM.
  Notation minvtble_iff_minvtbleb_true := minvtble_iff_minvtblebAM_true.
  Notation msingular_iff_minvtbleb_false := msingular_iff_minvtblebAM_false.
  Notation minvo := minvoAM.
  Notation minvo_Some_iff_minvtble := minvoAM_Some_iff_minvtble.
  Notation minvo_None_iff_msingular := minvoAM_None_iff_msingular.
  Notation minvo_Some_imply_eq1_l := minvoAM_Some_imply_eq1_l.
  Notation minvo_Some_imply_eq1_r := minvoAM_Some_imply_eq1_r.
  Notation minv := minvAM.
  Notation minvo_Some_imply_minv := minvoAM_Some_imply_minvAM.
  Notation minvo_None_imply_minv := minvoAM_None_imply_minv.
  Notation mmul_minv_l := mmul_minvAM_l.
  Notation mmul_minv_r := mmul_minvAM_r.
  Notation minv_minvtble := minvAM_minvtble.
  Notation mmul_eq1_imply_minv_l := mmul_eq1_imply_minvAM_l.
  Notation mmul_eq1_imply_minv_r := mmul_eq1_imply_minvAM_r.
  Notation minv_mat1 := minvAM_mat1.
  Notation minv_minv := minvAM_minvAM.
  Notation minv_mmul := minvAM_mmul.
  Notation minv_mtrans := minvAM_mtrans.
  Notation mdet_minv := mdet_minvAM.
  Notation minvtblebList := minvtblebListAM.
  Notation minvtblebList_spec := minvtblebListAM_spec.
  Notation minvList := minvListAM.
  Notation minvList_spec := minvListAM_spec.

  (* tips: we use GE model to solve equation for smaller time complexicity *)
  Notation solveEq := solveEqGE.
  Notation solveEq_spec := solveEqGE_spec.

  (* tips: only AM has NoCheck version *)  
  Notation minvNoCheck := minvNoCheckAM.
  Notation minvNoCheck_spec := minvNoCheckAM_spec.
  Notation solveEqNoCheck := solveEqNoCheckAM.
  Notation solveEqNoCheck_spec := solveEqNoCheckAM_spec.
  Notation solveEqListNoCheck := solveEqListNoCheckAM.
  Notation solveEqListNoCheck_spec := solveEqListNoCheckAM_spec.

  (* ======================================================================= *)
  (** ** Orthonormal vectors 标准正交的向量组 *)

  (** All (different) columns of a matrix are orthogonal each other.
      For example: [v1;v2;v3] => v1_|_v2 && v1_|_v3 && v2_|_v3. *)
  Definition mcolsOrth {r c} (M : mat r c) : Prop := mcolsOrth M.

  (** All (different) rows of a matrix are orthogonal each other. *)
  Definition mrowsOrth {r c} (M : mat r c) : Prop := mrowsOrth M.

  Lemma mtrans_mcolsOrth : forall {r c} (M : mat r c), mrowsOrth M -> mcolsOrth (M\T).
  Proof. intros. apply mtrans_mcolsOrth; auto. Qed.

  Lemma mtrans_mrowsOrth : forall {r c} (M : mat r c), mcolsOrth M -> mrowsOrth (M\T).
  Proof. intros. apply mtrans_mrowsOrth; auto. Qed.


  (** All columns of a matrix are unit vector.
      For example: [v1;v2;v3] => unit v1 && unit v2 && unit v3 *)
  Definition mcolsUnit {r c} (M : mat r c) : Prop := mcolsUnit M.

  (** All rows of a matrix are unit vector. *)
  Definition mrowsUnit {r c} (M : mat r c) : Prop := mrowsUnit M.

  Lemma mtrans_mcolsUnit : forall {r c} (M : mat r c), mrowsUnit M -> mcolsUnit (M\T).
  Proof. intros. apply mtrans_mcolsUnit; auto. Qed.

  Lemma mtrans_mrowsUnit : forall {r c} (M : mat r c), mcolsUnit M -> mrowsUnit (M\T).
  Proof. intros. apply mtrans_mrowsUnit; auto. Qed.


  (** The columns of a matrix is orthogomal *)
  Definition mcolsOrthonormal {r c} (M : mat r c) : Prop := mcolsOrthonormal M.

  (** The rows of a matrix is orthogomal *)
  Definition mrowsOrthonormal {r c} (M : mat r c) : Prop := mrowsOrthonormal M.

  (** mrowsOrthonormal M -> mcolsOrthonormal (M\T)  *)
  Lemma mtrans_mcolsOrthonormal : forall {r c} (M : mat r c),
      mrowsOrthonormal M -> mcolsOrthonormal (M\T).
  Proof. intros. apply mtrans_mcolsOrthonormal; auto. Qed.

  (** mcolsOrthonormal M -> mrowsOrthonormal (M\T)  *)
  Lemma mtrans_mrowsOrthonormal : forall {r c} (M : mat r c),
      mcolsOrthonormal M -> mrowsOrthonormal (M\T).
  Proof. intros. apply mtrans_mrowsOrthonormal; auto. Qed.

  
  (* ======================================================================= *)
  (** ** Orthogonal matrix *)

  (** An orthogonal matrix *)
  Definition morth {n} (M : smat n) : Prop := morth M.
  
  (** matrix M is orthogonal <-> columns of M are orthogomal *)
  Lemma morth_iff_mcolsOrthonormal : forall {n} (M : smat n),
      morth M <-> mcolsOrthonormal M.
  Proof. intros. apply morth_iff_mcolsOrthonormal. Qed.
  
  (** matrix M is orthogonal <-> rows of M are orthogomal *)
  Lemma morth_iff_mrowsOrthonormal : forall {n} (M : smat n),
      morth M <-> mrowsOrthonormal M.
  Proof. intros. apply morth_iff_mrowsOrthonormal. Qed.
  
  (** columns of M are orthonormal <-> rows of M are orthonormal *)
  Lemma mcolsOrthonormal_iff_mrowsOrthonormal : forall {n} (M : smat n),
      mcolsOrthonormal M <-> mrowsOrthonormal M.
  Proof. intros. apply mcolsOrthonormal_iff_mrowsOrthonormal. Qed.

  (** orthogonal M -> invertible M *)
  Lemma morth_minvtble : forall {n} (M : smat n), morth M -> minvtble M.
  Proof. intros. apply morth_minvtble; auto. Qed.

  (** orthogonal M -> M \-1 = M \T *)
  Lemma morth_imply_minv_eq_trans : forall {n} (M : smat n), morth M -> M\-1 = M \T.
  Proof. intros. apply morth_imply_minv_eq_trans in H; auto. Qed.

  (** M \-1 = M \T -> orthogonal M *)
  Lemma minv_eq_trans_imply_morth : forall {n} (M : smat n),
      minvtble M -> M\-1 = M \T -> morth M.
  Proof. intros. apply minv_eq_trans_imply_morth; auto. Qed.

  (** orthogonal M <-> M \T * M = mat1 *)
  Lemma morth_iff_mul_trans_l : forall {n} (M : smat n), morth M <-> M \T * M = mat1.
  Proof. intros. apply morth_iff_mul_trans_l; auto. Qed.

  (** orthogonal M <-> M * M \T = mat1 *)
  Lemma morth_iff_mul_trans_r : forall {n} (M : smat n), morth M <-> M * M \T = mat1.
  Proof. intros. apply morth_iff_mul_trans_r; auto. Qed.

  (** orthogonal mat1 *)
  Lemma morth_mat1 : forall {n}, morth (@mat1 n).
  Proof. intros. apply morth_mat1; auto. Qed.

  (** orthogonal M -> orthogonal N -> orthogonal (M * N) *)
  Lemma morth_mul : forall {n} (M N : smat n), morth M -> morth N -> morth (M * N).
  Proof. intros. apply morth_mul; auto. Qed.

  (** orthogonal M -> orthogonal M \T *)
  Lemma morth_mtrans : forall {n} (M : smat n), morth M -> morth (M \T).
  Proof. intros. apply morth_mtrans; auto. Qed.

  (** orthogonal M -> orthogonal M \-1 *)
  Lemma morth_minv : forall {n} (M : smat n), morth M -> morth (M\-1).
  Proof. intros. apply morth_minv; auto. Qed.

  (** orthogonal M -> |M| = ± 1 *)
  Lemma morth_mdet : forall {n} (M : smat n), morth M -> |M| = 1 \/ |M| = (- (1))%A.
  Proof. intros. apply morth_mdet; auto. Qed.

  (** Transformation by orthogonal matrix will keep inner-product *)
  Lemma morth_keep_dot : forall {n} (M : smat n) (a b : vec n),
      morth M -> <M *v a, M *v b> = <a, b>.
  Proof. intros. apply morth_keep_dot; auto. Qed.

  (* ======================================================================= *)
  (** ** O(n): General Orthogonal Group, General Linear Group *)
  
  (** The set of GOn *)
  Definition GOn {n : nat} := @GOn n.

  (** Additional coercion, hence the re-definition of `mat` and `GOn` *)
  Definition GOn_mat {n} (M : @GOn n) : mat n n := GOn_mat M.
  Coercion GOn_mat : GOn >-> mat.

  (** The condition to form a GOn from a matrix *)
  Definition GOnP {n} (M : smat n) : Prop := GOnP M.

  Lemma GOnP_spec : forall {n} (M : @GOn n), GOnP M.
  Proof. intros. apply GOnP_spec. Qed.

  (** Create a GOn from a matrix satisfing `GOnP` *)
  Definition mkGOn {n} (M : smat n) (H : GOnP M) : @GOn n := mkGOn M H.

  (** Multiplication of elements in GOn *)
  Definition GOn_mul {n} (M N : @GOn n) : @GOn n := GOn_mul M N.

  (** Identity element in GOn *)
  Definition GOn_1 {n} : @GOn n := GOn_1.

  (** Inverse operation of multiplication in GOn *)
  Definition GOn_inv {n} (M : @GOn n) : @GOn n := GOn_inv M.

  (** GOn_mul is associative *)
  Lemma GOn_mul_assoc : forall n, Associative (@GOn_mul n).
  Proof. intros. apply GOn_mul_assoc; auto. Qed.

  (** GOn_1 is left-identity-element of GOn_mul operation *)
  Lemma GOn_mul_id_l : forall n, IdentityLeft GOn_mul (@GOn_1 n).
  Proof. intros. apply GOn_mul_id_l. Qed.
  
  (** GOn_1 is right-identity-element of GOn_mul operation *)
  Lemma GOn_mul_id_r : forall n, IdentityRight GOn_mul (@GOn_1 n).
  Proof. intros. apply GOn_mul_id_r. Qed.

  (** GOn_inv is left-inversion of <GOn_mul,GOn_1> *)
  Lemma GOn_mul_inv_l : forall n, InverseLeft GOn_mul GOn_1 (@GOn_inv n).
  Proof. intros. apply GOn_mul_inv_l. Qed.

  (** GOn_inv is right-inversion of <GOn_mul,GOn_1> *)
  Lemma GOn_mul_inv_r : forall n, InverseRight GOn_mul GOn_1 (@GOn_inv n).
  Proof. intros. apply GOn_mul_inv_r. Qed.
  
  (** <GOn, +, 1> is a monoid *)
  Lemma GOn_Monoid : forall n, Monoid (@GOn_mul n) GOn_1.
  Proof. intros. apply GOn_Monoid. Qed.

  (** <GOn, +, 1, /x> is a group *)
  Lemma GOn_Group : forall n, Group (@GOn_mul n) GOn_1 GOn_inv.
  Proof. intros. apply GOn_Group. Qed.

  (** M \-1 = M \T *)
  Lemma GOn_imply_inv_eq_trans : forall {n} (M : @GOn n), M\-1 = (GOn_mat M) \T.
  Proof. intros. apply GOn_imply_minv_eq_trans. Qed.


  (* ======================================================================= *)
  (** ** SO(n): Special Orthogonal Group, Rotation Group *)

  (** The set of SOn *)
  Definition SOn {n: nat} := @SOn n.

  (** Additional coercion, hence the re-definition of `mat` and `SOn` *)
  Definition SOn_GOn {n} (M : @SOn n) : @GOn n := SOn_GOn M.
  Coercion SOn_GOn : SOn >-> GOn.

  (** The condition to form a SOn from a matrix *)
  Definition SOnP {n} (M : smat n) : Prop := SOnP M.

  Lemma SOnP_spec : forall {n} (M : @SOn n), SOnP M.
  Proof. intros. apply SOnP_spec. Qed.

  (** The transpose also keep SOn *)
  Lemma SOnP_mtrans : forall {n} (M : smat n), SOnP M -> SOnP (M\T).
  Proof. intros. apply SOnP_mtrans; auto. Qed.

  (** Create a SOn from a matrix satisfing `SOnP` *)
  Definition mkSOn {n} (M : smat n) (H : SOnP M) : @SOn n := mkSOn M H.

  (** Multiplication of elements in SOn *)
  Definition SOn_mul {n} (M N : @SOn n) : @SOn n := SOn_mul M N.
  
  (** Identity element in SOn *)
  Definition SOn_1 {n} : @SOn n := SOn_1.

  (** SOn_mul is associative *)
  Lemma SOn_mul_assoc : forall n, Associative (@SOn_mul n).
  Proof. intros. apply SOn_mul_assoc. Qed.

  (** SOn_1 is left-identity-element of SOn_mul operation *)
  Lemma SOn_mul_id_l : forall n, IdentityLeft SOn_mul (@SOn_1 n).
  Proof. intros. apply SOn_mul_id_l. Qed.
  
  (** SOn_1 is right-identity-element of SOn_mul operation *)
  Lemma SOn_mul_id_r : forall n, IdentityRight SOn_mul (@SOn_1 n).
  Proof. intros. apply SOn_mul_id_r. Qed.
  
  (** <SOn, +, 1> is a monoid *)
  Lemma SOn_Monoid : forall n, Monoid (@SOn_mul n) SOn_1.
  Proof. intros. apply SOn_Monoid. Qed.

  (** Inverse operation of multiplication in GOn *)
  Definition SOn_inv {n} (M : @SOn n) : @SOn n := SOn_inv M.

  (** SOn_inv is left-inversion of <SOn_mul,SOn_1> *)
  Lemma SOn_mul_inv_l : forall n, InverseLeft SOn_mul SOn_1 (@SOn_inv n).
  Proof. intros. apply SOn_mul_inv_l. Qed.

  (** SOn_inv is right-inversion of <SOn_mul,SOn_1> *)
  Lemma SOn_mul_inv_r : forall n, InverseRight SOn_mul SOn_1 (@SOn_inv n).
  Proof. intros. apply SOn_mul_inv_r. Qed.

  (** <SOn, +, 1, /x> is a group *)
  Lemma SOn_Group : forall n, Group (@SOn_mul n) SOn_1 SOn_inv.
  Proof. intros. apply SOn_Group. Qed.

  (** M \-1 = M \T *)
  Lemma SOn_minv_eq_trans : forall {n} (M : @SOn n), M\-1 = (GOn_mat M) \T.
  Proof. intros. apply SOn_minv_eq_trans. Qed.

  (** M\T * M = mat1 *)
  Lemma SOn_mul_trans_l_eq1 : forall {n} (M : @SOn n), (GOn_mat M)\T * M = mat1.
  Proof. intros. apply SOn_mul_trans_l_eq1. Qed.

  (** M * M\T = mat1 *)
  Lemma SOn_mul_trans_r_eq1 : forall {n} (M : @SOn n), M * (GOn_mat M)\T = mat1.
  Proof. intros. apply SOn_mul_trans_r_eq1. Qed.
  
End FieldMatrixTheory.


(* ######################################################################### *)
(** * Ordered field matrix theory *)
Module OrderedFieldMatrixTheory (E : OrderedFieldElementType).

  Include (FieldMatrixTheory E).

  Open Scope vec_scope.

  Section THESE_CODE_ARE_COPIED_FROM_OrderedRingMatrixTheroy.
    
    (** 0 <= <a, a> *)
    Lemma vdot_ge0 : forall {n} (a : vec n), 0 <= (<a, a>).
    Proof. intros. apply vdot_ge0. Qed.
    
    (** <a, b>² <= <a, a> * <b, b> *)
    Lemma vdot_sqr_le : forall {n} (a b : vec n), (<a, b>²) <= (<a, a> * <b, b>)%A.
    Proof. intros. apply vdot_sqr_le. Qed.

    (** (v i)² <= <a, a> *)
    Lemma vnth_sqr_le_vdot : forall {n} (a : vec n) (i : fin n), (a i) ² <= <a, a>.
    Proof. intros. apply vnth_sqr_le_vdot. Qed.

    (** (∀ i, 0 <= a.i) -> a.i <= ∑a *)
    Lemma vsum_ge_any : forall {n} (a : vec n) i, (forall i, 0 <= a.[i]) -> a.[i] <= vsum a.
    Proof. intros. apply vsum_ge_any; auto. Qed.
    
    (** (∀ i, 0 <= a.i) -> 0 <= ∑a *)
    Lemma vsum_ge0 : forall {n} (a : vec n), (forall i, 0 <= a.[i]) -> 0 <= vsum a.
    Proof. intros. apply vsum_ge0; auto. Qed.
    
    (** (∀ i, 0 <= a.i) -> (∃ i, a.i <> 0) -> 0 < ∑a *)
    Lemma vsum_gt0 : forall {n} (a : vec n),
        (forall i, 0 <= a.[i]) -> (exists i, a.[i] <> 0) -> 0 < vsum a.
    Proof. intros. apply vsum_gt0; auto. Qed.
    
  End THESE_CODE_ARE_COPIED_FROM_OrderedRingMatrixTheroy.

  (** a = 0 -> <a, a> = 0 *)
  Lemma vdot_same_eq0_if_vzero : forall {n} (a : vec n), a = vzero -> <a, a> = 0.
  Proof. intros. apply vdot_same_eq0_if_vzero; auto. Qed.
  
  (** <a, a> = 0 -> a = 0 *)
  Lemma vdot_same_eq0_then_vzero : forall {n} (a : vec n), <a, a> = 0 -> a = vzero.
  Proof. intros. apply vdot_same_eq0_then_vzero; auto. Qed.

  (** a <> vzero -> <a, a> <> 0 *)
  Lemma vdot_same_neq0_if_vnonzero : forall {n} (a : vec n), a <> vzero -> <a, a> <> 0.
  Proof. intros. apply vdot_same_neq0_if_vnonzero; auto. Qed.
  
  (** <a, a> <> 0 -> a <> vzero *)
  Lemma vdot_same_neq0_then_vnonzero : forall {n} (a : vec n), <a, a> <> 0 -> a <> vzero.
  Proof. intros. apply vdot_same_neq0_then_vnonzero; auto. Qed.

  (** 0 < <a, a> *)
  Lemma vdot_gt0 : forall {n} (a : vec n), a <> vzero -> 0 < (<a, a>).
  Proof. intros. apply vdot_gt0; auto. Qed.
  
  (** <a, b>² / (<a, a> * <b, b>) <= 1. *)
  Lemma vdot_sqr_le_form2 : forall {n} (a b : vec n),
      a <> vzero -> b <> vzero -> <a, b>² / (<a, a> * <b, b>)%A <= 1.
  Proof. intros. apply vdot_sqr_le_form2; auto. Qed.

  (** vproj (a + b) c = vproj a c + vproj b c *)
  Lemma vproj_vadd : forall {n} (a b c : vec n),
      c <> vzero -> vproj (a + b) c = vproj a c + vproj b c.
  Proof. intros. apply vproj_vadd; auto. Qed.
  
  (** vproj (x .* a) b = x .* (vproj a b) *)
  Lemma vproj_vcmul : forall {n} (a b : vec n) x,
      b <> vzero -> vproj (x \.* a) b = x \.* (vproj a b).
  Proof. intros. apply vproj_vcmul; auto. Qed.

  (** vproj a a = a *)
  Lemma vproj_same : forall {n} (a : vec n), a <> vzero -> vproj a a = a.
  Proof. intros. apply vproj_same; auto. Qed.

  (** (vproj a b) _|_ (vperp a b) *)
  Lemma vorth_vproj_vperp : forall {n} (a b : vec n),
      b <> vzero -> vproj a b _|_ vperp a b.
  Proof. intros. apply vorth_vproj_vperp; auto. Qed.

  (** vperp (a + b) c = vperp a c + vperp b c *)
  Lemma vperp_vadd : forall {n} (a b c : vec n),
      c <> vzero -> vperp (a + b) c = vperp a c + vperp b c.
  Proof. intros. apply vperp_vadd; auto. Qed.

  (** vperp (x .* a) b = x .* (vperp a b) *)
  Lemma vperp_vcmul : forall {n} (x : A) (a b : vec n),
      b <> vzero -> vperp (x \.* a) b = x \.* (vperp a b).
  Proof. intros. apply vperp_vcmul; auto. Qed.

  (** vperp a a = vzero *)
  Lemma vperp_self : forall {n} (a : vec n), a <> vzero -> vperp a a = vzero.
  Proof. intros. apply vperp_self; auto. Qed.

  (* ======================================================================= *)
  (** ** Two vectors are collinear *)

  (** Two non-zero vectors are collinear, if the components are proportional *)
  Definition vcoll {n} (a b : vec n) : Prop := @vcoll _ 0 Amul _ a b.
  Infix "//" := vcoll : vec_scope.

  (** a // a *)
  Lemma vcoll_refl : forall {n} (a : vec n), a <> vzero -> a // a.
  Proof. intros; apply vcoll_refl; auto. Qed.
  
  (** a // b -> a // u *)
  Lemma vcoll_sym : forall {n} (a b : vec n), a // b -> b // a.
  Proof. intros; apply vcoll_sym; auto. Qed.

  (** a // b -> b // c -> a // c *)
  Lemma vcoll_trans : forall {n} (a b c: vec n), a // b -> b // c -> a // c.
  Proof. intros; apply vcoll_trans with b; auto. Qed.

  (** a // b => ∃! x, x <> 0 /\ x .* a = b *)
  Lemma vcoll_imply_uniqueX : forall {n} (a b : vec n),
      a // b -> (exists ! x, x <> 0 /\ x \.* a = b).
  Proof. intros; apply vcoll_imply_uniqueX; auto. Qed.

  (** a // b -> (x \.* a) // b *)
  Lemma vcoll_vcmul_l : forall {n} x (a b : vec n), x <> 0 -> a // b -> x \.* a // b.
  Proof. intros; apply vcoll_vcmul_l; auto. Qed.

  (** a // b -> a // (x \.* b) *)
  Lemma vcoll_vcmul_r : forall {n} x (a b : vec n), x <> 0 -> a // b -> a // (x \.* b).
  Proof. intros; apply vcoll_vcmul_r; auto. Qed.

  (* ======================================================================= *)
  (** ** Two vectors are parallel (i.e., collinear with same direction) *)

  (** Two non-zero vectors are parallel, if positive proportional *)
  Definition vpara {n} (a b : vec n) : Prop := @vpara _ 0 Amul Alt _ a b.
  Infix "//+" := vpara : vec_scope.

  (** a //+ a *)
  Lemma vpara_refl : forall {n} (a : vec n), a <> vzero -> a //+ a.
  Proof. intros. apply vpara_refl; auto. Qed.
  
  (** a //+ b -> b //+ a *)
  Lemma vpara_sym : forall {n} (a b : vec n), a //+ b -> b //+ a.
  Proof. intros. apply vpara_sym; auto. Qed.

  (** a //+ b -> b //+ c -> a //+ c *)
  Lemma vpara_trans : forall {n} (a b c: vec n), a //+ b -> b //+ c -> a //+ c.
  Proof. intros. apply vpara_trans with b; auto. Qed.

  (** a //+ b => ∃! x, 0 < x /\ x .* a = b *)
  Lemma vpara_imply_uniqueX : forall {n} (a b : vec n),
      a //+ b -> (exists ! x, 0 < x /\ x \.* a = b).
  Proof. intros. apply vpara_imply_uniqueX; auto. Qed.

  (** a //+ b -> (x \.* u) //+ a *)
  Lemma vpara_vcmul_l : forall {n} x (a b : vec n),
      0 < x -> a //+ b -> x \.* a //+ b.
  Proof. intros. apply vpara_vcmul_l; auto. Qed.

  (** a //+ b -> a //+ (x .* b) *)
  Lemma vpara_vcmul_r : forall {n} x (a b : vec n),
      0 < x -> a //+ b -> a //+ (x \.* b).
  Proof. intros. apply vpara_vcmul_r; auto. Qed.

  (* ======================================================================= *)
  (** ** Two vectors are antiparallel (i.e., collinear with opposite direction) *)
  
  (** Two non-zero vectors are antiparallel, if negative proportional *)
  Definition vantipara {n} (a b : vec n) : Prop := @vantipara _ 0 Amul Alt _ a b.
  Infix "//-" := vantipara : vec_scope.

  (** a //- b -> b //- a *)
  Lemma vantipara_sym : forall {n} (a b : vec n),  a //- b -> b //- a.
  Proof. intros. apply vantipara_sym; auto. Qed.

  (** a //- b => ∃! x, x < 0 /\ x * a = b *)
  Lemma vantipara_imply_uniqueX : forall {n} (a b : vec n),
      a //- b -> (exists ! x, x < 0 /\ x \.* a = b).
  Proof. intros. apply vantipara_imply_uniqueX; auto. Qed.

  (** a //- b -> (x .* a) //- b *)
  Lemma vantipara_vcmul_l : forall {n} x (a b : vec n),
      0 < x -> a //- b -> x \.* a //- b.
  Proof. intros. apply vantipara_vcmul_l; auto. Qed.

  (** a //- b -> a //- (x .* b) *)
  Lemma vantipara_vcmul_r : forall {n} x (a b : vec n),
      0 < x -> a //- b -> a //- (x \.* b).
  Proof. intros. apply vantipara_vcmul_r; auto. Qed.
  
  (* ======================================================================= *)
  (** ** Convert between //, //+, and //-  *)
  
  (** a //+ b -> a // b *)
  Lemma vpara_imply_vcoll : forall {n} (a b : vec n), a //+ b -> a // b.
  Proof. intros. apply vpara_imply_vcoll; auto. Qed.
  
  (** a //- b -> a // b *)
  Lemma vantipara_imply_vcoll : forall {n} (a b : vec n), a //- b -> a // b.
  Proof. intros. apply vantipara_imply_vcoll; auto. Qed.
  
  (** a //+ b -> (-a) //- b *)
  Lemma vpara_imply_vantipara_opp_l : forall {n} (a b : vec n), a //+ b -> (-a) //- b.
  Proof. intros. apply vpara_imply_vantipara_opp_l; auto. Qed.
  
  (** a //+ b -> a //- (-b)*)
  Lemma vpara_imply_vantipara_opp_r : forall {n} (a b : vec n), a //+ b -> a //- (-b).
  Proof. intros. apply vpara_imply_vantipara_opp_r; auto. Qed.
  
  (** a // b -> (a //+ b) \/ (a //- b) *)
  Lemma vcoll_imply_vpara_or_vantipara : forall {n} (a b : vec n),
      a // b -> a //+ b \/ a //- b.
  Proof. intros. apply vpara_imply_vpara_or_vantipara; auto. Qed.
  
End OrderedFieldMatrixTheory.


(* ######################################################################### *)
(** * Normed ordered field matrix theory *)
Module NormedOrderedFieldMatrixTheory (E : NormedOrderedFieldElementType).
  
  Include (OrderedFieldMatrixTheory E).

  Import OrthAM.

  Open Scope vec_scope.
  
  (** Length of a vector *)
  Definition vlen {n} (a : vec n) : R := @vlen _ Aadd 0 Amul a2r _ a.
  Notation "|| a ||" := (vlen a) : vec_scope.

  (** ||vzero|| = 0 *)
  Lemma vlen_vzero : forall {n:nat}, || @vzero n || = 0%R.
  Proof. intros. apply vlen_vzero. Qed.

  (** 0 <= ||a|| *)
  Lemma vlen_ge0 : forall {n} (a : vec n), (0 <= ||a||)%R.
  Proof. intros. apply vlen_ge0. Qed.
  
  (** ||a|| = ||b|| <-> <a, a> = <b, b> *)
  Lemma vlen_eq_iff_dot_eq : forall {n} (a b : vec n), ||a|| = ||b|| <-> <a, a> = <b, b>.
  Proof. intros. apply vlen_eq_iff_dot_eq. Qed.

  (** <a, a> = ||a||² *)
  Lemma vdot_same : forall {n} (a : vec n), a2r (<a, a>) = (||a||²)%R.
  Proof. intros. apply vdot_same. Qed.

  (** |a i| <= ||a|| *)
  Lemma vnth_le_vlen : forall {n} (a : vec n) (i : fin n),
      a <> vzero -> (a2r (|a i|%A) <= ||a||)%R.
  Proof. intros. apply vnth_le_vlen; auto. Qed.

  (** || a || = 1 <-> <a, a> = 1 *)
  Lemma vlen_eq1_iff_vdot1 : forall {n} (a : vec n), ||a|| = 1%R <-> <a, a> = 1.
  Proof. intros. apply vlen_eq1_iff_vdot1. Qed.

  (** ||- a|| = ||a|| *)
  Lemma vlen_vopp : forall n (a : vec n), ||- a|| = ||a||.
  Proof. intros. apply vlen_vopp. Qed.

  (** ||x .* a|| = |k| * ||a|| *)
  Lemma vlen_vcmul : forall n x (a : vec n), ||x \.* a|| = ((a2r (|x|))%A * ||a||)%R.
  Proof. intros. apply vlen_vcmul. Qed.

  (** ||a + b||² = ||a||² + ||b||² + 2 * <a, b> *)
  Lemma vlen_sqr_vadd : forall {n} (a b : vec n),
      (||(a + b)%V||² = ||a||² + ||b||² + 2 * a2r (<a,b>))%R.
  Proof. intros. apply vlen_sqr_vadd. Qed.

  (** ||a - b||² = ||a||² + ||b||² - 2 * <a, b> *)
  Lemma vlen_sqr_vsub : forall {n} (a b : vec n),
      (||(a - b)%V||² = ||a||² + ||b||² - 2 * a2r (<a, b>))%R.
  Proof. intros. apply vlen_sqr_vsub. Qed.

  (* 柯西.许西尔兹不等式，Cauchy-Schwarz Inequality *)
  (** |<a, b>| <= ||a|| * ||b|| *)
  Lemma vdot_abs_le : forall {n} (a b : vec n), (|a2r (<a, b>)| <= ||a|| * ||b||)%R.
  Proof. intros. apply vdot_abs_le. Qed.

  (** <a, b> <= ||a|| * ||b|| *)
  Lemma vdot_le_mul_vlen : forall {n} (a b : vec n), (a2r (<a, b>) <= ||a|| * ||b||)%R.
  Proof. intros. apply vdot_le_mul_vlen. Qed.

  (** - ||a|| * ||b|| <= <a, b> *)
  Lemma vdot_ge_mul_vlen_neg : forall {n} (a b : vec n),
      (- (||a|| * ||b||) <= a2r (<a, b>))%R.
  Proof. intros. apply vdot_ge_mul_vlen_neg. Qed.

  (* 任意维度“三角形”两边长度之和大于第三边长度 *)
  (** ||a + b|| <= ||a|| + ||b|| *)
  Lemma vlen_le_add : forall {n} (a b : vec n), (||(a + b)%V|| <= ||a|| + ||b||)%R.
  Proof. intros. apply vlen_le_add. Qed.

  (* 任意维度“三角形”的任意一边的长度大于等于两边长度之差 *)
  (** ||a|| - ||b|| <= ||a + b|| *)
  Lemma vlen_ge_sub : forall {n} (a b : vec n), ((||a|| - ||b||) <= ||(a + b)%V||)%R.
  Proof. intros. apply vlen_ge_sub. Qed.

  (** ||a|| = 0 <-> a = 0 *)
  Lemma vlen_eq0_iff_eq0 : forall {n} (a : vec n), ||a|| = 0%R <-> a = vzero.
  Proof. intros. apply vlen_eq0_iff_eq0. Qed.

  (** ||a|| <> 0 <-> a <> 0 *)
  Lemma vlen_neq0_iff_neq0 : forall {n} (a : vec n), ||a|| <> 0%R <-> a <> vzero.
  Proof. intros. apply vlen_neq0_iff_neq0. Qed.

  (** a <> vzero -> 0 < ||a|| *)
  Lemma vlen_gt0 : forall {n} (a : vec n), a <> vzero -> (0 < ||a||)%R.
  Proof. intros. apply vlen_gt0; auto. Qed.
      
  (** 0 <= <a, a> *)
  Lemma vdot_same_ge0 : forall {n} (a : vec n), 0 <= <a, a>.
  Proof. intros. apply vdot_same_ge0. Qed.

  (** Verify the definition is reasonable *)
  Lemma vunit_spec : forall {n} (a : vec n), vunit a <-> ||a|| = 1%R.
  Proof. intros. apply vunit_spec. Qed.

  (* Context `{HOrderedField : OrderedField A Aadd Azero Aopp Amul Aone Ainv}. *)
  (* Context `{HConvertToR *)
  (*     : ConvertToR A Aadd Azero Aopp Amul Aone Ainv Alt Ale Altb Aleb a2r}. *)
  (* Notation vlen := (@vlen _ Aadd Azero Amul a2r). *)
  (* Notation "|| a ||" := (vlen a) : vec_scope. *)

  (** Transformation by orthogonal matrix will keep length. *)
  Lemma morth_keep_length : forall {n} (M : smat n) (a : vec n),
      morth M -> ||M *v a|| = ||a||.
  Proof. intros. apply morth_keep_length. auto. Qed.
  
  (** Transformation by orthogonal matrix will keep zero. *)
  Lemma morth_keep_nonzero : forall {n} (M : smat n) (a : vec n),
      a <> vzero -> morth M -> M *v a <> vzero.
  Proof. intros. apply morth_keep_nonzero; auto. Qed.

End NormedOrderedFieldMatrixTheory.
