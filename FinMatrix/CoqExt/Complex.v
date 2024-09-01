(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Complex number
  author    : Zhengpu Shi
  date      : 2022.06
 *)

Require Export Hierarchy ElementType.
Require Export RExt.
Open Scope R_scope.

Declare Scope C_scope.
Delimit Scope C_scope with C.
Open Scope C_scope.


(* ######################################################################### *)
(** * 1.1 Complex numbers and basic operations *)

(* ======================================================================= *)
(** ** Definition of complex number *)

Record C := mkC { Cre : R; Cim : R}.

Infix " '+i' " := mkC (at level 60) : C_scope.
Notation "z .a" := (Cre z) (at level 20, format "z .a") : C_scope.
Notation "z .b" := (Cim z) (at level 20, format "z .b") : C_scope.

(** Convert a real number to a complex number *)
Definition R2C (a : R) : C := a +i 0.
(* Coercion R2C : R >-> C. *)

(** Common constant complex numbers *)
Definition C0 := 0 +i 0.
Definition C1 := 1 +i 0.
Definition Ci := 0 +i 1.
(* Notation "0" := C0 : C_scope. *)
(* Notation "1" := C1 : C_scope. *)

Lemma Cproj_right : forall z : C, z = z.a +i z.b.
Proof. intros (a,b). auto. Qed.

Lemma Cexist_rep_complex : forall a b : R, exists x : C, x = a +i b.
Proof. intros. exists (a +i b). auto. Qed.

(** Equality of complex is decidable *)
Instance Ceq_Dec : Dec (@eq C).
Proof.
  constructor. intros (a1,b1) (a2,b2).
  destruct (Aeqdec a1 a2), (Aeqdec b1 b2); subst.
  - left; auto.
  - right; intro; inv H; easy.
  - right; intro; inv H; easy.
  - right; intro; inv H; easy.
Defined.

Lemma Ceq_iff : forall z1 z2 : C, z1 = z2 <-> z1.a = z2.a /\ z1.b = z2.b.
Proof.
  intros (a1,b1) (a2,b2). split; intros H; inv H; auto.
  simpl in *; subst. auto.
Qed.

(** Two complex numbers are neq, iff at least one components are neq *)
Lemma Cneq_iff : forall z1 z2 : C, z1 <> z2 <-> (z1.a <> z2.a \/ z1.b <> z2.b).
Proof. intros. rewrite Ceq_iff. tauto. Qed.

(** C1 <> C0 *)
Lemma C1_neq_C0 : C1 <> C0.
Proof.
  intro H. apply (proj1 (Ceq_iff _ _)) in H. simpl in *. destruct H; auto with R.
Qed.
Hint Resolve C1_neq_C0 : C.


(* ======================================================================= *)
(** ** Automation of compleax *)

(** simplify the expression contain complex numbers *)
Ltac Csimpl :=
  intros;
  repeat
    match goal with
    | z:C |- _ => destruct z as (?a,?b)
    end;
  simpl.

(** equality of complex numbers *)
Ltac Ceq :=
  Csimpl;
  apply (proj2 (Ceq_iff _ _)); (* z1.a = z2.a /\ z2.b = z2.b -> z1 = z2 *)
  split; simpl; try lra.

(** Automation for complex arithmetic *)
Ltac ca :=
  ra;
  try autorewrite with C;
  try auto with C;
  Csimpl; ra.


(* ======================================================================= *)
(** ** Injection from other type to complex *)
(** Injection from [N] to [C]*)
Definition nat2C (n : nat) : C := (INR n) +i 0.

(** Injection from [Z] to [C]*)
Definition Z2C (z : Z) : C := (IZR z) +i 0.


(* ======================================================================= *)
(** ** Square of norm of complex number *)

(** square of norm *)
Definition Cnorm2 (z : C) : R := 
  z.a * z.a + z.b * z.b.

Notation "| z |2" := (Cnorm2 z)
                       (at level 30, z at level 25, format "| z |2") : C_scope.
(** Note that, this notation is too complex, but I havn't found a simple style now *)
(* Notation "C2| z |" := (Cnorm2 z) : C_scope. *)
(* Reserved Notation "| r |"   (at level 30, r at level 25, format "| r |").  (* Rabs *) *)

(** z is zero, iff its norm2 is zero *)
Lemma C0_norm_0 : forall z, z = C0 <-> |z |2 = 0.
Proof. ca; cbv in *. inv H; ra. f_equal; ra. Qed.

(** z <> 0 <-> | z |2 <> 0 *)
Lemma Cneq0_iff_norm2_neq0 : forall z : C, z <> C0 <-> | z |2 <> 0.
Proof.
  intros. split; intros; intro.
  - apply C0_norm_0 in H0. easy.
  - apply C0_norm_0 in H0. easy.
Qed.

(** 0 <= | z |2 *)
Lemma Cnorm2_ge0 (z : C) : 0 <= | z |2.
Proof. destruct z. unfold Cnorm2; simpl. ra. Qed.

(** 0 < x*x + y*y <-> x +i y <> C0 *)
Lemma Cnorm2_pos_iff (x y : R) : (0 < x * x + y * y) <-> x +i y <> C0.
Proof.
  split; intros.
  - intro. inversion H0. subst. lra.
  - apply Cneq_iff in H. simpl in H. destruct H; ra.
Qed.

Hint Resolve Cnorm2_pos_iff : C.


(* ======================================================================= *)
(** ** Norm of complex number *)

Definition Cnorm (z : C) : R := (sqrt (Cnorm2 z)).
Notation "| z |" := (Cnorm z) : C_scope.

(** Cnorm2 z = (Cnorm z)² *)
Lemma Cnorm2_eq (z : C) : | z |2 = (| z |%C)².
Proof. unfold Cnorm. rewrite Rsqr_sqrt; auto. apply Cnorm2_ge0. Qed.

(** | 0 | = 0 *)
Lemma Cnorm_C0 : |C0| = R0.
Proof. cbv. autorewrite with R. ra. Qed.
Hint Rewrite Cnorm_C0 : C.

(** z = C0 -> | z | = 0 *)
Lemma Cnorm0_if_C0 : forall z : C, z = C0 -> | z | = 0.
Proof. ca. rewrite H. ca. Qed.
Hint Resolve Cnorm0_if_C0 : C.

(** | z | = 0 -> z = C0 *)
Lemma Cnorm0_imply_C0 : forall z : C, | z | = 0 -> z = C0.
Proof.
  ca. apply Rsqrt_plus_sqr_eq0_iff in H. simpl in H. destruct H. subst. auto.
Qed.
Hint Resolve Cnorm0_imply_C0 : C.

(** z = C0 <-> | z | = 0 *)
Lemma Cnorm0_iff_C0 : forall z : C, z = C0 <-> | z | = R0.
Proof. ca. Qed.

(** 0 <= | z | *)
Lemma Cnorm_ge0 : forall z : C, 0 <= | z |%C.
Proof. ca. unfold Cnorm. ca. Qed.
Hint Resolve Cnorm_ge0 : C.

(** z <> C0 -> 0 < | z | *)
Lemma Cnorm_gt0_if_neq0 : forall z : C, z <> C0 -> 0 < | z |%C.
Proof.
  intros. destruct (Aeqdec z C0); subst; try easy.
  destruct (Cnorm_ge0 z); auto.
  apply eq_sym, Cnorm0_iff_C0 in H0. easy.
Qed.
Hint Resolve Cnorm_gt0_if_neq0 : C.

(** z <> C0 -> | z | <> 0 *)
Lemma Cnorm_neq0_if_neq0 : forall z : C, z <> C0 -> | z | <> 0.
Proof. ca. Qed.
Hint Resolve Cnorm_neq0_if_neq0 : C.

(** | z | <> 0 -> z <> C0 *)
Lemma Cnorm_neq0_imply_neq0 : forall z : C, | z | <> 0 -> z <> C0.
Proof. ca. Qed.
Hint Resolve Cnorm_neq0_imply_neq0 : C.

(** | a +i 0 | = | a | *)
Lemma Cnorm_Cre_simpl : forall (a : R), | a +i 0 | = | a |%R.
Proof.
  intros; unfold Cnorm, Cnorm2; simpl. ca.
Qed.
Hint Rewrite Cnorm_Cre_simpl : C.

(** | 0 +i b | = | b | *)
Lemma Cnorm_Cim_simpl : forall (b : R), | 0 +i b | = | b |%R.
Proof.
  intros; unfold Cnorm, Cnorm2; simpl. ca.
Qed.
Hint Rewrite Cnorm_Cim_simpl : C.

(** | a +i b | = | b +i a | *)
Lemma Cnorm_comm : forall (a b : R), | a +i b | = | b +i a |.
Proof.
  intros; unfold Cnorm, Cnorm2. simpl. f_equal; ring.
Qed.

(** 0 < | z | -> z <> C0 *)
Lemma Cnorm_gt0_imply_neq0 : forall z : C, 0 < | z |%C -> z <> C0.
Proof.
  intros. destruct (Aeqdec z C0); auto. subst. rewrite Cnorm_C0 in H. lra.
Qed.
Hint Resolve Cnorm_gt0_imply_neq0 : C.

(** | R2C a | = | a | *)
Lemma Cnorm_R2C_Rabs : forall a : R, |R2C a| = | a |%R.
Proof. intros. unfold R2C. ca. Qed.
Hint Rewrite Cnorm_R2C_Rabs : C.

(** | | z | | = | z |, that is: | R2C (| z |) | = | z | *)
Lemma Cnorm_norm : forall z : C, | R2C (| z |%C) | = | z |.
Proof.
  ca. apply Rabs_right. apply Rle_ge. ca.
Qed.
Hint Rewrite Cnorm_norm : C.

(** | 1 | = 1 *)
Lemma Cnorm_C1 : | C1 | = 1.
Proof. unfold C1. ca. Qed.
Hint Rewrite Cnorm_C1 : C.

(** Rabs | z | = | z | *)
Lemma Rabs_Cnorm : forall z : C, | | z |%C |%R = | z |.
Proof. intro z; apply Rabs_right; apply Rle_ge; apply Cnorm_ge0. Qed.
Hint Rewrite Rabs_Cnorm : C.

(** | a | <= | a +i b | *)
Lemma Cre_le_Cnorm : forall z : C, | z.a | <= | z |%C.
Proof.
  Csimpl. unfold Cnorm,Cnorm2; simpl.
  destruct (Aeqdec b R0).
  - subst. autorewrite with R. lra.
  - apply Rle_trans with (sqrt (a * a)).
    autorewrite with R. lra. apply sqrt_le_1_alt. ra.
Qed.

(** | b | <= | a +i b | *)
Lemma Cim_le_Cnorm : forall z : C, | z.b | <= | z |%C.
Proof.
  Csimpl. unfold Cnorm,Cnorm2; simpl.
  destruct (Aeqdec a R0).
  - subst. autorewrite with R. lra.
  - apply Rle_trans with (sqrt (b * b)).
    autorewrite with R. lra. apply sqrt_le_1_alt. ra.
Qed.

(** | a +i b| <= | a | + | b | *)
Lemma Cnorm_le_Cre_Cim : forall z : C, | z |%C <= | z.a | + | z.b |.
Proof. Csimpl. unfold Cnorm, Cnorm2; simpl. apply R_neq5. Qed.

(* ======================================================================= *)
(** ** Addition of complex numbers *)
Definition Cadd (z1 : C) (z2 : C) : C := (z1.a + z2.a) +i (z1.b + z2.b).
Infix "+" := Cadd : C_scope.

Lemma Cadd_spec : forall z1 z2 : C,
    (z1 + z2).a = (z1.a + z2.a)%R /\ (z1 + z2).b = (z1.b + z2.b)%R.
Proof. Csimpl. auto. Qed.

Lemma Cre_add : forall z1 z2, (z1 + z2).a = (z1.a + z2.a)%R.
Proof. Csimpl. auto. Qed.

Lemma Cim_add : forall z1 z2, (z1 + z2).b = (z1.b + z2.b)%R.
Proof. Csimpl. auto. Qed.

Lemma Cadd_comm : forall z1 z2 : C, z1 + z2 = z2 + z1.
Proof. Ceq. Qed.

Lemma Cadd_assoc : forall a b c : C, a + b + c = a + (b + c).
Proof. Ceq. Qed.

Lemma Cadd_0_l : forall z : C, C0 + z = z.
Proof. Ceq. Qed.

Lemma Cadd_0_r : forall z : C, z + C0 = z.
Proof. Ceq. Qed.

Hint Rewrite
  Cre_add Cim_add
  Cadd_0_l Cadd_0_r
  : C.

Hint Resolve
  Cadd_comm
  Cadd_assoc
  : C.


(* ======================================================================= *)
(** ** Opposition of complex numbers *)

Definition Copp (z : C) :C := (-z.a) +i (-z.b).
Notation "- z" := (Copp z) : C_scope.

Lemma Cre_opp : forall z, (-z).a = (- z.a)%R.
Proof. Csimpl. auto. Qed.

Lemma Cim_opp : forall z, (-z).b = (- z.b)%R.
Proof. Csimpl. auto. Qed.

Lemma Copp_opp : forall z, --z = z.
Proof. Ceq. Qed.

Lemma Cadd_opp_l : forall z : C, - z + z = C0.
Proof. Ceq. Qed.

Lemma Cadd_opp_r : forall z : C, z + - z = C0.
Proof. Ceq. Qed.

(** |-z| = | z | *)
Lemma Cnorm_opp : forall z : C, | -z| = | z |.
Proof. Csimpl. unfold Copp; simpl. cbv. f_equal. ring. Qed.

Hint Rewrite
  Cre_opp Cim_opp Copp_opp
  Cadd_opp_l Cadd_opp_r
  : C.


(* ======================================================================= *)
(** ** Subtraction of complex numbers *)

Definition Csub (c1 c2 : C) : C := c1 + - c2.
Infix "-" := Csub : C_scope.

Lemma Cre_sub : forall z1 z2, (z1 - z2).a = (z1.a - z2.a)%R.
Proof. Csimpl. auto. Qed.

Lemma Cim_sub : forall z1 z2, (z1 - z2).b = (z1.b - z2.b)%R.
Proof. Csimpl. auto. Qed.

Lemma Copp_add_distr : forall z1 z2, - (z1 + z2) = -z1 - z2.
Proof. Ceq. Qed.

Lemma Copp_sub_distr : forall z1 z2, - (z1 - z2) = - z1 + z2.
Proof. Ceq. Qed.

Lemma Csub_antisym : forall z1 z2, z1 - z2 = - (z2 - z1).
Proof. Ceq. Qed.

(** |z1 - z2| = |z2 - z1| *)
Lemma Cnorm_sub_sym : forall z1 z2 : C, |z1 - z2| = |z2 - z1|.
Proof. Csimpl. cbv; f_equal; ring. Qed.

Infix "-" := Csub : C_scope.

Hint Rewrite
  Copp_add_distr
  Copp_sub_distr
  : C.

(* ======================================================================= *)
(** ** Triangle Inequalities *)
Section triangle_ineq.
  
  (** |z1 + z2| <= |z1| + |z2| *)
  (*
       \sqrt((a+c)^2+(b+d)^2) <= \sqrt(a^2+b^2) + \sqrt(c^2+d^2)
   <== (a+c)^2+(b+d)^2 <= (a^2+b^2)+(c^2+d^2) + 2\sqrt(a^2+b^2)\sqrt(c^2+d^2)
   <== ac+bd <= \sqrt((a^2+b^2)(c^2+d^2))
   <== a^2*c^2+b^2*d^2 + 2acbd <= a^2*c^2+b^2*d^2 + a^2*d^2+b^2*c^2
   <== 2acbd <= a^2*d^2+b^2*c^2
   <== 2AB <= A^2+B^2  (A=ad, B=bc)
   *)
  Lemma Cnorm_triang : forall z1 z2 : C, |z1 + z2|%C <= (|z1|%C + |z2|%C)%R.
  Proof.
    intros (a,b) (c,d). cbv.
    apply Rsqr_incr_0_var; ra. rewrite ?Rsqr_sqrt; ra.
    unfold Rsqr. ring_simplify.
    rewrite !pow2_sqrt; ra.
    rewrite (Rmult_assoc 2 (sqrt _)).
    rewrite <- sqrt_mult; ra.
    pose proof (R_neq6 a b c d). ra.
  Qed.

  (** Rabs (|z1| - |z2|) <= |z1 - z2| *)
  Lemma Cnorm_triang_rev : forall z1 z2 : C, | |z1|%C - |z2|%C | <= |z1 - z2|%C.
  Proof.
    intros z1 z2.
    (* intros (a,b) (c,d). *)
    assert (H1 : |z1 - z2 + z2|%C <= |z1 - z2|%C + |z2|%C) by (apply Cnorm_triang).
    assert (H2 : |z2 - z1 + z1|%C <= |z2 - z1|%C + |z1|%C) by (apply Cnorm_triang).
    assert (H3 : forall a b : C, a = a - b + b). Ceq.
    unfold Rabs; case Rcase_abs; intro H; ring_simplify.
    - rewrite <- H3 in H2. apply Rminus_le; apply Rle_minus in H2.
      ring_simplify in H2. rewrite Cnorm_sub_sym. lra.
    - rewrite <- H3 in H1; apply Rminus_le; apply Rle_minus in H1. lra.
  Qed.

  (** |z1| - |z2| <= |z1 - z2| *)
  Lemma Cnorm_triang_rev_l :  forall z1 z2 : C, |z1|%C - |z2|%C <= |z1 - z2|%C.
  Proof.
    intros z1 z2; apply Rle_trans with (| |z1|%C - |z2|%C |)%R.
    apply RRle_abs. apply Cnorm_triang_rev.
  Qed.

  (** |z2| - |z1| <= |z1 - z2| *)
  Lemma Cnorm_triang_rev_r :  forall z1 z2 : C, |z2|%C - |z1|%C <= |z1 - z2|%C.
  Proof.
    intros z1 z2; apply Rle_trans with (| |z2|%C - |z1|%C |%R).
    apply RRle_abs. rewrite Rabs_minus_sym. apply Cnorm_triang_rev.
  Qed.

End triangle_ineq.


(* ======================================================================= *)
(** ** Scalar multiplication of complex numbers *)

(** scalar multiplication *)
Definition Cscal (k : R) (z : C) : C := (k * z.a) +i (k * z.b).
Infix "s*" := Cscal: C_scope.

Lemma Cre_scal : forall z k, (k s* z).a = (k * z.a)%R.
Proof. intros (a,b) k; auto. Qed.

Lemma Cim_scal : forall z k, (k s* z).b = (k * z.b)%R.
Proof. intros (a,b) k; auto. Qed.

Lemma Cscal_1 : forall z : C, 1 s* z = z.
Proof. Ceq. Qed.

Lemma Cscal_add_distr_l : forall k z1 z2, k s* (z1 + z2) = k s* z1 + k s* z2.
Proof. Ceq. Qed.

Lemma Cscal_add_distr_r : forall k1 k2 z, (k1 + k2)%R s* z = k1 s* z + k2 s* z.
Proof. Ceq. Qed.

Lemma Cscal_mul_swap_l : forall k1 k2 z, (k1 * k2)%R s* z = k1 s* (k2 s* z).
Proof. Ceq. Qed.

(** |k * z| = |k| * | z | *)
(*
        |ka +i kb| = |k| * | a +i b |
    <== \sqrt((ka)^2 + (kb)^2) = |k| * \sqrt(a^2 + b^2)
    <== (ka)^2 + (kb)^2 = k^2 * (a^2 +b^2)
 *)
Lemma Cnorm_scal : forall k z, |k s* z| = (| k | * | z |%C)%R.
Proof.
  intros k (a,b). unfold Cnorm; unfold Cnorm2; simpl.
  rewrite <- sqrt_Rsqr_abs. rewrite <- sqrt_mult; ra.
  apply Rsqr_inj; ra. autorewrite with R. rewrite ?Rsqr_sqrt; ra.
Qed.


(* ======================================================================= *)
(** ** Multiplication of complex numbers *)

Definition Cmul (z1 : C) (z2 : C) : C :=
  (z1.a * z2.a - z1.b * z2.b) +i (z1.a * z2.b + z2.a * z1.b).
Infix "*" := Cmul : C_scope.

Lemma Cmul_comm : forall z1 z2 : C, z1 * z2 = z2 * z1.
Proof. Ceq. Qed.

Lemma Cmul_assoc : forall z1 z2 z3 : C, (z1 * z2) * z3 = z1 * (z2 * z3).
Proof. Ceq. Qed.

Lemma Cmul_0_l : forall z : C, C0 * z = C0 .
Proof. Ceq. Qed.

Lemma Cmul_0_r : forall z : C, z * C0 = C0.
Proof. Ceq. Qed.

Lemma Cmul_1_l : forall z : C, C1 * z = z .
Proof. Ceq. Qed.

Lemma Cmul_1_r : forall z : C, z * C1 = z .
Proof. Ceq. Qed.

Lemma Cmul_add_distr_l : forall z1 z2 z3 : C, z1 * (z2 + z3) = z1 * z2 + z1 * z3.
Proof. Ceq. Qed.

Lemma Cmul_add_distr_r : forall z1 z2 z3 : C, (z1 + z2) * z3= z1 * z3 + z2 * z3.
Proof. Ceq. Qed.

(** |z1 * z2| = |z1| * |z2| *)
(*
        | (a +i b) * (c +i d) | = |(ac-bd) +i (ad+bc)| = | a +i b | * |(c,d)|
    <== \sqrt((ac-bd)^2 + (ad+bc)^2) = \sqrt(a^2+b^2) * \sqrt(c^2+d^2)
                                     = \sqrt((a^2+b^2)*(c^2+d^2))
    <== (ac-bd)^2 + (ad+bc)^2 = (a^2+b^2)*(c^2+d^2)
    <== ring
 *)
Lemma Cnorm_Cmul : forall z1 z2 : C, |z1 * z2| = (|z1|%C * |z2|%C)%R.
Proof. intros (a,b) (c,d). cbv. rewrite <- sqrt_mult; ra. f_equal. ra. Qed.

Hint Resolve
  Cmul_comm Cmul_assoc
  Cmul_1_l Cmul_1_r
  Cmul_add_distr_l Cmul_add_distr_r
  : C.

Lemma C_ring : ring_theory C0 C1 Cadd Cmul Csub Copp eq.
Proof. constructor; intros; ca. Qed.

Add Ring C_ring_inst : C_ring.


(* ======================================================================= *)
(** ** Power on C *)

Fixpoint Cpow (z : C) (n : nat) {struct n} : C  :=
  match n with
  | 0%nat => C1
  | S m => z * (Cpow z m)
  end.

Infix "^" := Cpow : C_scope.

Lemma Cpow_0 : forall z : C, z ^ 0 = C1. 
Proof. auto. Qed.

Lemma C0_pow : forall n, (0 < n)%nat -> C0 ^ n = C0.
Proof.
  induction n; intros; auto. lia.
  destruct (Nat.eq_dec n 0).
  - rewrite e. Ceq.
  - simpl. rewrite IHn. Ceq. lia.
Qed.

Lemma Cpow_S : forall (z : C) (n : nat), z ^ (S n) = (z ^ n) * z.
Proof. intros. simpl. auto with C. Qed.

Lemma Cpow_add : forall (z : C) (n m : nat), z ^ (n + m) = z ^ n * z ^ m.
Proof.
  intros z n. induction n; intros; cbn.
  - auto with C.
  - rewrite IHn. auto with C.
Qed.

Lemma Cpow_mul : forall z n m, z ^ (n * m) = (z ^ n) ^ m.
Proof.
  intros z n m. revert n. induction m; intros; cbn.
  - rewrite Nat.mul_0_r. easy.
  - rewrite <- IHm. rewrite <- Cpow_add. f_equal. lia.
Qed.

Lemma Cpow_mul_distr_l : forall z1 z2 n, (z1 * z2) ^ n = z1 ^ n * z2 ^ n.
Proof. intros z1 z2 n. induction n; cbn; auto with C. rewrite IHn. ring. Qed.

Lemma Cpow_R2C : forall z n, (R2C z) ^ n = R2C (z ^ n).
Proof. intros z n ; induction n; auto. simpl. rewrite IHn. Ceq. Qed.	

(** | z ^ n| = | z | ^ n *)
Lemma Cnorm_pow : forall (z : C) n, |z ^ n| = ((| z |%C) ^ n)%R.
Proof.
  intros z n; induction n. apply Cnorm_C1.
  simpl; rewrite Cnorm_Cmul, IHn; reflexivity.
Qed.


(* ======================================================================= *)
(** ** Inversion of complex numbers *)

Definition Cinv (z : C) : C := (z.a / | z |2) +i (-z.b / | z |2).
Notation "/ z" := (Cinv z) : C_scope.

Lemma Cinv_rew : forall a b : R,
    (a +i b) <> C0 -> /(a +i b) = (/ (a*a + b*b)) s* (a +i - b)%R.
Proof. Ceq. cbv; lra. cbv; lra. Qed.

Lemma Cmul_inv_l : forall z : C, z <> C0 -> / z * z = C1.
Proof.
  Ceq. cbv. field. apply Rplus2_sqr_neq0. apply Cneq_iff in H. auto.
Qed.

Lemma Cmul_inv_r : forall z:C, z <> C0 -> z * /z = C1.
Proof. intros. rewrite Cmul_comm. apply Cmul_inv_l. auto. Qed.

(** Tips: A Coq-version-issue about inv_sqrt and sqrt_inv *)
Section coq_version_issue.
  
  (** There are two similiar lemmas: inv_sqrt and sqrt_inv *)
  (* Locate inv_sqrt. *)
  (* Notation Coq.Reals.R_sqrt.inv_sqrt *)
  (* Locate sqrt_inv. *)
  (* Constant Coq.Reals.R_sqrt.sqrt_inv *)
  (* Print inv_sqrt. *)
  (* Warning: Notation inv_sqrt is deprecated since 8.16. Use sqrt_inv. *)
  (* [deprecated-syntactic-definition,deprecated] *)
  (* Notation inv_sqrt := inv_sqrt_depr *)
  (* Check inv_sqrt_depr. *)
  (* inv_sqrt : forall x : R, 0 < x -> (/ sqrt x)%R = sqrt (/ x) *)
  (* Check sqrt_inv. *)
  (* sqrt_inv : forall x : R, sqrt (/ x) = (/ sqrt x)%R *)

(* 问题：
       1. 若 coq <= 8.14.0，则不包含 sqrt_inv，因此要使用 inv_sqrt
       2. 若 coq >= 8.16.0，则提示 inv_sqrt 过期，建议使用 sqrt_inv 。
       3. 这两个引理并不通用，sqrt_inv相比inv_sqrt，不必提供 0<x 的条件。
          长远来看，高版本下的引理更简洁了。
       解决：
       1. 为了同时适应二者，这里临时写一个 sqrt_inv，公理化的实现，结果是：
          coq.8.14.0 可完成编译，标准库并无此实现。
          coq.8.16.0 可完成编译，标准库已经有它的实现。
       
          待将来如果不想要这个公理化的引理，可以简单注释掉这里的定义即可。
          简单的屏蔽这个定义即可。
 *)
  
  (* Axiom sqrt_inv : forall x : R, sqrt (/ x) = (/ sqrt x)%R. *)
End coq_version_issue.

(** z <> C0 -> |/z| = / | z | *)
(*
        |/ (a +i b) | = |(a/(a^2+b^2), -b/(a^2+b^2))| = /| a +i b |
    <== \sqrt((a/(a^2+b^2))^2 + (-b/(a^2+b^2))^2) =/ (\sqrt (a^2+b^2))
    <== (a^2+b^2)/(a^2+b^2)^2 = 1/(a^2+b^2)
 *)
Lemma Cnorm_inv : forall z : C, z <> C0 -> | /z | = (/(| z |%C))%R.
Proof.
  intros (a,b) H. cbv. rewrite <- sqrt_inv. f_equal. ra.
  apply Cneq_iff in H; simpl in H. ra.
Qed.

(** z <> C0 -> (/z).a = z.a / | z |2 *)
Lemma Cre_inv (z : C) : z <> C0 -> (/ z).a = ((z.a) / | z |2)%R.
Proof. auto. Qed.

(** z <> C0 -> (/z).b = -z.b / | z |2 *)
Lemma Cim_inv_neq0 (z : C) : z <> C0 -> (/ z).b = (-z.b / | z |2)%R.
Proof. auto. Qed.

Hint Resolve
  Cmul_inv_l Cmul_inv_r
  : C.


(* ======================================================================= *)
(** ** Division of complex numbers *)

Definition Cdiv (c1 c2 : C) : C := c1 * / c2.
Infix "/" := Cdiv : C_scope.

(** z <> C0 -> /z = C1 / z *)
Lemma Cinv_eq_div (z : C) : z <> C0 -> (/ z) = (C1 / z).
Proof. Ceq. Qed.

Lemma C_field : field_theory C0 C1 Cadd Cmul Csub Copp Cdiv Cinv eq.
Proof. constructor; intros; auto with C. apply C_ring. Qed.

Add Field C_field_inst : C_field.


(* ======================================================================= *)
(** ** Conjugate of complex numbers *)

Definition Cconj (z : C) : C := (z.a) +i (-z.b).
Notation "z \*" := (Cconj z) (at level 20, format "z \*") : C_scope.

Lemma Cconj_add : forall z1 z2 : C, (z1 + z2)\* = z1\* + z2\*.
Proof. Ceq. Qed.

Lemma Cadd_conj : forall z : C, z + z\* = (2 * z.a) +i 0.
Proof. Ceq. Qed.

Lemma Cconj_sub : forall z1 z2 : C, (z1 - z2)\* = z1\* - z2\*.
Proof. Ceq. Qed.

Lemma Csub_conj : forall z : C, z - z\* = 0 +i (2 * z.b).
Proof. Ceq. Qed.

Lemma Cconj_mul : forall z1 z2 : C, (z1 * z2)\* = z1\* * z2\*.
Proof. Ceq. Qed.

(** | z\* | = | z | *)
Lemma Cnorm_conj : forall z : C, |z\*| = | z |.
Proof. Csimpl. cbv. f_equal; ring. Qed.

(* ######################################################################### *)
(** * 1.2 Triangle Representation of Complex number (复数的三角表示) *)

(** 1.2.1 Magnitude, Main argument and argument of complex number 
    (复数的模、主辐角和辐角) *)

(* ======================================================================= *)
(** ** Magnitude of complex number *)
(* Check Cnorm. *)

(** Some inequalities about real part or imaginay part of a complex number *)

Lemma Cnorm_ge_AbsCre (z : C) : | z.a | <= | z |%C.
Proof. apply Cre_le_Cnorm. Qed.

Lemma Cnorm_ge_AbsCim (z : C) : | z.b | <= | z |%C.
Proof. apply Cim_le_Cnorm. Qed.

Lemma Cnorm_le_AbsCre_plus_AbsCim (z : C) : | z |%C <= (|z.a| + |z.b|)%R.
Proof. apply Cnorm_le_Cre_Cim. Qed.

(** Main argument *)
(*
  算法伪代码：
  if (x = 0) {
    if (y < 0) { -pi/2 } else { pi/2 }
  } else {
    if (x < 0) {
      if (y < 0) { atan(y/x) - pi } else { atan(y/x) + pi }
    } else {
      atan(y/x)
    }
  }
 *)
Definition Carg (z : C) : R :=
  let x : R := Cre z in
  let y : R := Cim z in
  let r : R := atan (y / x) in
  let r1_pos : R := (PI / 2)%R in
  let r1_neg : R := (- r1_pos)%R in
  if (x =? 0)
  then (if y <? 0 then r1_neg else r1_pos)
  else (if x <? 0
        then (if y <? 0 then (r - PI)%R else (r + PI)%R)
        else r).

Notation "/_ z" := (Carg z) (at level 10) : C_scope.

(* 辐角的定义，是多值函数 (不再使用该定义，改用谓词来描述性质) *)
(* Definition CArg (z : C) (k : Z) : R := (∠z + 2 * (IZR k) * PI)%R. *)

(** Argument of a complex number *)
Definition isCArg (z : C) (theta : R) : Prop :=
  exists (k : Z), theta = (/_ z + 2 * (IZR k) * PI)%R.

(** Because, every different arguments of a complex number must have same sine and 
    cosine value, thus we should abtain same complex number.
    Therefore, we won't distinguish main argument and argument now. *)

(** Verify the definition of Carg *)

(** x > 0 -> /_ (x +i y) = atan (y/x) *)
Lemma Carg_xgt0 (x y : R) :
  x > 0 -> /_ (x +i y) = atan (y/x).
Proof.
  intros. unfold Carg. simpl.
  bdestruct (x =? 0); try lra.
  bdestruct (x <? 0); try lra.
Qed.

(** x = 0 -> y > 0 -> /_ (x +i y) = PI / 2 *)
Lemma Carg_xeq0_ygt0 (x y : R) :
  x = 0 -> y > 0 -> /_ (x +i y) = (PI / 2)%R.
Proof.
  intros. unfold Carg. simpl.
  bdestruct (x =? 0); try lra.
  bdestruct (y <? 0); try lra.
Qed.

(** x = 0 -> y < 0 -> /_ (x +i y) = (- PI / 2)%R *)
Lemma Carg_xeq0_ylt0 (x y : R) :
  x = 0 -> y < 0 -> /_ (x +i y) = (- PI / 2)%R.
Proof.
  intros. unfold Carg. simpl.
  bdestruct (x =? 0); try lra.
  bdestruct (y <? 0); try lra.
Qed.

(** x < 0 -> y >= 0 -> /_ (x +i y) = (atan (y/x) + PI)%R *)
Lemma Carg_xlt0_yge0 (x y : R) :
  x < 0 -> y >= 0 -> /_ (x +i y) = (atan (y/x) + PI)%R.
Proof.
  intros. unfold Carg. simpl.
  bdestruct (x =? 0); try lra.
  bdestruct (x <? 0); try lra.
  bdestruct (y <? 0); try lra.
Qed.

(** x < 0 -> y < 0 -> /_ (x +i y) = (atan (y/x) - PI)%R *)
Lemma Carg_xlt0_ylt0 (x y : R) :
  x < 0 -> y < 0 -> /_ (x +i y) = (atan (y/x) - PI)%R.
Proof.
  intros. unfold Carg. simpl.
  bdestruct (x =? 0); try lra.
  bdestruct (x <? 0); try lra.
  bdestruct (y <? 0); try lra.
Qed.


(** Note, this equation will be used in the proof about cos(/_  z) and sin(/_  z) *)

(** /(sqrt (1+(b/a)²)) = abs(a) / sqrt(a*a + b*b) *)
Lemma Rinv_Rsqrt_1_plus_Rsqr_b_div_a (a b : R) :
  a <> 0 -> (/ (sqrt (1+(b/a)²)) = (Rabs a) / sqrt(a*a + b*b))%R.
Proof.
  intros.
  replace (1 + (b/a)²)%R with ((a*a + b*b) / (a*a))%R; [|ra].
  rewrite sqrt_div_alt; ra. split; ra.
Qed.

(** nonzero complex number, the cosine of its main argument equal to 
    real part divide magnitude (主辐角的余弦等于实部除以模长) *)
Lemma cos_Carg_neq0 (z : C) : z <> C0 -> cos(/_ z) = (z.a / | z |%C)%R.
Proof.
  Csimpl. unfold Cnorm,Cnorm2; simpl.
  bdestruct (a >? 0).
  - rewrite Carg_xgt0; auto. rewrite cos_atan.
    unfold Rdiv at 1. rewrite Rinv_Rsqrt_1_plus_Rsqr_b_div_a; ra.
    rewrite Rabs_right; ra.
  - bdestruct (a =? 0); subst.
    + bdestruct (b >? 0).
      * rewrite Carg_xeq0_ygt0; ra.
      * apply Cneq_iff in H; simpl in H. assert (b < 0) by ra.
        rewrite Carg_xeq0_ylt0; ra.
    + bdestruct (b >=? 0).
      * rewrite Carg_xlt0_yge0; ra. rewrite cos_atan.
        unfold Rdiv at 1. rewrite Rinv_Rsqrt_1_plus_Rsqr_b_div_a; ra.
        rewrite Rabs_left1 by lra. ra.
      * rewrite Carg_xlt0_ylt0; ra. rewrite cos_atan.
        unfold Rdiv at 1. rewrite Rinv_Rsqrt_1_plus_Rsqr_b_div_a; ra.
        rewrite Rabs_left1 by lra. ra.
Qed.

(** nonzero complex number, the sine of its main argument equal to 
    imaginary part divide magnitude (主辐角的正弦等于虚部除以模长) *)
Lemma sin_Carg_neq0 (z : C) : z <> C0 -> sin(/_ z) = ((Cim z) / | z |%C)%R.
Proof.
  Csimpl. unfold Cnorm,Cnorm2; simpl.
  bdestruct (a >? 0).
  - rewrite Carg_xgt0; auto. rewrite sin_atan.
    unfold Rdiv at 1. rewrite Rinv_Rsqrt_1_plus_Rsqr_b_div_a; ra.
    rewrite Rabs_right; ra.
  - bdestruct (a =? 0); subst.
    + bdestruct (b >? 0).
      * rewrite Carg_xeq0_ygt0; ra.
      * apply Cneq_iff in H; simpl in H. assert (b < 0) by ra.
        rewrite Carg_xeq0_ylt0; ra. symmetry. ra.
    + bdestruct (b >=? 0).
      * rewrite Carg_xlt0_yge0; ra. rewrite sin_atan.
        unfold Rdiv at 1. rewrite Rinv_Rsqrt_1_plus_Rsqr_b_div_a; ra.
        rewrite Rabs_left1 by lra. ra.
      * rewrite Carg_xlt0_ylt0; ra. rewrite sin_atan.
        unfold Rdiv at 1. rewrite Rinv_Rsqrt_1_plus_Rsqr_b_div_a; ra.
        rewrite Rabs_left1 by lra. ra.
Qed.

(** 非零复数的主辐角的正切表达式 *)
Lemma tan_Carg_neq0 (z : C) : z.a <> 0%R -> tan(/_ z) = ((Cim z) / Cre z)%R.
Proof.
  intros.
  assert (z <> C0). apply Cneq_iff; auto.
  rewrite tan_eq.
  rewrite cos_Carg_neq0, sin_Carg_neq0; auto. field. split; auto.
  apply Cnorm_neq0_if_neq0; auto.
Qed.

(** 非零复数实部等于模乘以辐角余弦 *)
Lemma Cre_eq_Cnorm_mul_cos_Carg (z : C) : z <> C0 -> z.a = (| z |%C * cos(/_ z))%R.
Proof.
  intros. rewrite cos_Carg_neq0; auto. field. apply Cnorm_neq0_if_neq0 in H; auto.
Qed.

(** 非零复数虚部等于模乘以辐角正弦 *)
Lemma Cim_eq_Cnorm_mul_sin_Carg (z : C) : z <> C0 -> z.b = (| z |%C * sin(/_ z))%R.
Proof.
  intros. rewrite sin_Carg_neq0; auto. field. apply Cnorm_neq0_if_neq0; auto.
Qed.

(** 非零复数，(相等 <-> 模长和辐角相等) *)
Lemma Cneq0_eq_iff_Cnorm_Carg (z1 z2 : C) (H1 : z1 <> C0) (H2 : z2 <> C0) :
  z1 = z2 <-> (|z1| = |z2|) /\ (/_  z1 = /_  z2).
Proof.
  split; intros. subst; auto.
  destruct H. apply Ceq_iff.
  repeat rewrite Cre_eq_Cnorm_mul_cos_Carg, Cim_eq_Cnorm_mul_sin_Carg; auto.
  rewrite H,H0. auto.
Qed.


(* ======================================================================= *)
(** ** 1.2.2 复数模的三角不等式 *)

Lemma CnormCadd_le_CaddCnorm (z1 z2 : C) : |z1 + z2|%C <= |z1|%C + |z2|%C.
Proof. apply Cnorm_triang. Qed.

Lemma CnormCadd_ge_AbsSubCnorm (z1 z2 : C) : | |z1|%C - |z2|%C | <= |z1 + z2|%C.
Proof.
Admitted.

Lemma CnormCsub_le_CaddCnorm (z1 z2 : C) : |z1 - z2|%C <= |z1|%C + |z2|%C.
Proof.
Admitted.

Lemma CnormCsub_ge_AbsSubCnorm (z1 z2 : C) : | |z1|%C - |z2|%C | <= |z1 - z2|%C.
Proof. apply Cnorm_triang_rev. Qed.


(* ======================================================================= *)
(** ** 1.2.3 复数的三角表示 *)

(** 复数三角表示的定义 *)
Definition Ctrigo (r θ : R) : C := r s* (cos θ +i sin θ).
Infix "^^" := Ctrigo (at level 30) : C_scope.

(** 复数三角表示的重写形式 *)
(* Definition Ctrigo_rew (z : C) : C := Ctrigo | z | (/_  z). *)

(* (** 任意正整数r和实数θ，则存在一个复数z的三角表示如下 *) *)
(* Lemma Ctrigo_r_theta_existsC : forall (r θ : R) (k : Z), *)
(*     r > 0 -> (exists z : C, (z = Cscal r (cos θ +i sin  θ))). *)
(* Proof. *)
(*   intros. exists (Ctrigo r θ). auto. *)
(* Qed. *)

(** 复数的三角表示有无穷多种选择 *)
Lemma Ctrigo_many : forall (r θ : R) (k : Z),
    let θ' : R := (θ + 2 * (IZR k) * PI)%R in
    r ^^ θ = r s* (cos θ' +i sin θ').
Proof.
  intros. unfold Ctrigo, θ'. rewrite cos_period_Z, sin_period_Z.
  auto.
Qed.

(** Tips: 例 1.2。这类题目证明还是很繁琐，因实数构造问题
 这个例子也看出了大量的自动化的需求，比如带有 sqrt, cos, sin 等的运算，
 比如 Rsqr 2 与 sqr 2 的问题（它们混在一起）。
 能将这个证明简化到几步完成，而且还比较通用，也是个不错的课题。 *)

(* 由 0.875 = 7/8 <= x0 <= 7/4 = 1.75 和 x0 = k*PI + PI/2 判断出 k = 0 ? *)
Fact ex_1_2_ans1_aux1 (x : R) (k : Z) : (7/8 <= x <= 7/4)%R ->
                                        (x = IZR k * PI + PI / 2)%R -> k = Z0.
Proof.
  intros. subst.
  (* 7/8 <= k*PI + PI/2 <= 7/4 => k=0 *)
  (* 7/8 - PI/2 <= k*PI <= 7/4 - PI/2 *)
  (* (7/8 - PI/2)/PI <= k <= (7/4 - PI/2)/PI *)
  destruct H as [H1 H2].
  (* 证出两个不等式 0<=k, k<=0 *)
  assert (0 <= k)%Z.
  { apply le_IZR.
    Fail lra. (* 还不够智能，也许是因为有 PI *)
    (* 先消掉PI *)
    (* 如何证明  PI <= 3.15，可以找 PI 的估计值 *)
    assert (PI <= 3.15).
    
Admitted.

Example ex_1_2_ans1 : 1 +i 1 = Ctrigo (sqrt 2) (PI/4)%R.
Proof.
  (*   Opaque cos sin. compute. f_equal. *)
  (*   - destruct (Rcase_abs (R1+R1)). lra. *)
  (*     destruct (Rsqrt_exists). destruct a. destruct (PI_2_aux). destruct a. *)
  (*     (* - cos x = 0 => cos x = 0 *) *)
  (*     apply Ropp_eq_0_compat in H2.   (* ToDo: 这个引理本应该是iff的 *) *)
  (*     rewrite Ropp_involutive in H2. *)
  (*     (* cos x = 0 => x = k*PI + PI/2 = (2k*PI + PI)/2 *) *)
  (*     apply cos_eq_0_0 in H2. destruct H2 as [k]. *)
  (*     (* 推导出 k = 0 *) *)
  (*     assert (k = 0)%Z. apply (ex_1_2_ans1_aux1 x0 k); auto. subst. *)
  (*     ring_simplify (0 * PI + PI / 2)%R. *)
  (*     replace ((R1 + R1) * (PI / 2) * / ((R1 + R1) * (R1 + R1)))%R *)
  (*       with (PI/4)%R; try field. *)
  (*     rewrite cos_PI4.  *)
  (*     (* 0<=x -> 0<=y -> x^2 = y^2 -> x=y *) *)
  (*     apply Rsqr_inj; try lra. *)
  (*     + apply Rmult_le_pos; auto. apply Rlt_le. apply Rdiv_lt_0_compat; try lra. *)
  (*       apply Rlt_sqrt2_0. *)
  (*     + unfold Rsqr. ring_simplify. repeat rewrite <- Rsqr_pow2. rewrite <- H0. *)
  (*       rewrite Rsqr_div. rewrite Rsqr_sqrt; try lra. unfold Rsqr. field. *)
  (*       apply sqrt2_neq_0. *)
  (*   - destruct (Rcase_abs (R1+R1)). lra. *)
  (*     destruct (Rsqrt_exists). destruct a. destruct (PI_2_aux). destruct a. *)
  (*     (* - cos x = 0 => cos x = 0 *) *)
  (*     apply Ropp_eq_0_compat in H2.   (* ToDo: 这个引理本应该是iff的 *) *)
  (*     rewrite Ropp_involutive in H2. *)
  (*     (* cos x = 0 => x = k*PI + PI/2 = (2k*PI + PI)/2 *) *)
  (*     apply cos_eq_0_0 in H2. destruct H2 as [k]. *)
  (*     (* 推导出 k = 0 *) *)
  (*     assert (k = 0)%Z. apply (ex_1_2_ans1_aux1 x0 k); auto. subst. *)
  (*     ring_simplify (0 * PI + PI / 2)%R. *)
  (*     replace ((R1 + R1) * (PI / 2) * / ((R1 + R1) * (R1 + R1)))%R *)
  (*       with (PI/4)%R; try field. *)
  (*     rewrite sin_PI4.  *)
  (*     (* 0<=x -> 0<=y -> x^2 = y^2 -> x=y *) *)
  (*     apply Rsqr_inj; try lra. *)
  (*     + apply Rmult_le_pos; auto. apply Rlt_le. apply Rdiv_lt_0_compat; try lra. *)
  (*       apply Rlt_sqrt2_0. *)
  (*     + unfold Rsqr. ring_simplify. repeat rewrite <- Rsqr_pow2. rewrite <- H0. *)
  (*       rewrite Rsqr_div. rewrite Rsqr_sqrt; try lra. unfold Rsqr. field. *)
  (*       apply sqrt2_neq_0. *)
  (* Qed. *)
Abort.

Example ex_1_2_ans2 : 1 +i 1 = Ctrigo (sqrt 2) (PI/4)%R.
Abort.

(** 非零复数的共轭的三角表示 *)
Lemma Ctrigo_Cconj (z : C) : z <> C0 -> Cconj z = Ctrigo (| z |%C) (-/_ z)%R.
Proof.
  (* 展开z会很繁琐 *)
  intros; unfold Cconj, Ctrigo.
  rewrite cos_neg, sin_neg, ?cos_Carg_neq0, ?sin_Carg_neq0; auto.
  unfold Cscal. simpl. f_equal; field; apply Cnorm_neq0_if_neq0; auto.
Qed.

(** 1/z的三角表示 *)
Definition Ctrigo_Cinv (z : C) (k : Z) : C :=
  let r := | z | in
  let θ := Carg z in
  Ctrigo (/r)%R (-θ)%R.

(** /z 的三角表示公式正确 *)  
Lemma Ctrigo_Cinv_ok (z : C) (k : Z) : z <> C0 -> /z = Ctrigo_Cinv z k.
Proof.
  intros. (* rewrite Cinv_eq; auto. *)
  (* 1/z 改写为 {z}/{} *)
  intros; destruct z as (a,b). rewrite Cinv_rew; auto.
  remember ((a^2)+(b^2))%R as r.
  unfold Ctrigo_Cinv.
Admitted. 
(* 可能不需要展开z，或者要补充 Cnorm 关于 Cscal 等的性质，下次再证 *)


(* ======================================================================= *)
(** ** 1.2.4 用复数的三角表示作乘除法 *)

(** 复数乘法运算的三角表示版本 *)
Definition CmulTrigo (z1 z2 : C) : C :=
  Ctrigo (|z1|%C * |z2|%C)%R (/_  z1 + /_  z2)%R.

(** 复数除法运算的三角表示版本。注意，z2 <> C0 *)
Definition CdivTrigo (z1 z2 : C) : C :=
  Ctrigo (|z1|%C / |z2|%C)%R (/_  z1 - /_  z2)%R.

(** 复数乘法三角表示版本与常规乘法定义等价 *)
Lemma CmulTrigo_eq_Cmul (z1 z2 : C) : 
  z1 * z2 = CmulTrigo z1 z2.
Proof.
  unfold CmulTrigo, Ctrigo.
  rewrite cos_plus, sin_plus. unfold Cscal.
  (* 是否为复数零来分类讨论 *)
  destruct (Aeqdec z1 C0), (Aeqdec z2 C0); subst; Ceq;
    repeat rewrite Cnorm_C0_eq0; autorewrite with R; auto.
  (*   - autorewrite with R; auto. *)

  (*     Search (/_  C0). Ceq.  *)
  (*     repeat rewrite ?cos_Carg_neq0, ?sin_Carg_neq0; simpl; try easy. *)

  (*     repeat rewrite ?Cnorm_C0_eq0,?cos_Carg_neq0, ?sin_Carg_neq0; simpl; try easy. *)

  (*   2:{ *)
  (*     rewrite ?Cnorm_C0_eq0. simpl. cbv. *)
  (*   simpl. unfold Cmul. *)

  (*   ; ring_simplify. ; unfold R_R_to_C; f_equal; try ring. *)
  (*   unfold R_R_to_C. f_equal; field; split; apply Cnorm_ne0_iff_neq0; auto. *)
  (* Qed. *)
Abort.

(** 除数非零时，复数除法三角表示版本与常规除法定义等价 *)
Lemma CdivTrigo_eq_Cdiv (z1 z2 : C) :
  z2 <> C0 -> z1 / z2 = CdivTrigo z1 z2.
Proof.
  intros. unfold CdivTrigo, Ctrigo.
  rewrite cos_minus, sin_minus. unfold Cscal. simpl.
  (* 是否为复数零来分类讨论 *)
  destruct (Aeqdec z1 C0), (Aeqdec z2 C0);
    subst; rewrite ?Cnorm_C0_eq0; unfold Cdiv.
  - destruct H. auto.
    (*   - rewrite Cmul_0_l. ring_simplify. unfold Rdiv, R_R_to_C.  *)
    (*     f_equal; field; apply Cnorm_ne0_iff_neq0; auto. *)
    (*   - apply C0_neq0_False in H; easy. *)
    (*   - repeat rewrite cos_Carg_neq0, sin_Carg_neq0; auto. *)
    (*     destruct z1 as [x1 y1], z2 as [x2 y2]. unfold Cmul. simpl. *)
    (*     unfold Cnorm, Cnorm2. simpl. *)
    (*     remember (sqrt (x1 * x1 + y1 * y1)) as r1. *)
    (*     remember (sqrt (x2 * x2 + y2 * y2)) as r2. *)
    (*     assert ((x2 ^ 2 + y2 ^ 2)%R = (r2 ^ 2)%R). *)
    (*     { rewrite Heqr2. rewrite pow2_sqrt. repeat rewrite <- Rsqr_pow2; auto. *)
    (*       apply Raux_Rplus_Rmult_ge0. } *)
    (*     assert (r1 <> 0)%R. *)
    (*     { rewrite Heqr1. apply Cnorm_no_R0 in n. auto. } *)
    (*     assert (r2 <> 0)%R. *)
    (*     { rewrite Heqr2. apply Cnorm_no_R0 in H. auto. } *)
    (*     f_equal. *)
    (*     + replace (r1 / r2 * (x1 / r1 * (x2 / r2) + y1 / r1 * (y2 / r2)))%R *)
    (*       with ((x1*x2+y1*y2)/(r2^2))%R; try field; auto. *)
    (*       replace (r2^2)%R with (x2^2 + y2^2)%R; try field. *)
    (*       repeat rewrite <- Rsqr_pow2; auto. *)
    (*       apply Raux_neq0_neq0_imply_RplusRsqr_ge0; auto. *)
    (*     + replace (r1 / r2 * (y1 / r1 * (x2 / r2) - x1 / r1 * (y2 / r2)))%R *)
    (*       with ((x2*y1-x1*y2)/(r2^2))%R; try field; auto. *)
    (*       replace (r2^2)%R with (x2^2 + y2^2)%R; try field. *)
    (*       repeat rewrite <- Rsqr_pow2; auto. *)
    (*       apply Raux_neq0_neq0_imply_RplusRsqr_ge0; auto. *)
    (* Qed. *)
Abort.


(* ======================================================================= *)
(** ** 1.2.5 复数的乘方与开方 *)

(** 复数乘方运算的三角表示版本 *)
Definition CpowTrigo (z : C) (n : nat) : C :=
  Ctrigo (| z |%C ^ n)%R ((INR n) * (/_  z))%R.

(** 复数开方运算的三角表示版本。注意，z2 <> C0，共有 n 个根（n个不同的主辐角）*)
Definition CnrootTrigo (z : C) (n : nat) (k : nat) : C :=
  Ctrigo ( / (| z |%C ^ n))%R ((/_ z + 2 * (INR k) * PI) / (INR n))%R.

(** 复数乘方三角版本的性质 *)

(** 幂为 0 *)
Lemma CpowTrigo_0 (z : C) : CpowTrigo z 0 = C1.
Proof.
  unfold CpowTrigo. simpl. unfold Ctrigo.
  rewrite Rmult_0_l. rewrite cos_0, sin_0. compute. f_equal; ring.
Qed.

(** 幂为 S n *)
Lemma CpowTrigo_S (z : C) (n : nat) : CpowTrigo z (S n) = z * (CpowTrigo z n).
Proof.
  unfold CpowTrigo. 
Admitted.

(** 复数乘方三角表示版本与常规乘方定义等价 *)
Lemma CpowTrigo_eq_Cmul (z : C) (n : nat) : 
  Cpow z n  = CpowTrigo z n.
Proof.
  generalize dependent z. induction n; intros; simpl.
  - rewrite CpowTrigo_0; auto.
  - rewrite CpowTrigo_S. f_equal. auto.
Qed.

(** 复数开方运算的三角表示版本 与 复数乘方三角表示版本的互逆性 *)


(* begin hide *)
(** Simple tactics using the projections *)

(** 分解分量；化简；分割 *)
Ltac CusingR_simpl :=
  rewrite <- Ceq_iff ; simpl ; split.

(** 若前提中有复数则先分解 *)
Ltac CusingR_rec := match goal with
                    | id:C |- _ => destruct id ; try CusingR_rec
                    end.

(** 若有全称量词则先实例化，并且最后用 real 库自动处理 *)
Ltac CusingR := 
  intros; try CusingR_rec ; 
  apply (proj1 (Ceq_iff _ _)) ; split ; simpl ; auto with real.

(** 最后还要用 field 策略 处理 *)
Ltac CusingR_f := CusingR ; field.

(* begin hide *)
(* Annex tactic that should not be used *)
Ltac CusingRR :=  try rewrite <- Ceq_iff in * .

Ltac CusingR_rec1 := 
  (* 展开 not  *)
  unfold not in *;
  match goal with
  (* destruct complex 分解复数 *)
  | id:C |- _ => destruct id ; CusingRR ; try CusingR_rec1
  (* logical destruct in goal 逻辑分解 *)
  | id: _|- _ -> _ => intros ; CusingRR ; try CusingR_rec1
  | id: _|- _ /\ _ => split ; CusingRR ; try CusingR_rec1
  | id: _ /\ _ |- _ => destruct id ; CusingRR ; try CusingR_rec1
  | id: _ \/ _ |- _ => destruct id ; CusingRR ; try CusingR_rec1
  (* false *)
  | id: _ |- False => (apply id ; CusingR1) 
  (* si le apply id echoue on continue le matching sur les clauses
     如果apply id失败，则继续匹配子句 *) 
                   
  (* le ou a la fin sinon c'est galere
     或最后，否则很麻烦 *)
  | id: _|- _ \/ _ => try ((left ; CusingR1 ; fail) || (right ; CusingR1 ; fail)) ;
                    CusingRR ; simpl in *
  | _ => simpl in *
  end
    with CusingR1 := 
    intros ; CusingRR ; CusingR_rec1 ; subst ; intuition ;
    try ((lra || (field ; CusingR1))).

(* This tactic may help (not sure) *)
Ltac RusingC a b := 
  let z := fresh "z" in
  let H := fresh "H" in 
  let H1 := fresh "H1" in
  let H2 := fresh "H2" in 
  destruct (Cexist_rep_complex a b) as (z, H) ; destruct H as (H1, H2) ;
  try
    (rewrite <- H1 in * ; rewrite <- H2 in * ); 
  clear H1 ; clear H2 ; clear a ; clear b ; intuition.

(* end hide *)


(* ######################################################################### *)
(** * Algebraic Structures *)

(** equality is equivalence relation: Equivalence eq *)
Hint Resolve eq_equivalence : C.

(** operations are well-defined. Eg: Proper (eq ==> eq ==> eq) Cadd *)

Lemma Cadd_wd : Proper (eq ==> eq ==> eq) Cadd.
Proof. repeat (hnf; intros); subst; auto. Qed.

Lemma Copp_wd : Proper (eq ==> eq) Copp.
Proof. repeat (hnf; intros); subst; auto. Qed.

Lemma Csub_wd : Proper (eq ==> eq ==> eq) Csub.
Proof. repeat (hnf; intros); subst; auto. Qed.

Lemma Cmul_wd : Proper (eq ==> eq ==> eq) Cmul.
Proof. repeat (hnf; intros); subst; auto. Qed.

Lemma Cinv_wd : Proper (eq ==> eq) Cinv.
Proof. repeat (hnf; intros); subst; auto. Qed.

Lemma Cdiv_wd : Proper (eq ==> eq ==> eq) Cdiv.
Proof. repeat (hnf; intros); subst; auto. Qed.

Hint Resolve
  Cadd_wd Copp_wd Csub_wd
  Cmul_wd Cinv_wd Cdiv_wd
  : C.

(** Associative *)

Instance Cadd_Assoc : Associative Cadd.
Proof. constructor; intros; field. Qed.

Instance Cmul_Assoc : Associative Cmul.
Proof. constructor; intros; field. Qed.

Hint Resolve
  Cadd_Assoc
  Cmul_Assoc
  : C.

(** Commutative *)

Instance Cadd_Comm : Commutative Cadd.
Proof. constructor; intros; field. Qed.

Instance Cmul_Comm : Commutative Cmul.
Proof. constructor; intros; field. Qed.

Hint Resolve Cadd_Comm Cmul_Comm : C.

(** Identity Left/Right *)
Instance Cadd_IdL : IdentityLeft Cadd C0.
Proof. constructor. intros. field. Qed.

Instance Cadd_IdR : IdentityRight Cadd C0.
Proof. constructor; intros; field. Qed.

Instance Cmul_IdL : IdentityLeft Cmul C1.
Proof. constructor; intros; field. Qed.

Instance Cmul_IdR : IdentityRight Cmul C1.
Proof. constructor; intros; field. Qed.

Hint Resolve
  Cadd_IdL
  Cadd_IdR
  Cmul_IdL
  Cmul_IdR
  : C.

(** Inverse Left/Right *)

Instance Cadd_InvL : InverseLeft Cadd C0 Copp.
Proof. constructor; intros; ring. Qed.

Instance Cadd_InvC : InverseRight Cadd C0 Copp.
Proof. constructor; intros; ring. Qed.

Hint Resolve Cadd_InvL Cadd_InvC : C.

(** Distributive *)

Instance Cmul_add_DistrL : DistrLeft Cadd Cmul.
Proof. constructor; intros; field. Qed.

Instance Cmul_add_DistrR : DistrRight Cadd Cmul.
Proof. constructor; intros; field. Qed.

Hint Resolve
  Cmul_add_DistrL
  Cmul_add_DistrR
  : C.

(** Semigroup *)

Instance Cadd_SGroup : SGroup Cadd.
Proof. constructor; auto with C. Qed.

Instance Cmul_SGroup : SGroup Cmul.
Proof. constructor; auto with C. Qed.

Hint Resolve
  Cadd_SGroup
  Cmul_SGroup
  : C.

(** Abelian semigroup *)

Instance Cadd_ASGroup : ASGroup Cadd.
Proof. constructor; auto with C. Qed.

Instance Cmul_ASGroup : ASGroup Cmul.
Proof. constructor; auto with C. Qed.

Hint Resolve
  Cadd_ASGroup
  Cmul_ASGroup
  : C.

(** Monoid *)
  
Instance Cadd_Monoid : Monoid Cadd C0.
Proof. constructor; auto with C. Qed.

Instance Cmul_Monoid : Monoid Cmul C1.
Proof. constructor; auto with C. Qed.

Hint Resolve
  Cadd_Monoid
  Cmul_Monoid
  : C.

(** Abelian monoid *)
  
Instance Cadd_AMonoid : AMonoid Cadd C0.
Proof. constructor; auto with C. Qed.
  
Instance Cmul_AMonoid : AMonoid Cmul C1.
Proof. constructor; auto with C. Qed.

Hint Resolve Cadd_AMonoid Cmul_AMonoid : C.

(** Group *)

Instance Cadd_Group : Group Cadd C0 Copp.
Proof. constructor; auto with C. Qed.
Hint Resolve Cadd_Group : C.

(** AGroup *)

Instance Cadd_AGroup : AGroup Cadd C0 Copp.
Proof. constructor; auto with C. Qed.
Hint Resolve Cadd_AGroup : C.

(** SRing *)

Instance C_SRing : SRing Cadd C0 Cmul C1.
Proof. constructor; auto with C. all: Ceq. Qed.
Hint Resolve C_SRing : C.

(** Ring *)

Instance C_Ring : Ring Cadd C0 Copp Cmul C1.
Proof. constructor; auto with C. Qed.
Hint Resolve C_Ring : C.

(** ARing *)

Instance C_ARing : ARing Cadd C0 Copp Cmul C1.
Proof. constructor; auto with C. Qed.
Hint Resolve C_ARing : C.

(** Field *)

Instance C_Field : Field Cadd C0 Copp Cmul C1 Cinv.
Proof. constructor; auto with C. Qed.


(* ######################################################################### *)
(** * Instances for ElementType *)
   
Module ElementTypeC <: ElementType.
  Definition tA : Type := C.
  Definition Azero : tA := C0.
  Hint Unfold tA Azero : tA.

  Lemma AeqDec : Dec (@eq tA).
  Proof. apply Ceq_Dec. Defined.
End ElementTypeC.

Module MonoidElementTypeC <: MonoidElementType.
  Include ElementTypeC.

  Definition Aadd := Cadd.
  
  (** Note that, this explicit annotation is must,  *)
(*       otherwise, the ring has no effect. (because C and T are different) *)
  (* Definition Aadd : tA -> tA -> tA := fun a b => Cadd a b. *)
  Hint Unfold Aadd : tA.
  
  Infix "+" := Aadd : A_scope.

  Instance Aadd_AMonoid : AMonoid Aadd Azero.
  Proof. intros. repeat constructor; intros; autounfold with tA; ring. Qed.
End MonoidElementTypeC.

Module RingElementTypeC <: RingElementType.
  Include MonoidElementTypeC.

  Definition Aone : tA := C1.
  Definition Aopp := Copp.
  Definition Amul := Cmul.
  Hint Unfold Aone Aadd Aopp Amul : tA.
  
  Notation Asub := (fun x y => Aadd x (Aopp y)).
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := Asub : A_scope.

  Instance SRing : SRing Aadd Azero Amul Aone.
  Proof. repeat constructor; autounfold with tA; intros; ring. Qed.

  Instance ARing : ARing Aadd Azero Aopp Amul Aone.
  Proof. repeat constructor; autounfold with tA; intros; ring. Qed.
  
  Add Ring Ring_inst : (make_ring_theory ARing).
End RingElementTypeC.

Module FieldElementTypeC <: FieldElementType.
  Include RingElementTypeC.
  
  Definition Ainv := Cinv.
  Hint Unfold Ainv : tA.
  
  Notation Adiv := (fun x y => Amul x (Ainv y)).

  Lemma Aone_neq_Azero : Aone <> Azero.
  Proof. cbv in *. auto with C. Qed.
  
  Instance Field : Field Aadd Azero Aopp Amul Aone Ainv.
  Proof.
    constructor. apply ARing. intros.
    autounfold with tA. field. auto.
    apply Aone_neq_Azero.
  Qed.

  Add Field Field_inst : (make_field_theory Field).
End FieldElementTypeC.
