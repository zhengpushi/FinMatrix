(*
  Copyright 2024 ZhengPu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix theory on R.
  author    : ZhengPu Shi
  date      : 2023.12

  reference :
  1. 《高等数学学习手册》徐小湛，p173
  2. 《高等数学》 第七版，同济大学数学系，第八章，向量代数与空间解析几何
  3. Vector Calculus - Michael Corral
  4. https://github.com/coq/coq/blob/master/test-suite/success/Nsatz.v
     Note that, there are concepts related to geometry including point, parallel, 
     colinear.
  5. https://wuli.wiki/online/Cross.html
  6. https://en.wikipedia.org/wiki/Cross_product

  remark    :
  1. 在三维向量空间中：空间点M <-> 原点O指向M的向量 r⃗=OM=xi+yj+zk <-> 有序数(x,y,z)
  2. {R^n, standard-inner-product} is called Euclidean space
     |v| = √<v, v>
 *)

Require Export Hierarchy RExt RFunExt Ratan2.
Require Export MatrixModule.
Require Import ExtrOcamlBasic ExtrOcamlNatInt MyExtrOCamlR.

(* ######################################################################### *)
(** * Matrix theory come from common implementations *)

Include (NormedOrderedFieldMatrixTheory NormedOrderedFieldElementTypeR).

(* A TEMPORARY Fix: Let "Hierarchy.le_xx" has more priority than "Nat.le_xx" *)
Import Hierarchy RExt.

Open Scope R_scope.
Open Scope vec_scope.
Open Scope mat_scope.


(* ############################################################################ *)
(** * OCaml Extraction of matrix inversion *)

(* Recursive Extraction *)
(*   mmul *)
(*   minvtblebGE minvoGE minvGE minvListGE *)
(*   minvtblebAM minvoAM minvAM minvListAM. *)

(* Extraction "ocaml_test/matrix.ml" *)
(*   mmul *)
(*   minvtblebGE minvoGE minvGE minvListGE *)
(*   minvtblebAM minvoAM minvAM minvListAM. *)


(* ######################################################################### *)
(** * Matrix theory applied to this type *)

Open Scope vec_scope.

(* ======================================================================= *)
(** ** Extension for R *)
Lemma Rsqrt_1_minus_x_eq_y : forall x y : R,
    (x² + y²)%R <> 0 -> sqrt (1 - (x / sqrt (x² + y²))²) = |y| / sqrt (x² + y²).
Proof.
  intros.
  replace (1 - (x / sqrt (x² + y²))²)%R with (y² / (x² + y²))%R.
  - rewrite sqrt_div_alt; ra. f_equal. apply sqrt_square_abs.
  - rewrite Rsqr_div'. autorewrite with sqrt; ra. field. ra.
Qed.

Lemma Rsqrt_1_minus_y_eq_x : forall x y : R,
    (x² + y²)%R <> 0 -> sqrt (1 - (y / sqrt (x² + y²))²) = |x| / sqrt (x² + y²).
Proof.
  intros.
  rewrite Rplus_comm at 1. rewrite Rsqrt_1_minus_x_eq_y; ra.
  f_equal. rewrite Rplus_comm. auto.
Qed.

(* ======================================================================= *)
(** ** 去掉 a2r 以及 Aabs 的一些引理 *)

(** Aabs a = Rabs a *)
Lemma Aabs_eq_Rabs : forall a : A, | a |%A = | a |%R.
Proof.
  intros. unfold Aabs. destruct (Ale_dec Azero a); autounfold with A in *; ra.
  rewrite Rabs_left; ra.
Qed.

(** <a, a> = ||a||² *)
Lemma vdot_sameR : forall {n} (a : vec n), <a, a> = (||a||)².
Proof. intros. rewrite <- vdot_same. auto. Qed.


(* ======================================================================= *)
(** ** Vector normalization (only valid in R type) *)

(** Normalization of a non-zero vector a.
      That is, make a unit vector that in the same directin as a. *)
Definition vnorm {n} (a : vec n) : vec n := (1 / ||a||) \.* a.

(** The component of a normalized vector is equivalent to its original component 
      divide the vector's length *)
Lemma vnth_vnorm : forall {n} (a : vec n) i, a <> vzero -> (vnorm a).[i] = a.[i] / ||a||.
Proof.
  intros. unfold vnorm. rewrite vnth_vcmul; auto.
  autounfold with A. field. apply vlen_neq0_iff_neq0; auto.
Qed.

(** Unit vector is fixpoint of vnorm operation *)
Lemma vnorm_vunit_eq : forall {n} (a : vec n), vunit a -> vnorm a = a.
Proof.
  intros. unfold vnorm. rewrite (vunit_spec a) in H. rewrite H.
  autorewrite with R. apply vcmul_1_l.
Qed.

(** Normalized vector is non-zero  *)
Lemma vnorm_vnonzero : forall {n} (a : vec n), a <> vzero -> vnorm a <> vzero.
Proof.
  intros. unfold vnorm. intro.
  apply vcmul_eq0_imply_x0_or_v0 in H0. destruct H0; auto.
  apply vlen_neq0_iff_neq0 in H. unfold Rdiv in H0.
  rewrite Rmult_1_l in H0. apply Rinv_neq_0_compat in H. easy.
Qed.

(** The length of a normalized vector is one *)
Lemma vnorm_len1 : forall {n} (a : vec n), a <> vzero -> ||vnorm a|| = 1.
Proof.
  intros. unfold vnorm. rewrite vlen_vcmul. unfold a2r, id. rewrite Aabs_eq_Rabs.
  pose proof (vlen_gt0 a H). rewrite Rabs_right; ra. field; ra.
Qed.

(** Normalized vector are unit vector *)
Lemma vnorm_is_unit : forall {n} (a : vec n), a <> vzero -> vunit (vnorm a).
Proof. intros. apply vunit_spec. apply vnorm_len1; auto. Qed.

(** Normalized vector is parallel to original vector *)
Lemma vnorm_vpara : forall {n} (a : vec n), a <> vzero -> (vnorm a) //+ a.
Proof.
  intros. repeat split; auto.
  - apply vnorm_vnonzero; auto.
  - exists (||a||). split.
    + apply vlen_gt0; auto.
    + unfold vnorm. rewrite vcmul_assoc. apply vcmul_same_if_x1_or_v0.
      left. autounfold with A. field. apply vlen_neq0_iff_neq0; auto.
Qed.

Lemma vnorm_spec : forall {n} (a : vec n),
    a <> vzero -> (||vnorm a|| = 1 /\ (vnorm a) //+ a).
Proof. intros. split. apply vnorm_len1; auto. apply vnorm_vpara; auto. Qed.

(** Normalization is idempotent *)
Lemma vnorm_idem : forall {n} (a : vec n), a <> vzero -> vnorm (vnorm a) = vnorm a.
Proof. intros. apply vnorm_vunit_eq. apply vnorm_is_unit; auto. Qed.

(** x <> 0 -> vnorm (x \.* a) = (sign x) \.* (vnorm a) *)
Lemma vnorm_vcmul : forall {n} x (a : vec n),
    x <> 0 -> a <> vzero -> vnorm (x \.* a) = sign x \.* (vnorm a).
Proof.
  intros. unfold vnorm. rewrite vlen_vcmul. rewrite !vcmul_assoc.
  f_equal. unfold sign. autounfold with A. apply vlen_neq0_iff_neq0 in H0.
  unfold a2r,id. rewrite Aabs_eq_Rabs.
  bdestruct (0 <? x).
  - rewrite Rabs_right; ra. field. split; auto.
  - bdestruct (x =? 0). easy. rewrite Rabs_left; ra. field. auto.
Qed.

(** x > 0 -> vnorm (x \.* a) = vnorm a *)
Lemma vnorm_vcmul_k_gt0 : forall {n} x (a : vec n),
    x > 0 -> a <> vzero -> vnorm (x \.* a) = vnorm a.
Proof.
  intros. rewrite vnorm_vcmul; auto; ra. rewrite sign_gt0; auto. apply vcmul_1_l.
Qed.

(** x < 0 -> vnorm (x \.* a) = vnorm a *)
Lemma vnorm_vcmul_k_lt0 : forall {n} x (a : vec n),
    x < 0 -> a <> vzero -> vnorm (x \.* a) = - vnorm a.
Proof.
  intros. rewrite vnorm_vcmul; auto; ra. rewrite sign_lt0; auto.
  rewrite (vcmul_opp 1). f_equal. apply vcmul_1_l.
Qed.

(** -1 <= (vnorm a)[i] <= 1 *)
Lemma vnth_vnorm_bound : forall {n} (a : vec n) (i : fin n),
    a <> vzero -> -1 <= vnorm a i <= 1.
Proof.
  intros. rewrite vnth_vnorm; auto. pose proof (vnth_le_vlen a i H).
  apply Rabs_le_rev. rewrite Aabs_eq_Rabs in *. unfold a2r,id in *.
  apply Rdiv_abs_le_1. apply vlen_neq0_iff_neq0; auto.
  apply le_trans with (||a||); auto.
  rewrite Rabs_right. apply le_refl.
  apply Rle_ge. apply vlen_ge0.
Qed.

(** -1 <= a.i / ||a|| <= 1 *)
Lemma vnth_div_vlen_bound : forall {n} (a : vec n) i,
    a <> vzero -> -1 <= a i / (|| a ||) <= 1.
Proof.
  intros. pose proof (vnth_vnorm_bound a i H). unfold vnorm in H0.
  rewrite vnth_vcmul in H0. autounfold with A in *. ra.
Qed.

(** <vnorm a, vnorm b> = <a, b> / (||a|| * ||b||) *)
Lemma vdot_vnorm : forall {n} (a b : vec n),
    a <> vzero -> b <> vzero ->
    <vnorm a, vnorm b> = <a, b> / (||a|| * ||b||).
Proof.
  intros. unfold vnorm. rewrite vdot_vcmul_l, vdot_vcmul_r.
  autounfold with A. field. split; apply vlen_neq0_iff_neq0; auto.
Qed.

(** <vnorm a, vnorm b>² = <a, b>² / (<a, a> * <b, b>) *)
Lemma sqr_vdot_vnorm : forall {n} (a b : vec n),
    a <> vzero -> b <> vzero ->
    <vnorm a, vnorm b>² = <a, b>² / (<a, a> * <b, b>).
Proof.
  intros. rewrite vdot_vnorm; auto. rewrite Rsqr_div'. f_equal.
  rewrite Rsqr_mult. rewrite !vdot_sameR. auto.
Qed.

(** sqrt (1 - <a, b>²) = sqrt (<a, a> * <b, b> - <a, b>²) / (||a|| * ||b||) *)
Lemma sqrt_1_minus_sqr_vdot : forall {n} (a b : vec n),
    a <> vzero -> b <> vzero ->
    sqrt (1 - <vnorm a, vnorm b>²) =
      sqrt (((<a, a> * <b, b>) - <a, b>²) / (||a|| * ||b||)²).
Proof.
  intros. unfold vnorm. rewrite vdot_vcmul_l, vdot_vcmul_r. autounfold with A.
  replace (1 - (1 / (||a||) * (1 / (||b||) * (<a, b>)))²)%R
    with (((<a, a> * <b, b>) - <a, b>²) / (||a|| * ||b||)²); auto.
  rewrite !Rsqr_mult, !Rsqr_div'. rewrite <- !vdot_sameR. field_simplify_eq.
  - autorewrite with R. auto.
  - split; apply vdot_same_neq0_if_vnonzero; auto.
Qed.

(** vnorm a _|_ b <-> a _|_ b *)
Lemma vorth_vnorm_l : forall {n} (a b : vec n), a <> vzero -> vnorm a _|_ b <-> a _|_ b.
Proof.
  intros. unfold vorth, vnorm in *. rewrite vdot_vcmul_l. autounfold with A.
  assert (1 * / (||a||) <> 0)%R; ra.
  apply Rmult_integral_contrapositive_currified; ra.
  apply Rinv_neq_0_compat; auto. apply vlen_neq0_iff_neq0; auto.
Qed.

(** a _|_ vnorm b <-> a _|_ b *)
Lemma vorth_vnorm_r : forall {n} (a b : vec n), b <> vzero -> a _|_ vnorm b -> a _|_ b.
Proof.
  intros. apply vorth_comm. apply vorth_comm in H0. apply vorth_vnorm_l; auto.
Qed.

(* ======================================================================= *)
(** ** Angle between two vectors *)

(** The angle from vector u to vector v, Here, θ ∈ [0,π] *)
Definition vangle {n} (a b : vec n) : R := acos (<vnorm a, vnorm b>).
Infix "/_" := vangle : vec_scope.

(** The angle of between any vector and itself is 0 *)
Lemma vangle_self : forall {n} (a : vec n), a <> vzero -> a /_ a = 0.
Proof.
  intros. unfold vangle. rewrite vdot_sameR.
  rewrite vnorm_len1; auto. autorewrite with R. apply acos_1.
Qed.

(** Angle is commutative *)
Lemma vangle_comm : forall {n} (a b : vec n), a /_ b = b /_ a.
Proof. intros. unfold vangle. rewrite vdot_comm. auto. Qed.

(* Tips: Here, we can finish a demo proof with a special value π/4,
   but actual cases maybe have any value, it is hard to finished in Coq.
   Because the construction of {sqrt, acos, PI, etc} is complex. *)
(** The angle between (1,0,0) and (1,1,0) is 45 degree, i.e., π/4 *)
Fact vangle_pi4 : (@l2v 3 [1;0;0]) /_ (l2v [1;1;0]) = PI/4.
Proof.
  rewrite <- acos_inv_sqrt2. unfold vangle. f_equal.
  compute. autorewrite with R. auto.
Qed.

(** 单位向量的点积介于[-1,1] *)
Lemma vdot_unit_bound : forall {n} (a b : vec n),
    vunit a -> vunit b -> -1 <= <a, b> <= 1.
Proof.
  intros.
  pose proof (vdot_abs_le a b).
  pose proof (vdot_ge_mul_vlen_neg a b).
  unfold a2r,id in *. apply vunit_spec in H, H0. rewrite H,H0 in H1,H2.
  unfold Rabs in H1. destruct Rcase_abs; ra.
Qed.

(** 单位化后的非零向量的点积介于 [-1,1] *)
Lemma vdot_vnorm_bound : forall {n} (a b : vec n),
    a <> vzero -> b <> vzero -> -1 <= <vnorm a, vnorm b> <= 1.
Proof. intros. apply vdot_unit_bound; apply vnorm_is_unit; auto. Qed.

(** <a, b> = ||a|| * ||b|| * cos (a /_ b) *)
Lemma vdot_eq_cos_angle : forall {n} (a b : vec n),
    <a, b> = (||a|| * ||b|| * cos (a /_ b))%R.
Proof.
  intros. destruct (Aeqdec a vzero).
  - subst. rewrite vdot_0_l, vlen_vzero. rewrite Rmult_0_l. auto.
  - destruct (Aeqdec b vzero).
    + subst. rewrite vdot_0_r, vlen_vzero. rewrite Rmult_0_l,Rmult_0_r. auto.
    + unfold vangle. rewrite cos_acos.
      * unfold vnorm. rewrite <- vdot_vcmul_r. rewrite <- vdot_vcmul_l.
        rewrite !vcmul_assoc. autounfold with A.
        replace ((||a||) * (1 / ||a||))%R with 1;
          [|field; apply vlen_neq0_iff_neq0; auto].
        replace ((||b||) * (1 / ||b||))%R with 1;
          [|field; apply vlen_neq0_iff_neq0; auto].
        rewrite !vcmul_1_l. auto.
      * apply vdot_vnorm_bound; auto.
Qed.

(** The cosine law *)
Theorem CosineLaw : forall {n} (a b : vec n),
    ||(a - b)||² = (||a||² + ||b||² - 2 * ||a|| * ||b|| * cos (a /_ b))%R.
Proof.
  intros. rewrite vlen_sqr_vsub. f_equal. f_equal.
  rewrite vdot_eq_cos_angle. auto.
Qed.

(** A variant form of cosine law *)
Theorem CosineLaw_var : forall {n} (a b : vec n),
    ||(a + b)||² = (||a||² + ||b||² + 2 * ||a|| * ||b|| * cos (a /_ b))%R.
Proof.
  intros. rewrite vlen_sqr_vadd. f_equal. f_equal.
  rewrite vdot_eq_cos_angle. auto.
Qed.

(** The relation between dot product and the cosine of angle *)
Lemma vdot_eq_cos_angle_by_CosineLaw : forall {n} (a b : vec n),
    <a, b> = (||a|| * ||b|| * cos (a /_ b))%R.
Proof.
  intros. pose proof (vlen_sqr_vsub a b). pose proof (CosineLaw a b).
  unfold a2r,id in *. ra.
Qed.

(** 0 <= a /_ b <= PI *)
Lemma vangle_bound : forall {n} (a b : vec n),
    a <> vzero -> b <> vzero -> 0 <= a /_ b <= PI.
Proof. intros. unfold vangle. apply acos_bound. Qed.

(** a /_ b = 0 <-> (<a, b> = ||a|| * ||b||) *)
Lemma vangle_0_iff : forall {n} (a b : vec n),
    a <> vzero -> b <> vzero -> (a /_ b = 0 <-> <a, b> = (||a|| * ||b||)%R).
Proof.
  intros. rewrite (vdot_eq_cos_angle a b).
  rewrite <- associative. rewrite <- (Rmult_1_r (||a|| * ||b||)) at 2.
  split; intros.
  - apply Rmult_eq_compat_l. rewrite H1. ra.
  - apply Rmult_eq_reg_l in H1.
    * apply (cos_1_period _ 0) in H1. ra.
    * apply vlen_neq0_iff_neq0 in H,H0. ra.
Qed.

(** a /_ b = π <-> (<a, b> = -||a|| * ||b||) *)
Lemma vangle_PI_iff : forall {n} (a b : vec n),
    a <> vzero -> b <> vzero -> (a /_ b = PI <-> <a, b> = (-||a|| * ||b||)%R).
Proof.
  intros. rewrite (vdot_eq_cos_angle a b). rewrite <- !associative.
  replace (- (||a|| * ||b||))%R with ((||a|| * ||b||) * (-1))%R; ra.
  split; intros.
  - apply Rmult_eq_compat_l. rewrite H1. ra.
  - apply Rmult_eq_reg_l in H1.
    * apply (cos_neg1_period _ 0) in H1. ra.
    * apply vlen_neq0_iff_neq0 in H,H0. ra.
Qed.

(** a /_ b = 0 -> <a, b>² = <a, a> * <b, b> *)
Lemma vangle_0_imply_vdot_sqr_eq : forall {n} (a b : vec n),
    a <> vzero -> b <> vzero ->
    a /_ b = 0 -> <a, b>² = (<a, a> * <b, b>)%R.
Proof. intros. apply vangle_0_iff in H1; auto. rewrite H1, !vdot_sameR. ra. Qed.

(** a /_ b = π -> <a, b>² = <a, a> * <b, b> *)
Lemma vangle_PI_imply_vdot_sqr_eq : forall {n} (a b : vec n),
    a <> vzero -> b <> vzero ->
    a /_ b = PI -> <a, b>² = (<a, a> * <b, b>)%R.
Proof. intros. apply vangle_PI_iff in H1; auto. rewrite H1, !vdot_sameR. ra. Qed.

(** (<a, b>² = <a, a> * <b, b>) -> (a /_ b = 0) \/ (a /_ b = π) *)
Lemma vdot_sqr_eq_imply_vangle_0_or_PI : forall {n} (a b : vec n),
    a <> vzero -> b <> vzero ->
    <a, b>² = (<a, a> * <b, b>)%R -> (a /_ b = 0) \/ (a /_ b = PI).
Proof.
  intros. rewrite !vdot_sameR in H1. rewrite <- Rsqr_mult in H1.
  apply Rsqr_eq in H1. destruct H1.
  - apply vangle_0_iff in H1; auto.
  - apply vangle_PI_iff in H1; auto.
Qed.

(** (a /_ b = 0) \/ (a /_ b = π) -> <a, b>² = <a, a> * <b, b> *)
Lemma vangle_0_or_PI_imply_vdot_sqr_eq : forall {n} (a b : vec n),
    a <> vzero -> b <> vzero ->
    (a /_ b = 0) \/ (a /_ b = PI) -> <a, b>² = (<a, a> * <b, b>)%R. 
Proof.
  intros. destruct H1.
  - apply vangle_0_imply_vdot_sqr_eq; auto.
  - apply vangle_PI_imply_vdot_sqr_eq; auto.
Qed.

(** a /_ b = π/2 <-> (<a, b> = 0) *)
Lemma vangle_PI2_iff : forall {n} (a b : vec n),
    a <> vzero -> b <> vzero -> (a /_ b = PI/2 <-> (<a, b> = 0)).
Proof.
  intros. rewrite (vdot_eq_cos_angle a b). split; intros.
  - rewrite H1. rewrite cos_PI2. ra.
  - assert (cos (a /_ b) = 0).
    + apply vlen_neq0_iff_neq0 in H,H0. apply Rmult_integral in H1; ra.
    + apply (cos_0_period _ 0) in H2. ra.
Qed.

(** 0 <= sin (a /_ b) *)
Lemma sin_vangle_ge0 : forall {n} (a b : vec n),
    a <> vzero -> b <> vzero -> 0 <= sin (a /_ b).
Proof. intros. apply sin_ge_0; apply vangle_bound; auto. Qed.

(** θ ≠ 0 -> θ ≠ π -> 0 < sin (a /_ b) *)
Lemma sin_vangle_gt0 : forall {n} (a b : vec n),
    a <> vzero -> b <> vzero -> a /_ b <> 0 -> a /_ b <> PI -> 0 < sin (a /_ b).
Proof. intros. pose proof (vangle_bound a b H H0). apply sin_gt_0; ra. Qed.

(** 0 < x -> (x .* a) /_ b = a /_ b *)
Lemma vangle_vcmul_l_gt0 : forall {n} (a b : vec n) (x : R),
    0 < x -> a <> vzero -> b <> vzero -> (x \.* a) /_ b = a /_ b.
Proof.
  intros. unfold vangle. rewrite vnorm_vcmul; auto.
  rewrite vdot_vcmul_l. unfold sign. bdestruct (0 <? x); ra.
  - rewrite !Rmult_1_l. auto.
  - bdestruct (x =? 0); ra.
Qed.

(** x < 0 -> (x \.* a) /_ b = PI - a /_ b *)
Lemma vangle_vcmul_l_lt0 : forall {n} (a b : vec n) (x : R),
    x < 0 -> a <> vzero -> b <> vzero -> (x \.* a) /_ b = (PI - (a /_ b))%R.
Proof.
  intros. unfold vangle. rewrite vnorm_vcmul; auto.
  rewrite vdot_vcmul_l. unfold sign. bdestruct (0 <? x); ra.
  - bdestruct (x =? 0); ra. rewrite Rmult_neg1_l. rewrite acos_opp. auto.
  - bdestruct (x =? 0); ra.
Qed.

(** 0 < x -> a /_ (x .* b) = a /_ b *)
Lemma vangle_vcmul_r_gt0 : forall {n} (a b : vec n) (x : R),
    0 < x -> a <> vzero -> b <> vzero -> a /_ (x \.* b) = a /_ b.
Proof.
  intros. unfold vangle. rewrite vnorm_vcmul; auto.
  rewrite vdot_vcmul_r. unfold sign. bdestruct (0 <? x); ra.
  - rewrite !Rmult_1_l. auto.
  - bdestruct (x =? 0); ra.
Qed.

(** x < 0 -> a /_ (x .* b) = PI - a /_ b *)
Lemma vangle_vcmul_r_lt0 : forall {n} (a b : vec n) (x : R),
    x < 0 -> a <> vzero -> b <> vzero -> a /_ (x \.* b) = (PI - (a /_ b))%R.
Proof.
  intros. unfold vangle. rewrite vnorm_vcmul; auto.
  rewrite vdot_vcmul_r. unfold sign. bdestruct (0 <? x); ra.
  - bdestruct (x =? 0); ra. rewrite Rmult_neg1_l. rewrite acos_opp. auto.
  - bdestruct (x =? 0); ra.
Qed.

(** (vnorm a) /_ b = a /_ b *)
Lemma vangle_vnorm_l : forall {n} (a b : vec n),
    a <> vzero -> vnorm a /_ b = a /_ b.
Proof. intros. unfold vangle. rewrite vnorm_idem; auto. Qed.

(** a /_ (vnorm b) = a /_ b *)
Lemma vangle_vnorm_r : forall {n} (a b : vec n),
    b <> vzero -> a /_ vnorm b = a /_ b.
Proof. intros. unfold vangle. rewrite vnorm_idem; auto. Qed.

(** 0 < x -> (x .* a) /_ a = 0 *)
Lemma vangle_vcmul_same_l_gt0 : forall {n} (a : vec n) x,
    a <> vzero -> 0 < x -> (x \.* a) /_ a = 0.
Proof.
  intros. rewrite vangle_vcmul_l_gt0; auto. apply vangle_self; auto.
Qed.

(** 0 < x -> a /_ (x .* a) = 0 *)
Lemma vangle_vcmul_same_r_gt0 : forall {n} (a : vec n) x,
    a <> vzero -> 0 < x -> a /_ (x \.* a) = 0.
Proof.
  intros. rewrite vangle_vcmul_r_gt0; auto. apply vangle_self; auto.
Qed.

(** x < 0 -> (x * a) /_ a = π *)
Lemma vangle_vcmul_same_l_lt0 : forall {n} (a : vec n) x,
    a <> vzero -> x < 0 -> (x \.* a) /_ a = PI.
Proof.
  intros. rewrite vangle_vcmul_l_lt0; auto. rewrite vangle_self; auto. ring.
Qed.

(** x < 0 -> a /_ (x * a) = π *)
Lemma vangle_vcmul_same_r_lt0 : forall {n} (a : vec n) x,
    a <> vzero -> x < 0 -> a /_ (x \.* a) = PI.
Proof.
  intros. rewrite vangle_vcmul_r_lt0; auto. rewrite vangle_self; auto. ring.
Qed.

(** a //+ b -> a /_ b = 0 *)
Lemma vpara_imply_vangle_0 : forall {n} (a b : vec n),
    a <> vzero -> b <> vzero -> a //+ b -> a /_ b = 0.
Proof.
  intros. apply vpara_imply_uniqueX in H1. destruct H1 as [x [[H1 H2] _]].
  rewrite <- H2. rewrite vangle_vcmul_r_gt0; auto. apply vangle_self; auto.
Qed.

(** a //- b -> a /_ b = π *)
Lemma vantipara_imply_vangle_PI : forall {n} (a b : vec n),
    a <> vzero -> b <> vzero -> a //- b -> a /_ b = PI.
Proof.
  intros. apply vantipara_imply_uniqueX in H1. destruct H1 as [x [[H1 H2] _]].
  rewrite <- H2. rewrite vangle_vcmul_r_lt0; auto. rewrite vangle_self; auto. lra.
Qed.

(** a // b -> (a /_ b = 0 \/ a /_ b = π) *)
Lemma vcoll_imply_vangle_0_or_PI : forall {n} (a b : vec n),
    a <> vzero -> b <> vzero -> a // b -> (a /_ b = 0 \/ a /_ b = PI).
Proof.
  intros. apply vcoll_imply_vpara_or_vantipara in H1. destruct H1.
  - apply vpara_imply_vangle_0 in H1; auto.
  - apply vantipara_imply_vangle_PI in H1; auto.
Qed.

(* a /_ b = 0 -> a //+ b *)
Lemma vangle_0_imply_vpara : forall {n} (a b : vec n),
    a <> vzero -> b <> vzero -> a /_ b = 0 -> a //+ b.
Proof.
  intros.
  apply vangle_0_iff in H1; auto.
  unfold vpara. repeat split; auto.
Abort.

(* a /_ b = π -> a //- b *)
Lemma vangle_PI_imply_vantipara : forall {n} (a b : vec n),
    a <> vzero -> b <> vzero -> a /_ b = PI -> a //- b.
Proof.
  intros. unfold vpara. repeat split; auto.
  apply vangle_PI_iff in H1; auto.
Abort.

(* (a /_ b = 0 \/ a /_ b = π) -> a // b *)
Lemma vangle_0_or_PI_imply_vcoll : forall {n} (a b : vec n),
    a <> vzero -> b <> vzero -> (a /_ b = 0 \/ a /_ b = PI -> a // b).
Proof.
  intros. destruct H1.
  (* apply vangle_0_imply_vpara; auto. apply vangle_PI_imply_vpara; auto. *)
  (* Qed. *)
Abort.

(* a // b <-> (a /_ b = 0 \/ a /_ b = π) *)
Lemma vcoll_iff_vangle_0_or_PI : forall {n} (a b : vec n),
    a <> vzero -> b <> vzero -> (a // b <-> a /_ b = 0 \/ a /_ b = PI).
Proof.
  intros. split; intros.
  apply vcoll_imply_vangle_0_or_PI; auto.
  (*   apply vangle_0_or_PI_imply_vpara; auto. *)
  (* Qed. *)
Abort.

(** a /_ c = (a /_ b) + (b /_ c) *)
Lemma vangle_add : forall {n} (a b c : vec n), a /_ c = ((a /_ b) + (b /_ c))%R.
Proof.
(* 由于目前 vangle 只是夹角，没有区分起始和结束向量，所以该性质不成立。
   在2D和3D中有带方向的 vangle2, vangle3。并且在3D中，还需要共面条件。 *)
Abort.

(** 给定两个向量，若将这两个向量同时旋转θ角，则向量之和在旋转前后的夹角也是θ。*)
Lemma vangle_vadd : forall {n} (a b c d : vec n),
    a <> vzero -> b <> vzero ->
    ||a|| = ||c|| -> ||b|| = ||d|| ->
    a /_ b = c /_ d ->
    (a + b) /_ (c + d) = b /_ d.
Proof.
Abort.

Hint Resolve vdot_vnorm_bound : vec.

(* ======================================================================= *)
(** ** The cross product of 2D vectors *)

(* 2维向量的叉积的结果若为正，则夹角小于180度。 *)
(** u × a *)
Definition v2cross (a b : vec 2) : R := a.1 * b.2 - a.2 * b.1.

Module Export V2Notations.
  Infix "\x" := v2cross : vec_scope.
End V2Notations.

(** a × b = - (b × a) *)
Lemma v2cross_comm : forall (a b : vec 2), a \x b = (- (b \x a))%R.
Proof. intros. cbv; ra. Qed.

(** 0 <= a × b -> a × b = √((a⋅a)(b⋅b) - (a⋅b)²) *)
Lemma v2cross_ge0_eq : forall (a b : vec 2),
    a <> vzero -> b <> vzero -> 0 <= a \x b ->
    a \x b = sqrt ((<a, a> * <b, b>) - <a, b>²).
Proof.
  intros. apply Rsqr_inj. ra. ra. rewrite !Rsqr_sqrt.
  - cbv. rewrite <- !nth_v2f. field.
  - pose proof (vdot_sqr_le a b). autounfold with A in *. ra.
Qed.

(** a × b < 0 -> a × b = - √((a⋅a)(b⋅b) - (a⋅b)²) *)
Lemma v2cross_lt0_eq : forall (a b : vec 2),
    a <> vzero -> b <> vzero -> a \x b < 0 ->
    a \x b = (- sqrt ((<a, a> * <b, b>) - <a, b>²))%R.
Proof.
  intros. rewrite v2cross_comm. rewrite (vdot_comm a b).
  rewrite v2cross_ge0_eq; ra.
  - f_equal. f_equal. ring.
  - rewrite v2cross_comm; ra.
Qed.

(** a × b = 0 <-> (<a, b> = ||a|| * ||b||) *)
Lemma v2cross_eq0_iff_vdot_sqr_eq : forall (a b : vec 2),
    a <> vzero -> b <> vzero -> (a \x b = 0 <-> (<a, b>² = <a, a> * <b, b>)%R).
Proof.
  intros. bdestruct (0 <=? a \x b).
  - pose proof (vdot_sqr_le a b).
    pose proof (v2cross_ge0_eq a b H H0 H1). autounfold with A in *.
    rewrite H3. split; intros.
    + apply sqrt_eq_0 in H4; ra.
    + rewrite H4. autorewrite with R. auto.
  - split; intros; ra.
    assert (a \x b < 0); ra.
    pose proof (v2cross_lt0_eq a b H H0 H3).
    rewrite <- H2 in H4. autorewrite with R in H4. ra.
Qed.

(** (a × b = 0) <-> (a /_ b = 0) \/ (a /_ b = π) *)
Lemma v2cross_eq0_iff_vangle : forall (a b : vec 2),
    a <> vzero -> b <> vzero -> (a \x b = 0 <-> ((a /_ b = 0) \/ (a /_ b = PI))).
Proof.
  intros. rewrite v2cross_eq0_iff_vdot_sqr_eq; auto. split; intros.
  - apply vdot_sqr_eq_imply_vangle_0_or_PI; auto.
  - apply vangle_0_or_PI_imply_vdot_sqr_eq; auto.
Qed.

(** (a × b <> 0) <-> 0 < (a /_ b) < π) *)
Lemma v2cross_neq0_iff_vangle : forall (a b : vec 2),
    a <> vzero -> b <> vzero -> (a \x b <> 0 <-> (0 < (a /_ b) < PI)).
Proof.
  intros. rewrite v2cross_eq0_iff_vangle; auto.
  pose proof (vangle_bound a b H H0). ra.
Qed.


(* ======================================================================= *)
(** ** 2D vector theory *)

(** The length of 2D vector has a equal form *)
Lemma v2len_eq : forall a : vec 2, ||a|| = sqrt (a.1² + a.2²).
Proof. intros. cbv. f_equal. ra. Qed.

(** (a.1 / ||a||)² = 1 - (a.2 / ||a||)² *)
Lemma sqr_x_div_vlen : forall (a : vec 2),
    a <> vzero -> (a.1 / ||a||)² = (1 - (a.2 / ||a||)²)%R.
Proof.
  intros. rewrite !Rsqr_div'. rewrite <- !vdot_same. field_simplify_eq.
  cbv; field. apply vdot_same_neq0_if_vnonzero; auto.
Qed.

(** (a.2 / ||a||)² = 1 - (a.x / ||a||)² *)
Lemma sqr_y_div_vlen : forall (a : vec 2),
    a <> vzero -> (a.2 / ||a||)² = (1 - (a.1 / ||a||)²)%R.
Proof.
  intros. rewrite !Rsqr_div'. rewrite <- !vdot_same. field_simplify_eq.
  cbv; field. apply vdot_same_neq0_if_vnonzero; auto.
Qed.

(** 0 < <a, b> ->
    acos (<a, b> / (||a|| * ||b||)) =
    atan (sqrt (<a, a> * <b, b> - <a, b>²) / <a, b>) *)
Lemma acos_div_dot_gt0_eq : forall (a b : vec 2),
    (0 < <a, b>) ->
    acos (<a, b> / (||a|| * ||b||)) =
      atan (sqrt ((<a, a> * <b, b>) - <a, b>²) / <a, b>).
Proof.
  intros.
  assert (<a, b> <> 0); ra.
  pose proof (vdot_neq0_imply_neq0_l a b H0).
  pose proof (vdot_neq0_imply_neq0_r a b H0).
  pose proof (vlen_gt0 _ H1). pose proof (vlen_gt0 _ H2).
  pose proof (vdot_gt0 _ H1). pose proof (vdot_gt0 _ H2).
  pose proof (vdot_sqr_le a b). pose proof (vdot_sqr_le_form2 a b H1 H2).
  autounfold with A in *.
  rewrite acos_atan; [|ra]. f_equal. apply Rsqr_inj. ra. ra.
  rewrite !Rsqr_div', !Rsqr_mult, <- !vdot_sameR. field_simplify_eq; [|ra].
  rewrite Rsqr_sqrt; [|ra]. rewrite Rsqr_sqrt; [|ra].
  autorewrite with R. field. split; apply vdot_same_neq0_if_vnonzero; auto.
Qed.

(** <a, b> < 0 ->
    acos (<a, b> / (||a|| * ||b||)) =
    atan (sqrt (<a, a> * <b, b> - <a, b>²) / <a, b>) + PI *)
Lemma acos_div_dot_lt0_eq : forall (a b : vec 2),
    (<a, b> < 0) ->
    acos (<a, b> / (||a|| * ||b||)) =
      (atan (sqrt ((<a, a> * <b, b>) - <a, b>²) / <a, b>) + PI)%R.
Proof.
  intros.
  assert (<a, b> <> 0); ra.
  pose proof (vdot_neq0_imply_neq0_l a b H0).
  pose proof (vdot_neq0_imply_neq0_r a b H0).
  pose proof (vlen_gt0 _ H1). pose proof (vlen_gt0 _ H2).
  pose proof (vdot_gt0 _ H1). pose proof (vdot_gt0 _ H2).
  pose proof (vdot_sqr_le a b). pose proof (vdot_sqr_le_form2 a b H1 H2).
  autounfold with A in *.
  rewrite acos_atan_neg; [|ra]. f_equal. f_equal. apply Rsqr_inj_neg. ra. ra.
  rewrite !Rsqr_div', !Rsqr_mult, <- !vdot_same. field_simplify_eq; [|ra].
  unfold a2r, id.
  rewrite Rsqr_sqrt; [|ra]. rewrite Rsqr_sqrt; [|ra].
  autorewrite with R. field. split; apply vdot_same_neq0_if_vnonzero; auto.
Qed.

(* ======================================================================= *)
(** ** Standard base of 2-D vectors *)
Definition v2i : vec 2 := mkvec2 1 0.
Definition v2j : vec 2 := mkvec2 0 1.

(** 任意向量都能写成该向量的坐标在标准基向量下的线性组合 *)
Lemma v2_linear_composition : forall (a : vec 2), a = a.1 \.* v2i + a.2 \.* v2j.
Proof. intros. apply v2eq_iff. cbv. ra. Qed.

(** 标准基向量的长度为 1 *)
Lemma v2i_len1 : ||v2i|| = 1.
Proof. cbv. autorewrite with R; auto. Qed.

Lemma v2j_len1 : ||v2j|| = 1.
Proof. cbv. autorewrite with R; auto. Qed.

#[export] Hint Resolve v2i_len1 v2j_len1  : vec.

(** 标准基向量都是单位向量 *)
Lemma v2i_vunit : vunit v2i.
Proof. apply vunit_spec. apply v2i_len1. Qed.

Lemma v2j_vunit : vunit v2j.
Proof. apply vunit_spec. apply v2j_len1. Qed.

(** 标准基向量都是非零向量 *)
Lemma v2i_nonzero : v2i <> vzero.
Proof. intro. apply v2eq_iff in H. inv H. ra. Qed.

Lemma v2j_nonzero : v2j <> vzero.
Proof. intro. apply v2eq_iff in H. inv H. ra. Qed.

#[export] Hint Resolve v2i_nonzero v2j_nonzero : vec.

(** 标准基向量的规范化 *)
Lemma v2i_vnorm : vnorm v2i = v2i.
Proof. apply vnorm_vunit_eq. apply v2i_vunit. Qed.

Lemma v2j_vnorm : vnorm v2j = v2j.
Proof. apply vnorm_vunit_eq. apply v2j_vunit. Qed.

(** 标准基向量与任意向量 a 的点积等于 a 的各分量 *)
Lemma vdot_i_l : forall (a : vec 2), <v2i, a> = a.1. Proof. intros. cbv; ra. Qed.
Lemma vdot_i_r : forall (a : vec 2), <a, v2i> = a.1. Proof. intros. cbv; ra. Qed.
Lemma vdot_j_l : forall (a : vec 2), <v2j, a> = a.2. Proof. intros. cbv; ra. Qed.
Lemma vdot_j_r : forall (a : vec 2), <a, v2j> = a.2. Proof. intros. cbv; ra. Qed.

(** 标准基向量的夹角 *)
Lemma v2angle_i_j : v2i /_ v2j = PI/2.
Proof. cbv. match goal with |- context[acos ?a] => replace a with 0 end; ra. Qed.

(** 标准基向量的叉乘 *)
Lemma v2cross_i_l : forall (a : vec 2), v2i \x a = a.2.
Proof. intros. cbv. ring. Qed.
Lemma v2cross_i_r : forall (a : vec 2), a \x v2i = (- a.2)%R.
Proof. intros. cbv. ring. Qed.
Lemma v2cross_j_l : forall (a : vec 2), v2j \x a = (- a.1)%R.
Proof. intros. cbv. ring. Qed.
Lemma v2cross_j_r : forall (a : vec 2), a \x v2j = a.1.
Proof. intros. cbv. ring. Qed.


(* ======================================================================= *)
(** ** 2D vector angle from one to another *)

(* 
  1. vangle2 的动机：
  * vangle表示两个向量a和b的夹角θ，并未考虑两个向量的前后顺序。
    同时其值域是[0,π]，并未充满整个圆周，这将失去一些方位信息。
  * 可以规定从a到b逆时针旋转为正方向，从而将其值域扩展到 (-π,π] 或 [0,2π)。
    如果得到了 (-π, π]，则只需要当 θ∈(-π,0)时，加上2π即可。
  * 一个现有的模型是 atan2 函数。
  3. 有多种具体做法来实现这种扩展
  (1) 方法一 vangle2A
  * 做法
    由于 a⋅b = |a| |b| cos(θ) = ax*bx + ay*by
         a×b = |a| |b| sin(θ) = ax*by - ay*bx
    所以，tan(θ) = (a×b) / (a⋅b), θ = atan ((a×b) / (a⋅b))
    但是 atan 的值域是 (-π/2, π/2)。
    所以，使用 atan2 (a⋅b) (a×b)，其值域是 (-π, π]
  * 特点
    计算简单，应该是计算机软件中的常见做法。
    但是，因为 atan2 的构造有多个判断分支，也许证明不太方便。
  (2) 方法二 vangle2B
  * 做法
    首先分别得到a和b相对于x轴正方向的角度θa,θb,则所求结果是 θb-θa。
    也就是说，避开了点积和叉积运算。
  * 特点
    理解起来比较直观。但是要计算两次 atan2 运算，计算和证明都会复杂。
  (3) 方法三 vangle2C (取名为 vangle2)
  * 做法
    对之前用 acos 定义的夹角做直接的扩展。
    记夹角 vangle(a,b) 为 α，记叉积 a×b 为 Δ。定义所求的 θ 如下
    当 Δ >= 0,  θ = α  ∈ [0,π]，仅当 Δ = 0时，θ = π
    当 Δ < 0,   θ = -α ∈ (-π,0)
  * 特点
    复用了 vangle，避免了 atan2，可简化证明。
    另外，由于 vangle 的定义只在非零向量有效，所以该方法不支持零向量。
  4. 可证明这三种做法是等价的。我们选择便于证明的“方法三”。
 *)

Definition vangle2A (a b : vec 2) : R := atan2 (a \x b) (<a, b>).

Definition vangle2B (a b : vec 2) : R := atan2 (b.2) (b.1) - atan2 (a.2) (a.1).

(* Note that, vangle2C is the default choice, we will call it vangle2 for short *)
Definition vangle2 (a b : vec 2) : R :=
  let alpha := a /_ b in
  if 0 ??<= a \x b then alpha else (-alpha)%R.

Infix "/2_" := vangle2 : vec_scope.

Lemma vangle2B_vangle2A_equiv : forall (a b : vec 2), vangle2B a b = vangle2A a b.
Proof.
  intros. cbv. pose proof (atan2_minus_eq). unfold Rminus in H. rewrite H.
  f_equal; ra.
Qed.

Lemma vangle2C_vangle2A_equiv : forall (a b : vec 2),
    a <> vzero -> b <> vzero -> vangle2 a b = vangle2A a b.
Proof.
  intros. unfold vangle2A,vangle2,vangle,vnorm.
  rewrite !vdot_vcmul_l,!vdot_vcmul_r.
  pose proof (vlen_gt0 a H). pose proof (vlen_gt0 b H0).
  pose proof (vdot_gt0 a H). pose proof (vdot_gt0 b H0).
  autounfold with A.
  replace (1 / (||a||) * (1 / (||b||) * (<a, b>)))%R with ((<a, b>)/ (||a|| * ||b||)).
  2:{ field. split; apply vlen_neq0_iff_neq0; auto. }
  destruct (<a, b> ??= 0).
  - (* <a, b> = 0 *)
    rewrite e. autorewrite with R; ra.
    rewrite acos_0. destruct (0 ??<= a \x b).
    + rewrite atan2_X0_Yge0; ra.
    + rewrite atan2_X0_Ylt0; ra.
  - (* <a, b> <> 0 *)
    destruct (0 ??< <a, b>).
    + (* 0 < <a, b> *)
      rewrite acos_div_dot_gt0_eq; ra.
      rewrite atan2_Xgt0; ra. 
      destruct (0 ??<= a \x b).
      * (* 0 <= a × b *)
        rewrite v2cross_ge0_eq; ra.
      * (* a × b < 0*)
        rewrite v2cross_lt0_eq; ra.
        rewrite Rdiv_opp_l. rewrite atan_opp. auto.
    + (* <a, b> < 0 *)
      rewrite acos_div_dot_lt0_eq; ra.
      destruct (0 ??<= a \x b).
      * (* 0 <= a × b *)
        rewrite atan2_Xlt0_Yge0; ra. rewrite v2cross_ge0_eq; ra.
      * (* a × b < 0*)
        rewrite atan2_Xlt0_Ylt0; ra. rewrite v2cross_lt0_eq; ra.
        rewrite Rdiv_opp_l. rewrite atan_opp. ring.
Qed.

(* a /2_ b ∈ (-π,π] *)
Lemma vangle2_bound : forall (a b : vec 2),
    a <> vzero -> b <> vzero -> - PI < a /2_ b <= PI.
Proof.
  intros. unfold vangle2.
  pose proof PI_bound.
  pose proof (vangle_bound a b H H0).
  pose proof (v2cross_neq0_iff_vangle a b H H0).
  destruct (0 ??<= a \x b); ra.
Qed.

(** a × b = 0 -> (a /2_ b) = (b /2_ a) *)
Lemma vangle2_comm_cross_eq0 : forall (a b : vec 2),
    a <> vzero -> b <> vzero -> a \x b = 0 -> a /2_ b = b /2_ a.
Proof.
  intros. remember H1 as H2. clear HeqH2.
  apply v2cross_eq0_iff_vangle in H1; auto. destruct H1.
  - unfold vangle2. rewrite (vangle_comm b a). rewrite H1.
    destruct (_??<=_), (_??<=_); ra.
  - unfold vangle2. rewrite (vangle_comm b a). rewrite H1.
    rewrite (v2cross_comm b a). rewrite H2.
    autorewrite with R. auto.
Qed.

(** a × b <> 0 -> a /2_ b = - (b /2_ a) *)
Lemma vangle2_comm_cross_neq0 : forall (a b : vec 2),
    a <> vzero -> b <> vzero -> a \x b <> 0 -> a /2_ b = (- (b /2_ a))%R.
Proof.
  intros. remember H1 as H2. clear HeqH2.
  apply v2cross_neq0_iff_vangle in H1; auto.
  unfold vangle2. rewrite (vangle_comm b a).
  rewrite (v2cross_comm b a). destruct (_??<=_),(_??<=_); ra.
Qed.

(** i /2_ j = π/2 *)
Fact vangle2_i_j : v2i /2_ v2j = PI/2.
Proof.
  rewrite vangle2C_vangle2A_equiv; auto with vec. cbv. apply atan2_X0_Yge0; ra.
Qed.

(** j /2_ j = - π/2 *)
Fact vangle2_j_i : v2j /2_ v2i = - PI/2.
Proof.
  rewrite vangle2C_vangle2A_equiv; auto with vec. cbv. apply atan2_X0_Ylt0; ra.
Qed.

(** cos (a /2_ b) = cos (a /_ b) *)
Lemma cos_vangle2_eq : forall (a b : vec 2), cos (a /2_ b) = cos (a /_ b).
Proof. intros. unfold vangle2. destruct (_??<=_); ra. Qed.

(** sin (a /2_ b) = (0 <= a \x b) ? sin (a /_ a) : (- sin (a /_ b)) *)
Lemma sin_vangle2_eq : forall (a b : vec 2),
    sin (a /2_ b) = if 0 ??<= a \x b then sin (a /_ b) else (- sin (a /_ b))%R.
Proof. intros. unfold vangle2. destruct (_??<=_); ra. Qed.

(** i与任意非零向量v的夹角的余弦等于其横坐标除以长度 *)
Lemma cos_vangle2_i : forall (a : vec 2), a <> vzero -> cos (v2i /2_ a) = (a.1 / ||a||)%R.
Proof.
  intros. rewrite cos_vangle2_eq. unfold vangle. rewrite cos_acos; auto with vec.
  rewrite v2i_vnorm. rewrite vdot_i_l. rewrite vnth_vnorm; auto.
Qed.
  
(** i与任意非零向量v的夹角的正弦等于其纵坐标除以长度 *)
Lemma sin_vangle2_i : forall (a : vec 2), a <> vzero -> sin (v2i /2_ a) = (a.2 / ||a||)%R.
Proof.
  intros. unfold vangle2. unfold vangle. rewrite v2i_vnorm. rewrite vdot_i_l.
  rewrite vnth_vnorm; auto. pose proof (vlen_gt0 a H).
  rewrite v2cross_i_l. destruct (_??<=_).
  - rewrite sin_acos; auto with vec.
    + rewrite <- sqr_y_div_vlen; auto. ra.
    + apply vnth_div_vlen_bound; auto.
  - rewrite sin_neg. rewrite sin_acos; auto with vec.
    + rewrite <- sqr_y_div_vlen; auto. rewrite sqrt_Rsqr_abs. rewrite Rabs_left; ra.
    + apply vnth_div_vlen_bound; auto.
Qed.

(** j与任意非零向量v的夹角的余弦等于其纵坐标除以长度 *)
Lemma cos_vangle2_j : forall (a : vec 2), a <> vzero -> cos (v2j /2_ a) = (a.2 / ||a||)%R.
Proof.
  intros. rewrite cos_vangle2_eq. unfold vangle. rewrite cos_acos.
  - rewrite v2j_vnorm. rewrite vdot_j_l. rewrite vnth_vnorm; auto.
  - apply vdot_vnorm_bound; auto. apply v2j_nonzero.
Qed.

(** j与任意非零向量v的夹角的正弦等于其横坐标取负除以长度 *)
Lemma sin_vangle2_j : forall (a : vec 2),
    a <> vzero -> sin (v2j /2_ a) = (- a.1 / ||a||)%R.
Proof.
  intros. unfold vangle2. unfold vangle. rewrite v2j_vnorm. rewrite vdot_j_l.
  rewrite vnth_vnorm; auto. pose proof (vlen_gt0 a H).
  rewrite v2cross_j_l. destruct (_??<=_).
  - assert (a.1 <= 0); ra. rewrite sin_acos; auto with vec.
    + rewrite <- sqr_x_div_vlen; auto. rewrite sqrt_Rsqr_abs.
      rewrite Rabs_left1; ra.
      assert (0 < / (||a||)); ra.
    + apply vnth_div_vlen_bound; auto.
  - assert (a.1 > 0); ra. rewrite sin_neg. rewrite sin_acos; auto with vec.
    + rewrite <- sqr_x_div_vlen; auto.
      rewrite sqrt_Rsqr_abs. rewrite Rabs_right; ra.
    + apply vnth_div_vlen_bound; auto.
Qed.

(** ||a|| * cos (i /2_ a) = a.1 *)
Lemma v2len_mul_cos_vangle2_i : forall (a : vec 2),
    a <> vzero -> (||a|| * cos (v2i /2_ a) = a.1)%R.
Proof.
  intros. rewrite cos_vangle2_i; auto. field_simplify; auto.
  apply vlen_neq0_iff_neq0; auto.
Qed.

(** ||a|| * sin (i /2_ a) = a.2 *)
Lemma v2len_mul_sin_vangle2_i : forall (a : vec 2),
    a <> vzero -> (||a|| * sin (v2i /2_ a) = a.2)%R.
Proof.
  intros. rewrite sin_vangle2_i; auto. field_simplify; auto.
  apply vlen_neq0_iff_neq0; auto.
Qed.

(** ||a|| * cos (j /2_ a) = a.2 *)
Lemma v2len_mul_cos_vangle2_j : forall (a : vec 2),
    a <> vzero -> (||a|| * cos (v2j /2_ a) = a.2)%R.
Proof.
  intros. rewrite cos_vangle2_j; auto. field_simplify; auto.
  apply vlen_neq0_iff_neq0; auto.
Qed.

(** ||a|| * sin (j /2_ a) = - a.1 *)
Lemma v2len_mul_sin_vangle2_j : forall (a : vec 2),
    a <> vzero -> (||a|| * sin (v2j /2_ a) = - a.1)%R.
Proof.
  intros. rewrite sin_vangle2_j; auto. field_simplify; auto.
  apply vlen_neq0_iff_neq0; auto.
Qed.

(* ======================================================================= *)
(** ** Properties about parallel, orthogonal of 3D vectors *)

(* 与两个不共线的向量都垂直的向量是共线的 *)
Lemma vcoll_if_vorth_both : forall {n} (a b c d : vec n),
    ~(a // b) -> a _|_ c -> b _|_ c -> a _|_ d -> b _|_ d -> c // d.
Proof.
Abort.

(** 两个平行向量 a 和 b 若长度相等，则 a = b *)
Lemma vpara_and_same_len_imply : forall {n} (a b : vec n),
    a //+ b -> ||a|| = ||b|| -> a = b.
Proof.
  intros. destruct H as [H1 [H2 [x [H3 H4]]]].
  destruct (Aeqdec a vzero), (Aeqdec b vzero); try easy.
  assert (x = 1).
  { rewrite <- H4 in H0. rewrite vlen_vcmul in H0. unfold a2r,id in H0.
    symmetry in H0. apply Rmult_eq_r_reg in H0; auto.
    autounfold with A in *. unfold Aabs in H0. destruct (Ale_dec 0 x); lra.
    apply vlen_neq0_iff_neq0; auto. }
  rewrite H in H4. rewrite vcmul_1_l in H4; auto.
Qed.

(** 两个反平行向量 a 和 b 若长度相等，则 a = - b *)
Lemma vantipara_and_same_len_imply : forall {n} (a b : vec n),
    a //- b -> ||a|| = ||b|| -> a = -b.
Proof.
  intros. destruct H as [H1 [H2 [x [H3 H4]]]].
  destruct (Aeqdec a vzero), (Aeqdec b vzero); try easy.
  assert (x = - (1))%R.
  { rewrite <- H4 in H0. rewrite vlen_vcmul in H0. unfold a2r,id in H0.
    symmetry in H0. apply Rmult_eq_r_reg in H0; auto.
    autounfold with A in *. unfold Aabs in H0. destruct (Ale_dec 0 x); lra.
    apply vlen_neq0_iff_neq0; auto. }
  rewrite H in H4. rewrite vcmul_neg1_l in H4. rewrite <- H4, vopp_vopp. auto.
Qed.

(** 两个共线向量 a 和 b 若长度相等，则 a = ± b *)
Lemma vcoll_and_same_len_imply : forall {n} (a b : vec n),
    a // b -> ||a|| = ||b|| -> a = b \/ a = -b.
Proof.
  intros. destruct (vcoll_imply_vpara_or_vantipara a b H).
  - left. apply vpara_and_same_len_imply; auto.
  - right. apply vantipara_and_same_len_imply; auto.
Qed.

(* ======================================================================= *)
(** ** The cross product (vector product) of two 3-dim vectors *)
(* 1. 外积的几何学(三角学)意义  ||a × b|| = ||a|| * ||b|| * sin α
   2. 外积若不为零，则其与这两个向量都垂直。有两个向量，方向相反。
      根据所选左/右手系来确定方向。
   3. 3D坐标系中的x,y,z轴正方向用 i,j,k 表示，并按 i,j,k 顺序组成一个循环，则：
   (1) 相邻两个向量按相同次序的外积为第三个向量，即 i×j=k, j×k=i, k×i=j。
   (2) 相邻两个向量按相反次序的外积为第三个向量的取反，即 j×i=-k, etc. *)

(** The cross product of 3D vectors a and b *)
Definition v3cross (a b : vec 3) : vec 3 :=
  mkvec3
    (a.2 * b.3 - a.3 * b.2)%R
    (a.3 * b.1 - a.1 * b.3)%R
    (a.1 * b.2 - a.2 * b.1)%R.
Infix "\x" := v3cross : vec_scope.

(* functional style, for C-code generation *)
Definition v3crossFun (a b : vec 3) : vec 3 :=
  f2v (fun i =>
         match i with
         | 0 => a.2 * b.3 - a.3 * b.2
         | 1 => a.3 * b.1 - a.1 * b.3
         | 2 => a.1 * b.2 - a.2 * b.1
         | _=> 0
         end)%R.

(* These two definitions should equiv *)
Lemma v3cross_v3crossFun_equiv : forall a b : vec 3, a \x b = v3crossFun a b.
Proof. intros. apply v3eq_iff. auto. Qed.

(** a × a = 0 *)
Lemma v3cross_self : forall a : vec 3, a \x a = vzero.
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** a × b = - (b × a) *)
Lemma v3cross_anticomm : forall a b : vec 3, a \x b = -(b \x a).
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** (a + b) × c = (a × c) + (b × c) *)
Lemma v3cross_add_distr_l : forall a b c : vec 3,
    (a + b) \x c = (a \x c) + (b \x c).
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** a × (b + c) = (a × b) + (a × c) *)
Lemma v3cross_add_distr_r : forall a b c : vec 3,
    a \x (b + c) = (a \x b) + (a \x c).
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** (- a) × b = - (a × b) *)
Lemma v3cross_vopp_l : forall a b : vec 3, (-a) \x b = - (a \x b).
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** a × (- b) = - (a × b) *)
Lemma v3cross_vopp_r : forall a b : vec 3, a \x (-b) = - (a \x b).
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** (a - b) × c = (a × c) - (b × c) *)
Lemma v3cross_sub_distr_l : forall a b c : vec 3,
    (a - b) \x c = (a \x c) - (b \x c).
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** a × (b - c) = (a × b) - (a × c) *)
Lemma v3cross_sub_distr_r : forall a b c : vec 3,
    a \x (b - c) = (a \x b) - (a \x c).
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** (x .* a) × b = x .* (a × b) *)
Lemma v3cross_vcmul_assoc_l : forall (x : R) (a b : vec 3),
    (x \.* a) \x b = x \.* (a \x b).
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** a × (x .* b) = x \.* (a × b) *)
Lemma v3cross_vcmul_assoc_r : forall (x : R) (a b : vec 3),
    a \x (x \.* b) = x \.* (a \x b).
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** <a × b, c> = <c × a, b> *)
Lemma v3cross_vdot_l : forall a b c : vec 3, <a \x b, c> = <c \x a, b>.
Proof. intros. cbv. field. Qed.

(** <a × b, c> = <b × c, a> *)
Lemma v3cross_dot_r : forall a b c : vec 3, <a \x b, c> = <b \x c, a>.
Proof. intros. cbv. field. Qed.

(** <a × b, a> = 0 *)
Lemma v3cross_vdot_same_l : forall a b : vec 3, <a \x b, a> = 0.
Proof. intros. cbv. field. Qed.

(** <a × b, b> = 0 *)
Lemma v3cross_vdot_same_r : forall a b : vec 3, <a \x b, b> = 0.
Proof. intros. cbv. field. Qed.

(** a × (a × b) = (a × b) × a *)
Lemma v3cross_a_ba : forall a b : vec 3, a \x (b \x a) = (a \x b) \x a.
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** a × (a × b) = - (a × (b × a)) *)
Lemma v3cross_a_ab : forall a b : vec 3, a \x (a \x b) = - ((a \x b) \x a).
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** (a × b) × a = <a, a> \.* a - <a, b> \.* a *)
Lemma v3cross_ab_a_eq_minus : forall a b : vec 3,
    (a \x b) \x a = <a, a> \.* b - <a, b> \.* a.
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** a × (b × a) = <a, a> \.* b - <a, b> \.* a *)
Lemma v3cross_a_ba_eq_minus : forall a b : vec 3,
    a \x (b \x a) = <a, a> \.* b - <a, b> \.* a.
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** a × (a × b) = <a, b> \.* a - <a, a> \.* b *)
Lemma v3cross_a_ab_eq_minus : forall a b : vec 3,
    a \x (a \x b) = <a, b> \.* a - <a, a> \.* b.
Proof. intros. apply v3eq_iff; cbv; ra. Qed.

(** <a × b, c × d> = <a, c> * <b, d> - <a, d> * <b, c> *)
Lemma v3cross_dot_v3cross : forall (a b c d : vec 3),
    (<a \x b, c \x d > = (<a, c> * <b, d>) - (<a, d> * <b, c>))%R.
Proof.
  (* 我尚未完成推理，先暴力证明 *)
  intros. cbv; ra.
Qed.

(** (a × b) ⟂ a *)
Lemma v3cross_orth_l : forall a b : vec 3, (a \x b) _|_ a.
Proof. intros. unfold vorth. apply v3cross_vdot_same_l. Qed.

(** (a × b) ⟂ b *)
Lemma v3cross_orth_r : forall a b : vec 3, (a \x b) _|_ b.
Proof. intros. unfold vorth. apply v3cross_vdot_same_r. Qed.

(** || a × b ||² = ||a||² * ||b||² - <a, b>² *)
Lemma vlen_v3cross_form1 : forall a b : vec 3,
    || a \x b ||² = ((||a||² * ||b||²) - (<a, b>)²)%R.
Proof. intros. rewrite <- !vdot_same. cbv; ra. Qed.

(** || a × b || = ||a|| * ||b|| * |sin (a /_ b)| *)
Lemma vlen_v3cross : forall a b : vec 3,
    a <> vzero -> b <> vzero -> || a \x b || = (||a|| * ||b|| * sin (a /_ b))%R.
Proof.
  intros. pose proof (vlen_v3cross_form1 a b).
  rewrite vdot_eq_cos_angle in H1. rewrite !Rsqr_mult in H1. rewrite cos2 in H1.
  apply Rsqr_inj; ra. apply vlen_ge0.
  apply Rmult_le_pos. apply vlen_ge0.
  apply Rmult_le_pos. apply vlen_ge0. apply sin_vangle_ge0; auto.
Qed.

(** ||a × b|| = 0 <-> (θ = 0 \/ θ = PI) *)
Lemma vlen_v3cross_eq0_iff_angle_0_pi : forall (a b : vec 3),
    a <> vzero -> b <> vzero -> ||a \x b|| = 0 <-> (a /_ b = 0 \/ a /_ b = PI).
Proof.
  intros. rewrite vlen_v3cross; auto.
  pose proof (vangle_bound a b H H0).
  apply vlen_neq0_iff_neq0 in H,H0.
  split; intros.
  - apply Rmult_integral in H2; destruct H2; ra.
    apply Rmult_integral in H2; destruct H2; ra.
    apply sin_eq_O_2PI_0 in H2; ra.
  - apply Rmult_eq_0_compat. right.
    apply Rmult_eq_0_compat. right.
    apply sin_eq_O_2PI_1; ra.
Qed.

(** a × b = vzero <-> (θ = 0 \/ θ = PI) *)
Lemma v3cross_eq0_iff_angle_0_pi : forall (a b : vec 3),
    a <> vzero -> b <> vzero -> (a \x b = vzero <-> (a /_ b = 0 \/ a /_ b = PI)).
Proof.
  intros. rewrite <- vlen_v3cross_eq0_iff_angle_0_pi; auto.
  rewrite vlen_eq0_iff_eq0. easy.
Qed.

(** a × b = vzero <-> a // b *)
Lemma v3cross_eq0_iff_vcoll : forall (a b : vec 3),
    a <> vzero -> b <> vzero -> (a \x b = vzero <-> a // b).
Proof.
  intros. rewrite v3cross_eq0_iff_angle_0_pi; auto. split; intros.
  2:{ apply vcoll_imply_vangle_0_or_PI; auto. }
  -
Abort.

(** a × b = (sin (u ∠ a) * ||a|| * ||b||) \.* vnorm (a × b) *)
Lemma v3cross_eq_vcmul : forall (a b : vec 3),
    a <> vzero -> b <> vzero ->
    a /_ b <> 0 -> a /_ b <> PI ->
    a \x b = ((sin (a /_ b) * ||a|| * ||b||)%R \.* vnorm (a \x b)).
Proof.
  intros. unfold vnorm. rewrite vlen_v3cross; auto.
  rewrite vcmul_assoc.
  match goal with |- context [?x \.* _] => replace x with 1 end.
  rewrite vcmul_1_l; easy.
  autounfold with A. field. repeat split.
  - pose proof (sin_vangle_gt0 a b H H0). ra.
  - apply vlen_neq0_iff_neq0; auto.
  - apply vlen_neq0_iff_neq0; auto.
Qed.

(** If a ∠ b ∈ (0,π) (that is they are Linear-Independent), then a × b is 
    nonzero. *)
Lemma v3cross_neq0_if_vangle_in_0_pi : forall (a b : vec 3),
    a <> vzero -> b <> vzero -> 0 < a /_ b < PI -> a \x b <> vzero.
Proof.
  intros. apply vlen_neq0_iff_neq0.
  intro. apply vlen_v3cross_eq0_iff_angle_0_pi in H2; auto. ra.
Qed.


(* ======================================================================= *)
(** ** Skew-symmetric matrix of 3-dimensions *)

(** Equivalent form of skewP of 3D vector *)
Lemma skewP3_eq : forall M : mat 3 3,
    skewP M <->
      (M.11 = 0) /\ (M.22 = 0) /\ (M.33 = 0) /\
        (M.12 = -M.21 /\ M.13 = -M.31 /\ M.23 = -M.32)%R.
Proof.
  intros. split; intros.
  - hnf in H. assert (m2l (- M)%M = m2l (M\T)). rewrite H. auto.
    cbv in H0. list_eq. cbv. ra.
  - hnf. cbv in H. meq; ra.
Qed.

(** Convert a vector to its corresponding skew-symmetric matrix *)
Definition skew3 (a : vec 3) : mat 3 3 :=
  l2m [[0;    -a.3; a.2 ];
       [a.3;  0;    -a.1];
       [-a.2; a.1;  0   ]]%R.
Notation "`| a |x" := (skew3 a) : vec_scope.

Lemma skew3_spec : forall a, skewP (skew3 a).
Proof. intros. rewrite skewP3_eq. cbv. lra. Qed.

(** Convert a skew-symmetric matrix to its corresponding vector *)
Definition vex3 (M : mat 3 3) : vec 3 := l2v [M.32; M.13; M.21].

Lemma skew3_vex3 : forall (m : mat 3 3), skewP m -> skew3 (vex3 m) = m.
Proof. intros. apply skewP3_eq in H. cbv in H. meq; ra. Qed.

Lemma vex3_skew3 : forall (a : vec 3), vex3 (skew3 a) = a.
Proof. intros. veq. Qed.

Lemma v3cross_eq_skew_mul_vec : forall (a b : vec 3),
    a \x b = `|a|x *v b.
Proof. intros; veq; ra. Qed.

Lemma v3cross_eq_skew_mul_cvec : forall (a b : cvec 3),
    cv2v a \x (cv2v b) = cv2v ((`|cv2v a|x * b)%M).
Proof. intros; veq; ra. Qed.

Section examples.
  
  (** Example 4, page 19, 高等数学，第七版 *)
  Example v3cross_example1 : (l2v [2;1;-1]) \x (l2v [1;-1;2]) = l2v [1;-5;-3].
  Proof. veq; ra. Qed.

  (** Example 5, page 19, 高等数学，第七版 *)
  (** 根据三点坐标求三角形面积 *)
  Definition area_of_triangle (A B C : vec 3) :=
    let AB := B - A in
    let AC := C - A in
    ((1/2) * ||AB \x AC||)%R.

  (** Example 6, page 20, 高等数学，第七版 *)
  (** 刚体绕轴以角速度 ω 旋转，某点M（OM为向量r⃗）处的线速度v⃗，三者之间的关系*)
  Definition v3_rotation_model (ω r a : vec 3) := a = ω \x r.
  
End examples.

(* ======================================================================= *)
(** ** 3D vector theory *)

(** vdot in 3D has given form *)
Lemma v3dot_eq : forall a b : vec 3, <a, b> = (a.1 * b.1 + a.2 * b.2 + a.3 * b.3)%R.
Proof. intros. cbv. ring. Qed.

(** A 3D unit vector satisfy these algebraic equations *)

Lemma v3unit_sqr_xyz : forall (a : vec 3), vunit a -> (a.1² + a.2² + a.3² = 1)%R.
Proof. intros. cbv in *. ra. Qed.

Lemma v3unit_sqr_xzy : forall (a : vec 3), vunit a -> (a.1² + a.3² + a.2² = 1)%R.
Proof. intros. cbv in *. ra. Qed.

Lemma v3unit_sqr_yzx : forall (a : vec 3), vunit a -> (a.2² + a.3² + a.1² = 1)%R.
Proof. intros. cbv in *. ra. Qed.

Lemma v3unit_sqr_yxz : forall (a : vec 3), vunit a -> (a.2² + a.1² + a.3² = 1)%R.
Proof. intros. cbv in *. ra. Qed.

Lemma v3unit_sqr_zxy : forall (a : vec 3), vunit a -> (a.3² + a.1² + a.2² = 1)%R.
Proof. intros. cbv in *. ra. Qed.

Lemma v3unit_sqr_zyx : forall (a : vec 3), vunit a -> (a.3² + a.2² + a.1² = 1)%R.
Proof. intros. cbv in *. ra. Qed.

Lemma v3unit_sqr_x : forall (a : vec 3), vunit a -> a.1² = (1 - a.2² - a.3²)%R.
Proof. intros. cbv in *. ra. Qed.

Lemma v3unit_sqr_y : forall (a : vec 3), vunit a -> a.2² = (1 - a.1² - a.3²)%R.
Proof. intros. cbv in *. ra. Qed.

Lemma v3unit_sqr_z : forall (a : vec 3), vunit a -> a.3² = (1 - a.1² - a.2²)%R.
Proof. intros. cbv in *. ra. Qed.

(** vnorm a = (a.1 / ||a||, a.2 / ||a||, a.3 / ||v||) *)
Lemma v3norm_eq : forall (a : vec 3),
    let v' := vnorm a in
    a <> vzero -> (v'.1 = a.1 / ||a||) /\ (v'.2 = a.2 / ||a||) /\ (v'.3 = a.3 / ||a||).
Proof.
  intros. unfold v', vnorm. rewrite !vnth_vcmul. autounfold with A.
  repeat split; ra.
Qed.

Lemma v3norm_sqr_eq1 : forall (a : vec 3),
    a <> vzero -> ((a.1 / ||a||)² + (a.2 / ||a||)² + (a.3 / ||a||)² = 1)%R.
Proof.
  intros. pose proof (vdot_same_neq0_if_vnonzero a H).
  rewrite !Rsqr_div'. rewrite <- !vdot_same. cbv. field. cbv in H0. ra.
Qed.

(** Projection component of vector in 3D : 投影分量 *)
(*
  (** The matrix form of vproj in 3-dim *)
  Definition v3proj (a b : vec 3) : vec 3 :=
    let x := a.1 in
    let y := a.2 in
    let z := a.3 in
    let M : mat 3 3 :=
      l2m [[x * x; x * y; x * z];
           [y * x; y * y; y * z];
           [z * x; z * y; z * z]]%R in
    (1 / <a, a>) \.* (M * u).

  Lemma v3proj_spec : forall a b : vec 3, v3proj a b = vproj a b.
  Proof. apply v3eq_iff; cbv; ra. Qed.

  (** a × (proj a b) = 0 *)
  Lemma v3cross_v3proj_eq0 : forall a b : vec 3, a \x v3proj a b = vzero.
  Proof. apply v3eq_iff; cbv; ra. Qed.
 *)

(** Perpendicular component of vector in 3D : 垂直分量 *)

(** The perpendicular vector can be get from cross product.
    ref: https://en.wikipedia.org/wiki/Rodrigues%27_rotation_formula.
    利用两次叉乘得到垂直分量的表示。此式在几何上容易理解，但代数上不是很显然。*)
Definition v3perp (a b : vec 3) : vec 3 := - ((a \x b) \x b).

Lemma v3perp_spec : forall (a b : vec 3), vunit b -> v3perp a b = vperp a b.
Proof.
  intros.
  pose proof (v3unit_sqr_xyz b H) as H0; cbv in H0; rewrite <- !nth_v2f in H0.
  apply v3eq_iff. repeat split; cbv; rewrite <- !nth_v2f; field_simplify; try lra.
  - pose proof (v3unit_sqr_xzy b H) as H1; cbv in H1; rewrite <- !nth_v2f in H1.
    ring_simplify in H1; rewrite H1; field.
  - pose proof (v3unit_sqr_yxz b H) as H1; cbv in H1; rewrite <- !nth_v2f in H1.
    ring_simplify in H1; rewrite H1; field.
  - pose proof (v3unit_sqr_zyx b H) as H1; cbv in H1; rewrite <- !nth_v2f in H1.
    ring_simplify in H1; rewrite H1; clear H1. field.
Qed.

(** Two vectors in 3D are parallel, can be determined by cross-product.
      That is: a // b <-> a × b = 0 *)
Definition v3para (a b : vec 3) : Prop := a \x b = vzero.

Lemma v3para_spec : forall (a b : vec 3),
    a <> vzero -> b <> vzero -> (a // b <-> v3para a b).
Proof.
  intros. unfold v3para. rewrite v3cross_eq0_iff_angle_0_pi; auto.
  (*   apply vpara_iff_vangle_0_or_PI; auto. *)
  (* Qed. *)
Abort.


(* ======================================================================= *)
(** ** Standard base for Euclidean space (3-D vectors) *)

Definition v3i : vec 3 := mkvec3 1 0 0.
Definition v3j : vec 3 := mkvec3 0 1 0.
Definition v3k : vec 3 := mkvec3 0 0 1.

(** 任意向量都能写成该向量的坐标在标准基向量下的线性组合 *)
Lemma v3_linear_composition : forall (a : vec 3),
    a = a.1 \.* v3i + a.2 \.* v3j + a.3 \.* v3k.
Proof. intros. apply v3eq_iff. cbv. ra. Qed.

(** 标准基向量的长度为 1 *)
Lemma v3i_len1 : ||v3i|| = 1. Proof. cbv. autorewrite with R; auto. Qed.
Lemma v3j_len1 : ||v3j|| = 1. Proof. cbv. autorewrite with R; auto. Qed.
Lemma v3k_len1 : ||v3k|| = 1. Proof. cbv. autorewrite with R; auto. Qed.

(** 标准基向量都是单位向量 *)
Lemma v3i_vunit : vunit v3i. Proof. apply vunit_spec. apply v3i_len1. Qed.
Lemma v3j_vunit : vunit v3j. Proof. apply vunit_spec. apply v3j_len1. Qed.
Lemma v3k_vunit : vunit v3k. Proof. apply vunit_spec. apply v3k_len1. Qed.

(** 标准基向量都是非零向量 *)
Lemma v3i_nonzero : v3i <> vzero.
Proof. intro. apply v3eq_iff in H. destruct H as [H1 [H2 H3]]. ra. Qed.

Lemma v3j_nonzero : v3j <> vzero.
Proof. intro. apply v3eq_iff in H. destruct H as [H1 [H2 H3]]. ra. Qed.

Lemma v3k_nonzero : v3k <> vzero.
Proof. intro. apply v3eq_iff in H. destruct H as [H1 [H2 H3]]. ra. Qed.

(** 标准基向量的规范化 *)
Lemma v3i_vnorm : vnorm v3i = v3i.
Proof. apply vnorm_vunit_eq. apply v3i_vunit. Qed.

Lemma v3j_vnorm : vnorm v3j = v3j.
Proof. apply vnorm_vunit_eq. apply v3j_vunit. Qed.

Lemma v3k_vnorm : vnorm v3k = v3k.
Proof. apply vnorm_vunit_eq. apply v3k_vunit. Qed.

(** 标准基向量与任意向量v的点积等于v的各分量 *)
Lemma v3dot_i_l : forall a : vec 3, <v3i, a> = a.1. Proof. intros. cbv; ring. Qed.
Lemma v3dot_j_l : forall a : vec 3, <v3j, a> = a.2. Proof. intros. cbv; ring. Qed.
Lemma v3dot_k_l : forall a : vec 3, <v3k, a> = a.3. Proof. intros. cbv; ring. Qed.
Lemma v3dot_i_r : forall a : vec 3, <a, v3i> = a.1. Proof. intros. cbv; ring. Qed.
Lemma v3dot_j_r : forall a : vec 3, <a, v3j> = a.2. Proof. intros. cbv; ring. Qed.
Lemma v3dot_k_r : forall a : vec 3, <a, v3k> = a.3. Proof. intros. cbv; ring. Qed.

(** i × j = k, j × x = i, x × i = j *)
Lemma v3cross_ij : v3i \x v3j = v3k. Proof. apply v3eq_iff; cbv; ra. Qed.
Lemma v3cross_jk : v3j \x v3k = v3i. Proof. apply v3eq_iff; cbv; ra. Qed.
Lemma v3cross_ki : v3k \x v3i = v3j. Proof. apply v3eq_iff; cbv; ra. Qed.

(** j × i = -k, x × j = -i, i × x = -j *)
Lemma v3cross_ji : v3j \x v3i = - v3k. Proof. apply v3eq_iff; cbv; ra. Qed.
Lemma v3cross_kj : v3k \x v3j = - v3i. Proof. apply v3eq_iff; cbv; ra. Qed.
Lemma v3cross_ik : v3i \x v3k = - v3j. Proof. apply v3eq_iff; cbv; ra. Qed.

(** 矩阵乘以标准基向量得到列向量 *)
Lemma mmulv_v3i : forall (M : smat 3), M *v v3i = M&1. Proof. intros; veq; ra. Qed.
Lemma mmulv_v3j : forall (M : smat 3), M *v v3j = M&2. Proof. intros; veq; ra. Qed.
Lemma mmulv_v3k : forall (M : smat 3), M *v v3k = M&3. Proof. intros; veq; ra. Qed.

(** 矩阵的列向量等于矩阵乘以标准基向量 *)
Lemma mcol_eq_mul_v3i : forall (M : smat 3), M&1 = M *v v3i. Proof. intros; veq; ra. Qed.
Lemma mcol_eq_mul_v3j : forall (M : smat 3), M&2 = M *v v3j. Proof. intros; veq; ra. Qed.
Lemma mcol_eq_mul_v3k : forall (M : smat 3), M&3 = M *v v3k. Proof. intros; veq; ra. Qed.

(** 矩阵的行向量等于矩阵乘以标准基向量 *)
Lemma mrow_eq_mul_v3i : forall (M : smat 3), M.1 = M\T *v v3i.
Proof. intros; veq; ra. Qed.
Lemma mrow_eq_mul_v3j : forall (M : smat 3), M.2 = M\T *v v3j.
Proof. intros; veq; ra. Qed.
Lemma mrow_eq_mul_v3k : forall (M : smat 3), M.3 = M\T *v v3k.
Proof. intros; veq; ra. Qed.

(** 标准基向量的夹角 *)
Lemma v3angle_i_j : v3i /_ v3j = PI/2.
Proof. cbv. match goal with |- context[acos ?a] => replace a with 0 end; ra. Qed.

Lemma v3angle_j_k : v3j /_ v3k = PI/2.
Proof. cbv. match goal with |- context[acos ?a] => replace a with 0 end; ra. Qed.

Lemma v3angle_k_i : v3k /_ v3i = PI/2.
Proof. cbv. match goal with |- context[acos ?a] => replace a with 0 end; ra. Qed.

(* ======================================================================= *)
(** ** Direction cosine of 3-D vectors *)

(* ToDo:
   ref: https://en.wikipedia.org/wiki/Euclidean_vector
   关于方向余弦矩阵，这里有更多的工作要做，不仅仅是三维，
   它可用于表示在不同的笛卡尔基之间的变换。
   
   以三维为例，给定两组基{e1,e2,e3}和{n1,n2,n3}，
   任意向量a可以被表示为 a = pe1 + qe2 + re3 = un1 + vn2 + wn3，
   而每个系数可这样获得 p = a⋅e1, q = a⋅e2, 依次类推。

   于是我们可以根据第一组基下的坐标来计算第二组基下的坐标
   u = (pe1 + qe2 + re3)⋅n1 = pe1⋅n1 + qe2⋅n1 + re3⋅n1,
   a = (pe1 + qe2 + re3)⋅n2 = pe1⋅n2 + qe2⋅n2 + re3⋅n2,
   w = (pe1 + qe2 + re3)⋅n3 = pe1⋅n3 + qe2⋅n3 + re3⋅n3.

   将每个点积用一个唯一的标量代替后得到
   u = c11p + c12q + c13r,
   a = c21p + c22q + c23r,
   w = c31p + c32q + c33r.
   
   这些方程表示为单个矩阵等式
   [u]   [c11 c12 c13] [p]
   [v] = [c21 c22 c23] [q]. 
   [w]   [c31 c32 c33] [r]

   该矩阵等式关联了向量a在基n下的坐标(u,v,w)和在基e下的奏表(p,q,r)。
   每个矩阵元素cjk是nj和ek的方向余弦，（即，两个向量夹角的余弦，也等于点积）。
   因此，
   c11 = n1⋅e1, c12 = n1⋅e2, c13 = n1⋅e3
   c21 = n2⋅e1, c12 = n2⋅e2, c13 = n2⋅e3
   c31 = n3⋅e1, c12 = n3⋅e2, c13 = n3⋅e3

   上述包含了所有cjk的矩阵称为“从e到n的变换矩阵”，或“从e到n的旋转矩阵”，或“从e到n的
   方向余弦矩阵”。
 *)

(** Direction cosine of a vector relative to standard basis.
      That is : (cos α, cos β, cos γ) *)
Definition v3dc (a : vec 3) : vec 3 :=
  mkvec3 (a.1 / ||a||) (a.2 / ||a||) (a.3 / ||a||). 

(** The original (lower level) definition as its spec. *)
Lemma v3dc_spec : forall (a : vec 3),
    let a' := v3dc a in
    let r := ||a|| in 
    (a'.1 = <a, v3i> / r) /\ a'.2 = (<a, v3j> / r) /\ a'.3 = (<a, v3k> / r).
Proof. intros. rewrite v3dot_i_r, v3dot_j_r, v3dot_k_r; auto. Qed.

(** dc of a nonzero vector is a unit vector *)
Lemma v3dc_unit : forall (a : vec 3), a <> vzero -> vunit (v3dc a).
Proof.
  intros. unfold vunit,Vector.vunit. cbn.
  erewrite !nth_v2f, !Vector.vnth_vmap2; cbn.
  pose proof (v3norm_sqr_eq1 a H).
  autounfold with A in *; autorewrite with R in *; lra.
  Unshelve. all: lia.
Qed.


(* ======================================================================= *)
(** ** The triple scalar product (or called Mixed products) of 3-D vectors *)

(** [a b c] = <u×v, w>
    几何意义：绝对值表示以向量a,b,c为棱的平行六面体的体积，另外若a,b,c组成右手系，
    则混合积的符号为正；若组成左手系，则符号为负。*)
Definition v3mixed (a b c : vec 3) : R := <a \x b, c>.
Notation "`[ a b c ]" :=
  (v3mixed a b c) (at level 1, a, b at level 9, format "`[ a  b  c ]") : vec_scope.

(* alternate definition of v3mixed *)
Lemma v3mixed_swap_op : forall (a b c : vec 3), <a, b \x c> = <a \x b, c>.
Proof. intros. cbv. ring. Qed.

(** The mixed product with columns is equal to the determinant *)
Lemma v3mixed_eq_det_cols : forall a b c : vec 3, `[a b c] = mdet (cvl2m [a;b;c]).
Proof. intros. cbv. ring. Qed.

(** The mixed product with rows is equal to the determinant *)
Lemma v3mixed_eq_det_rows : forall a b c : vec 3, `[a b c] = mdet (rvl2m [a;b;c]).
Proof. intros. cbv. ring. Qed.

(** [a b c] = [b c a] *)
Lemma v3mixed_comm : forall (a b c : vec 3), `[a b c] = `[b c a].
Proof. intros. cbv. ring. Qed.

(** 若混合积≠0，则三向量可构成平行六面体，即三向量不共面，反之也成立。
    所以：三向量共面的充要条件是混合积为零。*)
Definition v3coplanar (a b c : vec 3) : Prop := `[a b c] = 0.

(** (a,b) 的法向量和 (b,c) 的法向量相同，则 (a,b,c) 共面 *)
Lemma v3cross_same_v3coplanar : forall a b c : vec 3,
    a \x b = b \x c -> v3coplanar a b c.
Proof.
  intros. unfold v3coplanar, v3mixed. rewrite H. apply v3cross_vdot_same_r.
Qed.

(** Example 7, page 22, 高等数学，第七版 *)
(** 根据四顶点的坐标，求四面体的体积：四面体ABCD的体积等于AB,AC,AD为棱的平行六面体
    的体积的六分之一 *)
Definition v3_volume_of_tetrahedron (A B C D : vec 3) :=
  let AB := B - A in
  let AC := C - A in
  let AD := D - A in
  ((1/6) * `[AB AC AD])%R.

(** u,v,w ∈ one-plane, u ∠ w = (u ∠ a) + (a ∠ w) *)
Lemma v3angle_add : forall (a b c : vec 3),
    a /_ b < PI ->
    b /_ c < PI ->
    v3coplanar a b c ->
    a /_ c = ((a /_ b) + (b /_ c))%R.
Proof.
  (* 由于 a /_ b 和 b /_ a 并没有区分，所以该性质不成立。*)
  (* intros. unfold vangle. unfold vnorm. unfold vlen. *)
  (* unfold vcmul. unfold vdot. unfold Vector.vdot. *)
  (* vec2fun. unfold Tmul,Tadd,T0,T. *)
  (* autorewrite with R. *)
Abort.


(* ======================================================================= *)
(** ** Standard base for 4-D vectors *)

Definition v4i : vec 4 := mkvec4 1 0 0 0.
Definition v4j : vec 4 := mkvec4 0 1 0 0.
Definition v4k : vec 4 := mkvec4 0 0 1 0.
Definition v4l : vec 4 := mkvec4 0 0 0 1.


(* ======================================================================= *)
(** ** matrix norm *)

Open Scope mat_scope.

(** norm space *)
Class Norm `{Ring} (f : A -> R) (cmul : R -> A -> A) := {
    Norm_pos : forall a : A, 0 <= f a;
    Norm_eq0_iff : forall a : A, f a = 0 <-> a = Azero;
    Norm_cmul_compat : forall (c : R) (a : A), f (cmul c a) = ((Rabs c) * f a)%A
  }.

(* Equivalent form of matrix norm *)
Definition mnorm_spec_pos {r c} (mnorm : mat r c -> R) : Prop :=
  forall M : mat r c,
    (M <> mat0 -> mnorm M > 0) /\ (M = mat0 -> mnorm M = 0).

Definition mnorm_spec_mcmul {r c} (mnorm : mat r c -> R) : Prop :=
  forall (M : mat r c) (x : R),
    mnorm (x \.* M) = ((Rabs x) * (mnorm M))%R.

Definition mnorm_spec_trig {r c} (mnorm : mat r c -> R) : Prop :=
  forall (M N : mat r c),
    mnorm (M + N) <= mnorm M + mnorm N.

(* ======================================================================= *)
(** ** matrix F norm *)

(* F-norm (M) := √(∑∑M(i,j)²) *)
Definition mnormF {r c} (M : mat r c) : R :=
  sqrt (vsum (fun i => vsum (fun j => (M.[i].[j])²))).

(** mnormF m = √ tr (M\T * M) *)
Lemma mnormF_eq_trace : forall {r c} (M : mat r c),
    mnormF M = sqrt (tr (M\T * M)).
Proof.
  intros. unfold mnormF. f_equal. unfold mtrace, Matrix.mtrace.
  rewrite vsum_vsum. auto.
Qed.

Lemma mnormF_spec_pos : forall r c, mnorm_spec_pos (@mnormF r c).
Proof.
  intros. hnf. intros. split; intros.
  - unfold mnormF. apply sqrt_lt_R0. apply vsum_gt0.
    + intros. apply vsum_ge0. intros. apply sqr_ge0.
    + apply mneq_iff_exist_mnth_neq in H. destruct H as [i [j H]].
      exists i. intro. apply vsum_eq0_rev with (i:=j) in H0; auto.
      * rewrite mnth_mat0 in H. cbv in H. ra.
      * intros. cbv. ra.
  - rewrite H. unfold mnormF.
    apply sqrt_0_eq0. apply vsum_eq0; intros. apply vsum_eq0; intros.
    rewrite mnth_mat0. ra.
Qed.

Lemma mnormF_spec_mcmul : forall r c, mnorm_spec_mcmul (@mnormF r c).
Proof.
Admitted.

Lemma mnormF_spec_trig : forall r c, mnorm_spec_trig (@mnormF r c).
Proof.
Admitted.

(* ======================================================================= *)
(** ** Orthogonal matrix *)

(** Transformation by orthogonal matrix will keep normalization. *)
Lemma morth_keep_norm : forall {n} (M : smat n) (a : vec n),
    morth M -> vnorm (M *v a) = M *v vnorm a.
Proof.
  intros. unfold vnorm.
  pose proof (morth_keep_length M). unfold vlen. rewrite H0; auto.
  rewrite <- mmulv_vcmul. auto.
Qed.

(** Transformation by orthogonal matrix will keep angle. *)
Lemma morth_keep_angle : forall {n} (M : smat n) (a b : vec n),
    morth M -> (M *v a) /_ (M *v b) = a /_ b.
Proof.
  intros. unfold vangle. f_equal. rewrite !morth_keep_norm; auto.
  apply morth_keep_dot; auto.
Qed.

(** if M is orthogonal, then M&i <> vzero *)
Lemma morth_imply_col_neq0 : forall {n} (M : smat n) i, morth M -> mcol M i <> vzero.
Proof.
  intros. apply morth_iff_mcolsOrthonormal in H. destruct H as [H1 H2].
  specialize (H2 i). apply vunit_neq0; auto.
Qed.

(** if M is orthogonal, then ||M&i||=1 *)
Lemma morth_imply_vlen_col : forall {n} (M : smat n) i, morth M -> || mcol M i || = 1.
Proof.
  intros. apply morth_iff_mcolsOrthonormal in H. destruct H as [H1 H2].
  apply vlen_eq1_iff_vdot1. apply H2.
Qed.

(** if M is orthogonal, then ||M.i||=1 *)
Lemma morth_imply_vlen_row : forall {n} (M : smat n) i, morth M -> || mrow M i || = 1.
Proof.
  intros.
  apply morth_iff_mrowsOrthonormal in H. destruct H as [H1 H2].
  apply vlen_eq1_iff_vdot1. apply H2.
Qed.

(** if M is orthogonal, then <M&i, M&j> = 0 *)
Lemma morth_imply_vdot_cols_diff : forall {n} (M : smat n) i j,
    morth M -> i <> j -> <mcol M i, mcol M j> = 0.
Proof.
  intros. apply morth_iff_mcolsOrthonormal in H. destruct H as [H1 H2].
  apply H1; auto.
Qed.

(** if M is orthogonal, then M&i _|_ &j *)
Lemma morth_imply_orth_cols_diff : forall {n} (M : smat n) i j,
    morth M -> i <> j -> mcol M i _|_ mcol M j.
Proof.
  intros. apply morth_iff_mcolsOrthonormal in H. destruct H as [H1 H2].
  apply H1; auto.
Qed.

(** if M is orthogonal, then M&i /_ &j = π/2 *)
Lemma morth_imply_vangle_cols_diff : forall {n} (M : smat n) i j,
    morth M -> i <> j -> mcol M i /_ mcol M j = PI/2.
Proof.
  intros. apply vangle_PI2_iff; try apply morth_imply_col_neq0; auto.
  apply morth_imply_vdot_cols_diff; auto.
Qed.

(** if M is orthogonal, then sin (M&i /_ &j) = 1 *)
Lemma morth_imply_sin_vangle_cols_diff : forall {n} (M : smat n) i j,
    morth M -> i <> j -> sin (mcol M i /_ mcol M j) = 1.
Proof. intros. rewrite (morth_imply_vangle_cols_diff); auto. ra. Qed.

(** if M is orthogonal, then ||M&i×M&j||=1 *)
Lemma morth_imply_vlen_v3cross_cols_diff : forall (M : smat 3) i j,
    morth M -> i <> j -> || mcol M i \x mcol M j || = 1.
Proof.
  intros. rewrite vlen_v3cross; try apply morth_imply_col_neq0; auto.
  rewrite !morth_imply_vlen_col; auto.
  rewrite morth_imply_sin_vangle_cols_diff; auto. ra.
Qed.

(* SO(3)保持叉乘的一些尝试 *)
Section morth_keep_cross_try.
  (* https://en.wikipedia.org/wiki/Cross_product#Algebraic&02AProperties *)
  Notation "M \-1" := (minvAM M) : mat_scope.

  Goal forall (M : smat 3) (a b : vec 3),
      mdet M <> 0 -> (M *v a) \x (M *v b) = ((mdet M) \.* (M\-1\T *v (a \x b)))%V.
  Proof.
    intros. rewrite <- mmulv_mcmul.
    (* rewrite <- mcomat_eq; auto. *)
    (* rewrite !v3cross_eq_skew_mul_vec. *)
    (* rewrite <- !mmulv_assoc. f_equal. *)
    (* apply meq_iff_mnth; intros. *)
    (* rewrite !mnth_mmul. *)
  Abort.

  (** if M is orthogonal, then M&1×M&2 //+ M&3 *)
  Lemma morth_imply_vpara_v3cross_12 : forall (M : smat 3),
      morth M -> M&1 \x M&2 //+ M&3.
  Proof.
    intros.
    pose proof (v3cross_eq0_iff_angle_0_pi (M&1 \x M&2) (M&3)).
    assert (M&1 \x M&2 /_ M&3 = 0 \/ M&1 \x M&2 /_ M&3 = PI). admit.
    apply H0 in H1.
  Abort.

(* 其他证明思路
   https://math.stackexchange.com/questions/279173/rotational-invariance-of-cross-product *)

(* https://en.wikipedia.org/wiki/Cross_product 
   当 a = c, b = d 时，这就是叉乘直接分量形式，即
             [ î  ĵ  k̂ ]
   a×b = det [ a1 a2 a3]
             [ b1 b2 b3]
   这是 Binet–Cauchy identity 的 n = 3 的情形，需要先证明一般情形，但比较复杂。
   见 https://en.wikipedia.org/wiki/Binet%E2%80%93Cauchy_identity。
 *)
  
End morth_keep_cross_try.

(* SO(3)保持叉乘的证明 *)
Section SO3_keep_v3cross.
  (* 参考了 stackexchange, user1551 的证明思路 *)
  (* https://math.stackexchange.com/questions/2534923/does-so3-preserve-the-cross-product *)
  Open Scope vec_scope.

  (** morth(M) -> det(M) = 1 -> [Mu Mv Mw] = <Mu, M(v×w)> *)
  Lemma morth_keep_v3cross_det1_aux : forall (M : smat 3) (a b c : vec 3),
      morth M -> mdet M = 1 ->
      `[(M *v a) (M *v b) (M *v c)] = <M *v a, M *v (b \x c)>.
  Proof.
    intros.
    rewrite morth_keep_dot; auto. rewrite v3mixed_swap_op. fold (v3mixed a b c).
    rewrite !v3mixed_eq_det_cols.
    replace (@cvl2m 3 3 [M *v a; M *v b; M *v c])
      with (M * @cvl2m 3 3 [a; b; c])%M by meq.
    rewrite mdet_mmul. rewrite H0. autounfold with A. ring.
  Qed.

  (** morth(M) -> det(M) = -1 -> [Mu Mv Mw] = -<Mu, M(v×w)> *)
  Lemma morth_keep_v3cross_detNeg1_aux : forall (M : smat 3) (a b c : vec 3),
      morth M -> mdet M = (-1)%R ->
      `[(M *v a) (M *v b) (M *v c)] = (- (<M *v a, M *v (b \x c)>)%V)%R.
  Proof.
    intros.
    rewrite morth_keep_dot; auto. rewrite v3mixed_swap_op. fold (v3mixed a b c).
    rewrite !v3mixed_eq_det_cols.
    replace (@cvl2m 3 3 [M *v a; M *v b; M *v c])
      with (M * @cvl2m 3 3 [a; b; c])%M by meq.
    rewrite mdet_mmul. rewrite H0. autounfold with A. ring.
  Qed.
    
  (* orthogonal matrix keep v3cross *)
  (** morth(M) -> det(M) = 1 -> Mu × Mv = M(u×v) *)
  Lemma morth_keep_v3cross_det1 : forall (M : smat 3) (a b : vec 3),
      morth M -> mdet M = 1 -> (M *v a) \x (M *v b) = (M *v (a \x b)).
  Proof.
    intros.
    pose proof (morth_keep_v3cross_det1_aux M).
    apply vdot_cancel_l; intros.
    rewrite !v3mixed_swap_op. fold (v3mixed c (M *v a) (M *v b)).
    specialize (H1 (M\T *v c) a b H H0).
    replace (M *v (M \T *v c)) with c in H1; auto.
    rewrite <- mmulv_assoc. rewrite morth_iff_mul_trans_r in H.
    rewrite H; auto. rewrite mmulv_1_l. auto.
  Qed.

  (** SO(3) keep v3cross *)
  Corollary SO3_keep_v3cross : forall (M : smat 3) (a b : vec 3),
      SOnP M -> (M *v a) \x (M *v b) = M *v (a \x b).
  Proof. intros. hnf in H. destruct H. apply morth_keep_v3cross_det1; auto. Qed.

  (** morth(M) -> det(M) = -1 -> Ma × Mb = -M(a × b) *)
  Lemma morth_keep_v3cross_detNeg1 : forall (M : smat 3) (a b : vec 3),
      morth M -> mdet M = (-1)%R -> (M *v a) \x (M *v b) = -(M *v (a \x b)).
  Proof.
    intros.
    pose proof (morth_keep_v3cross_detNeg1_aux M).
    apply vdot_cancel_l; intros.
    rewrite !v3mixed_swap_op. fold (v3mixed c (M *v a) (M *v b)).
    specialize (H1 (M\T *v c) a b H H0).
    replace (M *v (M \T *v c)) with c in H1; auto.
    - rewrite H1. rewrite vdot_vopp_r. auto.
    - rewrite <- mmulv_assoc. rewrite morth_iff_mul_trans_r in H.
      rewrite H; auto. rewrite mmulv_1_l. auto.
  Qed.
  
  (** Cross product invariant for columns of SO(3) : M&1 × M&2 = M&3 *)
  Lemma SO3_v3cross_c12 : forall (M : smat 3), SOnP M -> M&1 \x M&2 = M&3.
  Proof.
    intros. rewrite mcol_eq_mul_v3i, mcol_eq_mul_v3j, mcol_eq_mul_v3k.
    rewrite SO3_keep_v3cross; auto. f_equal. apply v3cross_ij.
  Qed.
  
  (** Cross product invariant for columns of SO(3) : M&2 × M&3 = M&1 *)
  Lemma SO3_v3cross_c23 : forall (M : smat 3), SOnP M -> M&2 \x M&3 = M&1.
  Proof.
    intros. rewrite mcol_eq_mul_v3i, mcol_eq_mul_v3j, mcol_eq_mul_v3k.
    rewrite SO3_keep_v3cross; auto. f_equal. apply v3cross_jk.
  Qed.
  
  (** Cross product invariant for columns of SO(3) : M&3 × M&1 = M&2 *)
  Lemma SO3_v3cross_c31 : forall (M : smat 3), SOnP M -> M&3 \x M&1 = M&2.
  Proof.
    intros. rewrite mcol_eq_mul_v3i, mcol_eq_mul_v3j, mcol_eq_mul_v3k.
    rewrite SO3_keep_v3cross; auto. f_equal. apply v3cross_ki.
  Qed.

  (** Cross product invariant for rows of SO(3) : M.1 × M.2 = M.3 *)
  Lemma SO3_v3cross_r12 : forall (M : smat 3), SOnP M -> M.1 \x M.2 = M.3.
  Proof.
    intros. rewrite mrow_eq_mul_v3i, mrow_eq_mul_v3j, mrow_eq_mul_v3k.
    rewrite SO3_keep_v3cross; auto. f_equal. apply v3cross_ij.
    apply SOnP_mtrans; auto.
  Qed.
  
  (** Cross product invariant for rows of SO(3) : M.2 × M.3 = M.1 *)
  Lemma SO3_v3cross_r23 : forall (M : smat 3), SOnP M -> M.2 \x M.3 = M.1.
  Proof.
    intros. rewrite mrow_eq_mul_v3i, mrow_eq_mul_v3j, mrow_eq_mul_v3k.
    rewrite SO3_keep_v3cross; auto. f_equal. apply v3cross_jk.
    apply SOnP_mtrans; auto.
  Qed.
  
  (** Cross product invariant for rows of SO(3) : M.3 × M.1 = M.2 *)
  Lemma SO3_v3cross_r31 : forall (M : smat 3), SOnP M -> M.3 \x M.1 = M.2.
  Proof.
    intros. rewrite mrow_eq_mul_v3i, mrow_eq_mul_v3j, mrow_eq_mul_v3k.
    rewrite SO3_keep_v3cross; auto. f_equal. apply v3cross_ki.
    apply SOnP_mtrans; auto.
  Qed.

End SO3_keep_v3cross.

(* ======================================================================= *)
(** ** SO2 and SO3 *)

(** SO2 *)
Notation SO2 := (@SOn 2).

(** SO3 *)
Notation SO3 := (@SOn 3).

Example SO3_example1 : forall M : SO3, M\-1 = M\T.
Proof. apply SOn_minv_eq_trans. Qed.


(* ######################################################################### *)
(** * Modules for notations to avoid name pollution *)
Module V3Notations.
  Infix "\x" := v3cross : vec_scope.
  Notation "`| a |x" := (skew3 a) : vec_scope.
End V3Notations.


(* ######################################################################### *)
(** * Usage demo *)

(* ======================================================================= *)
(** ** Exercise in textbook *)

(** 习题8.2第12题, page 23, 高等数学，第七版 *)
(** 利用向量来证明不等式，并指出等号成立的条件 *)
Theorem Rineq3 : forall a1 a2 a3 b1 b2 b3 : R,
    sqrt (a1² + a2² + a3²) * sqrt (b1² + b2² + b3²) >= |a1*b1 + a2*b2 + a3*b3|.
Proof.
  intros.
  pose (a := mkvec3 a1 a2 a3).
  pose (b := mkvec3 b1 b2 b3).
  replace (sqrt (a1² + a2² + a3²)) with (vlen a); [|cbv; f_equal; ring].
  replace (sqrt (b1² + b2² + b3²)) with (vlen b); [|cbv; f_equal; ring].
  replace (a1 * b1 + a2 * b2 + a3 * b3)%R with (<a, b>); [|cbv; ring].
  pose proof (vdot_abs_le a b). ra.
Qed.

Section Example4CoordinateSystem.
  Variable ψ θ φ: R.
  Let Rx := (mkmat_3_3 1 0 0 0 (cos φ) (sin φ) 0 (-sin φ) (cos φ))%R.
  Let Ry := (mkmat_3_3 (cos θ) 0 (-sin θ) 0 1 0 (sin θ) 0 (cos θ))%R.
  Let Rz := (mkmat_3_3 (cos ψ) (sin ψ) 0 (-sin ψ) (cos ψ) 0 0 0 1)%R.
  Let Rbe := (mkmat_3_3
                (cos θ * cos ψ) (cos ψ * sin θ * sin φ - sin ψ * cos φ)
                (cos ψ * sin θ * cos φ + sin φ * sin ψ) (cos θ * sin ψ)
                (sin ψ * sin θ * sin φ + cos ψ * cos φ)
                (sin ψ * sin θ * cos φ - cos ψ * sin φ)
                (-sin θ) (sin φ * cos θ) (cos φ * cos θ))%R.
  Lemma Rbe_ok : (Rbe = Rz\T * Ry\T * Rx\T).
  Proof. apply m2l_inj; cbv; list_eq; lra. Qed.
    
End Example4CoordinateSystem.


(** Test for symbol matrix *)
Section Symbol_matrix.
  
  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : A.
  (* Compute m2l (minvAM1 (l2m [[a11]])). *)
  (* Compute m2l (minvAM2 (l2m [[a11;a12];[a21;a22]])). *)
  (* Compute m2l (minvAM3 (l2m [[a11;a12;a13];[a21;a22;a23];[a31;a32;a33]])). *)
End Symbol_matrix.


(** Test for symbol matrix for flight-control-system *)
Section Symbol_matrix.
  Variable θ ϕ : R.
  Notation sθ := (sin θ). Notation cθ := (cos θ).
  Notation sϕ := (sin ϕ). Notation cϕ := (cos ϕ).

  (* Given input matrix *)
  Let M : smat 3 := l2m [[1;0;-sθ];[0;cϕ;cθ*sϕ];[0;-sϕ;cθ*cϕ]]%R.

  (* A unknown inverse matrix *)
  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : A.
  Let M' : smat 3 := l2m [[a11;a12;a13];[a21;a22;a23];[a31;a32;a33]].
  
  (* Find inverse matrix *)
  Goal minvNoCheck M = M'.
  Proof.
    meq; field_simplify; autorewrite with R. 
    all:
    match goal with
    | |- ?a = ?b => idtac
    | |- ?a <> ?b => try admit
    end.
    (* now, we find a preliminary formulas: *)
    (*
  1 = a11

goal 2 (ID 4122) is:
 sϕ * sθ / cθ = a12
goal 3 (ID 4128) is:
 cϕ * sθ / cθ = a13
goal 4 (ID 4132) is:
 0 = a21
goal 5 (ID 4139) is:
 cϕ * cθ / cθ = a22
goal 6 (ID 4147) is:
 (- (cθ * sϕ / cθ))%R = a23
goal 7 (ID 4151) is:
 0 = a31
goal 8 (ID 4158) is:
 sϕ / cθ = a32
goal 9 (ID 4164) is:
 cϕ / cθ = a33
     *)
  Abort.
  
End Symbol_matrix.


(** example for symbol matrix *)
Module Exercise_Ch1_Symbol.

  (* for better readibility *)
  Notation "0" := R0.
  Notation "1" := R1.
  Notation "2" := (R1 + R1)%R.
  Notation "3" := (R1 + (R1 + R1))%R.
  Notation "4" := ((R1 + R1) * (R1 + R1))%R.
  
  Example ex6_1 : forall a b : R,
      (let m := mkmat_3_3 (a*a) (a*b) (b*b) (2*a) (a+b) (2*b) 1 1 1 in
      mdet m = (a - b)^3)%R.
  Proof. intros; cbv; lra. Qed.
  
  Example ex6_2 : forall a b x y z : R,
      (let m1 := mkmat_3_3
                   (a*x+b*y) (a*y+b*z) (a*z+b*x)
                   (a*y+b*z) (a*z+b*x) (a*x+b*y)
                   (a*z+b*x) (a*x+b*y) (a*y+b*z) in
       let m2 := mkmat_3_3 x y z y z x z x y in
       mdet m1 = (a^3 + b^3) * mdet m2)%R.
  Proof. intros; cbv; lra. Qed.
  
  Example ex6_3 : forall a b e d : A,
      (let m := mkmat_4_4
                 (a*a) ((a+1)^2) ((a+2)^2) ((a+3)^2)
                 (b*b) ((b+1)^2) ((b+2)^2) ((b+3)^2)
                 (e*e) ((e+1)^2) ((e+2)^2) ((e+3)^2)
                 (d*d) ((d+1)^2) ((d+2)^2) ((d+3)^2) in
      mdet m = 0)%R.
  Proof. intros. cbv. lra. Qed.
  
  Example ex6_4 : forall a b e d : A,
      let m := mkmat_4_4
                 1 1 1 1
                 a b e d
                 (a^2) (b^2) (e^2) (d^2)
                 (a^4) (b^4) (e^4) (d^4) in
      (mdet m = (a-b)*(a-e)*(a-d)*(b-e)*(b-d)*(e-d)*(a+b+e+d))%R.
  Proof. intros; cbv; lra. Qed.
  
  (** 6.(5), it is an infinite structure, need more work, later... *)

End Exercise_Ch1_Symbol.
