import geometry.euclidean

noncomputable theory
open_locale classical
open_locale real
open_locale real_inner_product_space

section isometry
/-!
### Euclidean isometries

This section develops properties of isometries in Euclidean space,
showing that they are affine maps that preserve the inner product.
-/

variables {V1 : Type*} {P1 : Type*} [inner_product_space ℝ V1] [metric_space P1]
    [S1 : normed_add_torsor V1 P1] {V2 : Type*} {P2 : Type*} [inner_product_space ℝ V2]
    [metric_space P2] [S2 : normed_add_torsor V2 P2]

/-- Whether a map on vectors preserves the inner product. -/
def preserves_inner (f : V1 → V2) : Prop := ∀ x y, ⟪(f x), (f y)⟫ = ⟪x, y⟫

/-- A function that preserves the inner product preserves addition. -/
lemma fn_of_add_eq_add_of_fn_of_preserves_inner {f : V1 → V2}
    (h : preserves_inner f) (x y : V1) : f (x + y) = f x + f y :=
begin
  apply eq_of_sub_eq_zero,
  rw [←inner_self_eq_zero, inner_sub_right, inner_sub_left, inner_sub_left, inner_add_right,
      inner_add_right, inner_add_left, inner_add_left, inner_add_left, h, h, h, h, h, h, h, h, h,
      inner_add_right, inner_add_right, inner_add_right, inner_add_left, inner_add_left,
      real_inner_comm y x],
  ring
end

/-- A function that preserves the inner product preserves scalar
multiplication. -/
lemma fn_of_smul_eq_smul_of_fn_of_preserves_inner {f : V1 → V2}
    (h : preserves_inner f) (r : ℝ) (x : V1) : f (r • x) = r • f x :=
begin
  apply eq_of_sub_eq_zero,
  rw [←inner_self_eq_zero, inner_sub_right, inner_sub_left, inner_sub_left, inner_smul_right,
      inner_smul_right, inner_smul_left, inner_smul_left, h, h, h, h, inner_smul_right,
      inner_smul_right, inner_smul_left],
  ring
end

/-- A function that preserves the inner product is a linear map. -/
def linear_map_of_preserves_inner {f : V1 → V2} (h : preserves_inner f) :
  linear_map ℝ V1 V2 :=
{ to_fun := f,
  map_add' := fn_of_add_eq_add_of_fn_of_preserves_inner h,
  map_smul' := fn_of_smul_eq_smul_of_fn_of_preserves_inner h }

variables (V1) (V2)
include S1 S2

/-- The map on vectors corresponding to a map from P1 to P2, at a base
point p. -/
def vector_map_of_point_map (f : P1 → P2) (p : P1) : V1 → V2 := λ v, f (v +ᵥ p) -ᵥ f p

/-- Applying the map on vectors at the result of adding a vector. -/
lemma neg_vector_map_of_point_map_of_add (f : P1 → P2) (p : P1) (v : V1) :
  -vector_map_of_point_map V1 V2 f (v +ᵥ p) (-v) = vector_map_of_point_map V1 V2 f p v :=
begin
  unfold vector_map_of_point_map,
  rw [←add_vadd, neg_add_self, zero_vadd, neg_vsub_eq_vsub_rev]
end

/-- An isometry preserves the inner product. -/
lemma preserves_inner_of_isometry {f : P1 → P2} (h : isometry f) (p : P1) :
  preserves_inner (vector_map_of_point_map V1 V2 f p) :=
begin
  unfold preserves_inner,
  intros x y,
  rw [←neg_vector_map_of_point_map_of_add, inner_neg_left,
      real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
      real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two],
  unfold vector_map_of_point_map,
  rw [←add_vadd, neg_add_self, zero_vadd, add_comm, vsub_add_vsub_cancel, ←dist_eq_norm_vsub V2,
      ←dist_eq_norm_vsub V2, ←dist_eq_norm_vsub V2, isometry.dist_eq h, isometry.dist_eq h,
      isometry.dist_eq h, dist_eq_norm_vsub V1 _ p, dist_eq_norm_vsub V1 _ (x +ᵥ p),
      dist_eq_norm_vsub V1 _ (x +ᵥ p), vadd_vsub, vsub_vadd_eq_vsub_sub, vsub_vadd_eq_vsub_sub,
      vsub_self, vadd_vsub, zero_sub, norm_neg, norm_sub_rev],
  ring
end

/-- An isometry induces the same map on vectors with any base
point. -/
lemma vector_map_of_isometry_eq {f : P1 → P2} (h : isometry f) (p1 p2 : P1) :
  vector_map_of_point_map V1 V2 f p1 = vector_map_of_point_map V1 V2 f p2 :=
begin
  ext x,
  unfold vector_map_of_point_map,
  rw ←vsub_vadd (x +ᵥ p2) p1,
  conv_rhs {
    congr,
    skip,
    rw ←vsub_vadd p2 p1
  },
  rw ←vsub_sub_vsub_cancel_right (f (x +ᵥ p2 -ᵥ p1 +ᵥ p1)) _ (f p1),
  change vector_map_of_point_map V1 V2 f p1 x =
    vector_map_of_point_map V1 V2 f p1 (x +ᵥ p2 -ᵥ p1) -
      vector_map_of_point_map V1 V2 f p1 (p2 -ᵥ p1),
  apply eq_sub_of_add_eq,
  symmetry,
  rw vadd_vsub_assoc,
  exact fn_of_add_eq_add_of_fn_of_preserves_inner (preserves_inner_of_isometry V1 V2 h p1) _ _
end

/-- The map on vectors corresponding to a map from P1 to P2, for an
isometry. -/
def vector_map_of_isometry {f : P1 → P2} (h : isometry f) : V1 → V2 :=
vector_map_of_point_map V1 V2 f (classical.choice S1.nonempty)

/-- The linear map on vectors corresponding to a map from P1 to P2,
for an isometry. -/
def linear_map_of_isometry {f : P1 → P2} (h : isometry f) : linear_map ℝ V1 V2 :=
linear_map_of_preserves_inner (preserves_inner_of_isometry V1 V2 h (classical.choice S1.nonempty))

/-- An isometry is an affine map. -/
def affine_map_of_isometry {f : P1 → P2} (h : isometry f) : affine_map ℝ P1 P2 :=
{ to_fun := f,
  linear := linear_map_of_isometry V1 V2 h,
  map_vadd' := begin
    intros p v,
    unfold linear_map_of_isometry linear_map_of_preserves_inner,
    simp_rw vector_map_of_isometry_eq V1 V2 h _ p,
    exact (vsub_vadd (f (v +ᵥ p)) (f p)).symm
  end }

end isometry
