import linear_algebra.affine_space
import geometry.euclidean
import tactic.interval_cases

noncomputable theory
open_locale big_operators
open_locale classical
open_locale real

section isometry
/-!
### Euclidean isometries

This section develops properties of isometries in Euclidean space,
showing that they are affine maps that preserve the inner product.
-/

open add_action add_torsor

variables {V1 : Type*} {P1 : Type*} [inner_product_space V1] [metric_space P1]
    [S1 : euclidean_affine_space V1 P1] {V2 : Type*} {P2 : Type*} [inner_product_space V2]
    [metric_space P2] [S2 : euclidean_affine_space V2 P2]

/-- Whether a map on vectors preserves the inner product. -/
def preserves_inner (f : V1 → V2) : Prop := ∀ x y, inner (f x) (f y) = inner x y

/-- A function that preserves the inner product preserves addition. -/
lemma fn_of_add_eq_add_of_fn_of_preserves_inner {f : V1 → V2}
    (h : preserves_inner f) (x y : V1) : f (x + y) = f x + f y :=
begin
  apply eq_of_sub_eq_zero,
  rw [←inner_self_eq_zero, inner_sub_right, inner_sub_left, inner_sub_left, inner_add_right,
      inner_add_right, inner_add_left, inner_add_left, inner_add_left, h, h, h, h, h, h, h, h, h,
      inner_add_right, inner_add_right, inner_add_right, inner_add_left, inner_add_left,
      inner_comm y x],
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
  rw [vadd_assoc, neg_add_self, zero_vadd, neg_vsub_eq_vsub_rev]
end

/-- An isometry preserves the inner product. -/
lemma preserves_inner_of_isometry {f : P1 → P2} (h : isometry f) (p : P1) :
  preserves_inner (vector_map_of_point_map V1 V2 f p) :=
begin
  unfold preserves_inner,
  intros x y,
  rw [←neg_vector_map_of_point_map_of_add, inner_neg_left,
      inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
      inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two],
  unfold vector_map_of_point_map,
  rw [vadd_assoc, neg_add_self, zero_vadd, add_comm, vsub_add_vsub_cancel, ←dist_eq_norm V2,
      ←dist_eq_norm V2, ←dist_eq_norm V2, isometry.dist_eq h, isometry.dist_eq h,
      isometry.dist_eq h, dist_eq_norm V1 _ p, dist_eq_norm V1 _ (x +ᵥ p),
      dist_eq_norm V1 _ (x +ᵥ p), vadd_vsub, vsub_vadd_eq_vsub_sub, vsub_vadd_eq_vsub_sub,
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
  rw ←vsub_vadd V1 (x +ᵥ p2) p1,
  conv_rhs {
    congr,
    skip,
    rw ←vsub_vadd V1 p2 p1
  },
  rw ←vsub_sub_vsub_cancel_right V2 (f (x +ᵥ p2 -ᵥ p1 +ᵥ p1)) _ (f p1),
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
def affine_map_of_isometry {f : P1 → P2} (h : isometry f) : affine_map ℝ V1 P1 V2 P2 :=
{ to_fun := f,
  linear := linear_map_of_isometry V1 V2 h,
  map_vadd' := begin
    intros p v,
    unfold linear_map_of_isometry linear_map_of_preserves_inner,
    simp_rw vector_map_of_isometry_eq V1 V2 h _ p,
    exact (vsub_vadd V2 (f (v +ᵥ p)) (f p)).symm
  end }

end isometry

namespace inner_product_geometry

variables {V : Type*} [inner_product_space V]

/-- The cosine of the sum of two angles in a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
lemma cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  real.cos (angle x (x - y) + angle y (y - x)) = -real.cos (angle x y) :=
begin
  by_cases hxy : x = y,
  { rw [hxy, angle_self hy],
    simp },
  { rw [real.cos_add, cos_angle, cos_angle, cos_angle],
    have hxn : ∥x∥ ≠ 0 := (λ h, hx (norm_eq_zero.1 h)),
    have hyn : ∥y∥ ≠ 0 := (λ h, hy (norm_eq_zero.1 h)),
    have hxyn : ∥x - y∥ ≠ 0 := (λ h, hxy (eq_of_sub_eq_zero (norm_eq_zero.1 h))),
    apply mul_right_cancel' hxn,
    apply mul_right_cancel' hyn,
    apply mul_right_cancel' hxyn,
    apply mul_right_cancel' hxyn,
    rw [mul_sub_right_distrib, mul_sub_right_distrib, mul_sub_right_distrib,
        mul_sub_right_distrib,
        (show real.sin (angle x (x - y)) * real.sin (angle y (y - x)) *
                ∥x∥ * ∥y∥ * ∥x - y∥ * ∥x - y∥ =
              (real.sin (angle x (x - y)) * (∥x∥ * ∥x - y∥)) *
                (real.sin (angle y (y - x)) * (∥y∥ * ∥x - y∥)), by ring),
        sin_angle_mul_norm_mul_norm, norm_sub_rev x y, sin_angle_mul_norm_mul_norm,
        norm_sub_rev y x, inner_sub_left, inner_sub_left, inner_sub_right, inner_sub_right,
        inner_sub_right, inner_sub_right, inner_comm y x,
        (show inner x x * (inner x x - inner x y - (inner x y - inner y y)) -
                (inner x x - inner x y) * (inner x x - inner x y) =
              inner x x * inner y y - inner x y * inner x y, by ring),
        (show inner y y * (inner y y - inner x y - (inner x y - inner x x)) -
                (inner y y - inner x y) * (inner y y - inner x y) =
              inner x x * inner y y - inner x y * inner x y, by ring),
        real.mul_self_sqrt (sub_nonneg_of_le (inner_mul_inner_self_le x y)),
        inner_self_eq_norm_square, inner_self_eq_norm_square,
        inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two],
    field_simp [hxn, hyn, hxyn],
    ring }
end

/-- The sine of the sum of two angles in a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
lemma sin_angle_sub_add_angle_sub_rev_eq_sin_angle {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  real.sin (angle x (x - y) + angle y (y - x)) = real.sin (angle x y) :=
begin
  by_cases hxy : x = y,
  { rw [hxy, angle_self hy],
    simp },
  { rw [real.sin_add, cos_angle, cos_angle],
    have hxn : ∥x∥ ≠ 0 := (λ h, hx (norm_eq_zero.1 h)),
    have hyn : ∥y∥ ≠ 0 := (λ h, hy (norm_eq_zero.1 h)),
    have hxyn : ∥x - y∥ ≠ 0 := (λ h, hxy (eq_of_sub_eq_zero (norm_eq_zero.1 h))),
    apply mul_right_cancel' hxn,
    apply mul_right_cancel' hyn,
    apply mul_right_cancel' hxyn,
    apply mul_right_cancel' hxyn,
    rw [right_distrib, right_distrib, right_distrib, right_distrib,
        (show real.sin (angle x (x - y)) * (inner y (y - x) / (∥y∥ * ∥y - x∥)) * ∥x∥ * ∥y∥ * ∥x - y∥ =
                real.sin (angle x (x - y)) * (∥x∥ * ∥x - y∥) *
                  (inner y (y - x) / (∥y∥ * ∥y - x∥)) * ∥y∥, by ring),
        sin_angle_mul_norm_mul_norm, norm_sub_rev x y,
        (show inner x (x - y) / (∥x∥ * ∥y - x∥) * real.sin (angle y (y - x)) * ∥x∥ * ∥y∥ * ∥y - x∥ =
                inner x (x - y) / (∥x∥ * ∥y - x∥) *
                  (real.sin (angle y (y - x)) * (∥y∥ * ∥y - x∥)) * ∥x∥, by ring),
        sin_angle_mul_norm_mul_norm, norm_sub_rev y x, mul_assoc (real.sin (angle x y)),
        sin_angle_mul_norm_mul_norm, inner_sub_left, inner_sub_left, inner_sub_right,
        inner_sub_right, inner_sub_right, inner_sub_right, inner_comm y x,
        (show inner x x * (inner x x - inner x y - (inner x y - inner y y)) -
                (inner x x - inner x y) * (inner x x - inner x y) =
              inner x x * inner y y - inner x y * inner x y, by ring),
        (show inner y y * (inner y y - inner x y - (inner x y - inner x x)) -
                (inner y y - inner x y) * (inner y y - inner x y) =
              inner x x * inner y y - inner x y * inner x y, by ring),
        inner_self_eq_norm_square, inner_self_eq_norm_square,
        inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two],
    field_simp [hxn, hyn, hxyn],
    ring }
end

/-- The cosine of the sum of the angles of a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
lemma cos_angle_add_angle_sub_add_angle_sub_eq_neg_one {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  real.cos (angle x y + angle x (x - y) + angle y (y - x)) = -1 :=
by rw [add_assoc, real.cos_add, cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle hx hy,
       sin_angle_sub_add_angle_sub_rev_eq_sin_angle hx hy, ←neg_mul_eq_mul_neg, ←neg_add',
       add_comm, ←pow_two, ←pow_two, real.sin_sq_add_cos_sq]

/-- The sine of the sum of the angles of a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
lemma sin_angle_add_angle_sub_add_angle_sub_eq_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  real.sin (angle x y + angle x (x - y) + angle y (y - x)) = 0 :=
begin
  rw [add_assoc, real.sin_add, cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle hx hy,
      sin_angle_sub_add_angle_sub_rev_eq_sin_angle hx hy],
  ring
end

/-- The sum of the angles of a possibly degenerate triangle (where the
two given sides are nonzero), vector angle form. -/
lemma angle_add_angle_sub_add_angle_sub_eq_pi {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  angle x y + angle x (x - y) + angle y (y - x) = π :=
begin
  have hcos := cos_angle_add_angle_sub_add_angle_sub_eq_neg_one hx hy,
  have hsin := sin_angle_add_angle_sub_add_angle_sub_eq_zero hx hy,
  rw real.sin_eq_zero_iff at hsin,
  cases hsin with n hn,
  symmetry' at hn,
  have h0 : 0 ≤ angle x y + angle x (x - y) + angle y (y - x) :=
    add_nonneg (add_nonneg (angle_nonneg _ _) (angle_nonneg _ _)) (angle_nonneg _ _),
  have h3 : angle x y + angle x (x - y) + angle y (y - x) ≤ π + π + π :=
    add_le_add (add_le_add (angle_le_pi _ _) (angle_le_pi _ _)) (angle_le_pi _ _),
  have h3lt : angle x y + angle x (x - y) + angle y (y - x) < π + π + π,
  { by_contradiction hnlt,
    have hxy : angle x y = π,
    { by_contradiction hxy,
      exact hnlt (add_lt_add_of_lt_of_le (add_lt_add_of_lt_of_le
                                           (lt_of_le_of_ne (angle_le_pi _ _) hxy)
                                         (angle_le_pi _ _)) (angle_le_pi _ _)) },
    rw hxy at hnlt,
    rw angle_eq_pi_iff at hxy,
    rcases hxy with ⟨hx, ⟨r, ⟨hr, hxr⟩⟩⟩,
    rw [hxr, ←one_smul ℝ x, ←mul_smul, mul_one, ←sub_smul, one_smul, sub_eq_add_neg,
        angle_smul_right_of_pos _ _ (add_pos' zero_lt_one (neg_pos_of_neg hr)), angle_self hx,
        add_zero] at hnlt,
    apply hnlt,
    rw add_assoc,
    exact add_lt_add_left (lt_of_le_of_lt (angle_le_pi _ _)
                                          (lt_add_of_pos_right π real.pi_pos)) _ },
  have hn0 : 0 ≤ n,
  { rw [hn, mul_nonneg_iff_right_nonneg_of_pos real.pi_pos] at h0,
    norm_cast at h0,
    exact h0 },
  have hn3 : n < 3,
  { rw [hn, (show π + π + π = 3 * π, by ring)] at h3lt,
    replace h3lt := lt_of_mul_lt_mul_right h3lt (le_of_lt real.pi_pos),
    norm_cast at h3lt,
    exact h3lt },
  interval_cases n,
  { rw hn at hcos,
    simp at hcos,
    norm_num at hcos },
  { rw hn,
    norm_num },
  { rw hn at hcos,
    simp at hcos,
    norm_num at hcos },
end

end inner_product_geometry

namespace euclidean_geometry

open add_torsor inner_product_geometry
open_locale euclidean_geometry

variables (V : Type*) {P : Type*} [inner_product_space V] [metric_space P]
    [euclidean_affine_space V P]
include V

/-- The sum of the angles of a possibly degenerate triangle (where the
given vertex is distinct from the others), angle-at-point. -/
lemma angle_add_angle_add_angle_eq_pi {p1 p2 p3 : P} (h2 : p2 ≠ p1) (h3 : p3 ≠ p1) :
  ∠ V p1 p2 p3 + ∠ V p2 p3 p1 + ∠ V p3 p1 p2 = π :=
begin
  rw [add_assoc, add_comm, add_comm (∠ V p2 p3 p1), angle_comm V p2 p3 p1],
  unfold angle,
  rw [←angle_neg_neg (p1 -ᵥ p3), ←angle_neg_neg (p1 -ᵥ p2), neg_vsub_eq_vsub_rev,
      neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev,
      ←vsub_sub_vsub_cancel_right V p3 p2 p1, ←vsub_sub_vsub_cancel_right V p2 p3 p1],
  exact angle_add_angle_sub_add_angle_sub_eq_pi (λ he, h3 ((vsub_eq_zero_iff_eq V).1 he))
                                                (λ he, h2 ((vsub_eq_zero_iff_eq V).1 he))
end

end euclidean_geometry
