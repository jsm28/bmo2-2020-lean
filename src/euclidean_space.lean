import algebra.big_operators
import analysis.normed_space.real_inner_product
import affine_space

noncomputable theory
open_locale big_operators

/-!
# Euclidean spaces

This file defines Euclidean affine spaces.

## Implementation notes

Rather than requiring Euclidean affine spaces to be finite-dimensional
(as in the definition on Wikipedia), this is specified only for those
theorems that need it.

## References

* https://en.wikipedia.org/wiki/Euclidean_space

-/

/-- A `euclidean_affine_space V P` is an affine space with points `P`
over an `inner_product_space V`. We bundle the distance and require
it to be the same as results from the inner product. -/
class euclidean_affine_space (V : Type*) (P : Type*) [inner_product_space V] [nonempty P]
    [has_dist P] extends affine_space V P :=
(dist_eq_norm_vsub : ∀ (x y : P), dist x y = ∥(x -ᵥ y : V)∥)

/-- The distance equals the norm of subtracting two points. This lemma
is needed to make V an explicit rather than implicit argument. -/
lemma euclidean_dist (V : Type*) {P : Type*} [inner_product_space V]
    [nonempty P] [has_dist P] [euclidean_affine_space V P] (x y : P) :
  dist x y = ∥(x -ᵥ y : V)∥ :=
euclidean_affine_space.dist_eq_norm_vsub x y

/-- The standard Euclidean space, fin n → ℝ. -/
instance standard_euclidean_space_is_vector_space (n : ℕ) : vector_space ℝ (fin n → ℝ) :=
by apply_instance
instance standard_euclidean_space_has_inner (n : ℕ) : has_inner (fin n → ℝ) :=
{ inner := λ a b, ∑ i, a i * b i }
instance standard_euclidean_space_is_inner_product_space (n : ℕ) :
  inner_product_space (fin n → ℝ) :=
{ comm := begin
    intros x y,
    unfold inner,
    conv_lhs {
      congr,
      skip,
      funext,
      rw mul_comm
    }
  end,
  nonneg := begin
    intro x,
    unfold inner,
    exact finset.sum_nonneg (λ i hi, mul_self_nonneg _)
  end,
  definite := begin
    intro x,
    unfold inner,
    intro h,
    rw finset.sum_eq_zero_iff_of_nonneg at h,
    { ext i,
      replace h := h i (finset.mem_univ _),
      change x i = 0,
      rwa [mul_eq_zero_iff', or_self] at h },
    { exact λ i hi, mul_self_nonneg _ }
  end,
  add_left := begin
    intros x y z,
    unfold inner,
    convert finset.sum_add_distrib,
    conv_lhs {
      funext,
      rw [(show (x + y) i = x i + y i, by refl), right_distrib]
    }
  end,
  smul_left := begin
    intros x y r,
    unfold inner,
    rw finset.mul_sum,
    conv_lhs {
      funext,
      congr,
      skip,
      funext,
      rw [(show (r • x) i = r * x i, by refl), mul_assoc]
    }
  end }
instance standard_euclidean_affine_space_has_dist (n : ℕ) : has_dist (fin n → ℝ) :=
{ dist := λ x y, ∥x - y∥ }
instance standard_euclidean_affine_space (n : ℕ) :
  euclidean_affine_space (fin n → ℝ) (fin n → ℝ) :=
{ dist_eq_norm_vsub := λ x y, rfl }

section real_inner_product
/-!
### Geometrical results on real inner product spaces

This section develops some geometrical definitions and results on real
inner product spaces, where those definitions and results can most
conveniently be developed in terms of vectors and then used to deduce
corresponding results for Euclidean affine spaces.
-/

variables {V : Type*} [inner_product_space V]

/-- The inner product of two vectors, divided by the product of their
norms, has absolute value at most 1. -/
lemma abs_inner_div_norm_mul_norm_le_one (x y : V) : abs (inner x y / (∥x∥ * ∥y∥)) ≤ 1 :=
begin
  rw [abs_div],
  by_cases h : 0 = abs (∥x∥ * ∥y∥),
  { rw [←h, div_zero],
    norm_num },
  { apply div_le_of_le_mul (lt_of_le_of_ne (ge_iff_le.mp (abs_nonneg (∥x∥ * ∥y∥))) h),
    convert abs_inner_le_norm x y using 1,
    rw [abs_mul, abs_of_nonneg (norm_nonneg x), abs_of_nonneg (norm_nonneg y), mul_one] }
end

/-- The undirected angle between two vectors. -/
def angle_of_vectors (x y : V) : ℝ := (inner x y / (∥x∥ * ∥y∥)).arccos

/-- The angle between two vectors is nonnegative. -/
lemma angle_of_vectors_nonneg (x y : V) : 0 ≤ angle_of_vectors x y :=
real.arccos_nonneg _

/-- The angle between two vectors is at most π. -/
lemma angle_of_vectors_le_pi (x y : V) : angle_of_vectors x y ≤ real.pi :=
real.arccos_le_pi _

/-- The angle between a vector and the negation of another vector. -/
lemma angle_of_vectors_of_neg (x y : V) :
  angle_of_vectors x (-y) = real.pi - angle_of_vectors x y :=
begin
  unfold angle_of_vectors,
  rw ←real.arccos_neg,
  congr,
  rw [norm_neg, inner_neg_right, neg_div]
end

/-- The cosine of the angle between two vectors. -/
lemma cos_angle_of_vectors (x y : V) :
  (angle_of_vectors x y).cos = inner x y / (∥x∥ * ∥y∥) :=
real.cos_arccos (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).1
                (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).2

/-- The cosine of the angle between two vectors, multiplied by the
product of their norms. -/
lemma cos_angle_of_vectors_mul_norm_mul_norm (x y : V) :
  (angle_of_vectors x y).cos * (∥x∥ * ∥y∥) = inner x y :=
begin
  rw cos_angle_of_vectors,
  by_cases h : (∥x∥ * ∥y∥) = 0,
  { rw [h, mul_zero],
    cases eq_zero_or_eq_zero_of_mul_eq_zero h with hx hy,
    { rw norm_eq_zero at hx,
      rw [hx, inner_zero_left] },
    { rw norm_eq_zero at hy,
      rw [hy, inner_zero_right] } },
  { exact div_mul_cancel _ h }
end

/-- Two vectors have inner product 0 if and only if the angle between
them is π/2. -/
lemma inner_eq_zero_iff_angle_eq_pi_div_two (x y : V) :
  inner x y = 0 ↔ angle_of_vectors x y = real.pi / 2 :=
begin
  split,
  { intro h,
    unfold angle_of_vectors,
    rw [h, zero_div, real.arccos_zero] },
  { intro h,
    unfold angle_of_vectors at h,
    rw ←real.arccos_zero at h,
    have h2 : inner x y / (∥x∥ * ∥y∥) = 0 :=
      real.arccos_inj (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).1
                      (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).2
                      (by norm_num)
                      (by norm_num)
                      h,
    by_cases h : (∥x∥ * ∥y∥) = 0,
    { cases eq_zero_or_eq_zero_of_mul_eq_zero h with hx hy,
      { rw norm_eq_zero at hx,
        rw [hx, inner_zero_left] },
      { rw norm_eq_zero at hy,
        rw [hy, inner_zero_right] } },
    { rwa div_eq_zero_iff h at h2 } },
end

/-- Pythagorean theorem, if-and-only-if vector inner product form. -/
lemma norm_add_square_eq_norm_square_add_norm_square_iff_inner_eq_zero (x y : V) :
  ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ ↔ inner x y = 0 :=
begin
  rw [norm_add_mul_self, add_right_cancel_iff, add_right_eq_self, mul_eq_zero],
  norm_num
end

/-- Pythagorean theorem, subtracting vectors, if-and-only-if vector
inner product form. -/
lemma norm_sub_square_eq_norm_square_add_norm_square_iff_inner_eq_zero (x y : V) :
  ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ ↔ inner x y = 0 :=
begin
  rw [norm_sub_mul_self, add_right_cancel_iff, sub_eq_add_neg, add_right_eq_self, neg_eq_zero,
      mul_eq_zero],
  norm_num
end

/-- Pythagorean theorem, if-and-only-if vector angle form. -/
lemma norm_add_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two (x y : V) :
  ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ ↔ angle_of_vectors x y = real.pi / 2 :=
begin
  rw norm_add_square_eq_norm_square_add_norm_square_iff_inner_eq_zero,
  exact inner_eq_zero_iff_angle_eq_pi_div_two x y
end

/-- Pythagorean theorem, subtracting vectors, if-and-only-if vector angle form. -/
lemma norm_sub_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two (x y : V) :
  ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ ↔ angle_of_vectors x y = real.pi / 2 :=
begin
  rw norm_sub_square_eq_norm_square_add_norm_square_iff_inner_eq_zero,
  exact inner_eq_zero_iff_angle_eq_pi_div_two x y
end

end real_inner_product

section euclidean

variables (V : Type*) {P : Type*} [inner_product_space V] [nonempty P] [has_dist P]
    [euclidean_affine_space V P]
include V

/-- If the underlying vector space is a normed space, this defines a
metric space structure on the affine space. -/
instance euclidean_affine_space_is_metric_space : metric_space P :=
{ dist_self := begin
    intro p,
    rw euclidean_dist V p p,
    rw [affine_space.vsub_self V p, norm_zero]
  end,
  eq_of_dist_eq_zero := begin
    intros p1 p2 h,
    rw euclidean_dist V p1 p2 at h,
    rw norm_eq_zero at h,
    exact affine_space.eq_of_vsub_eq_zero V h
  end,
  dist_comm := begin
    intros x y,
    rw [euclidean_dist V x y, euclidean_dist V y x],
    convert norm_neg (y -ᵥ x),
    exact affine_space.vsub_rev_eq_neg_vsub V y x
  end,
  dist_triangle := begin
    intros x y z,
    rw [euclidean_dist V x y, euclidean_dist V y z, euclidean_dist V x z],
    rw ←affine_space.add_vsub_vsub_cancel V x y z,
    apply norm_add_le
  end }

/-- The undirected angle at `p2` between the line segments to `p1` and
`p3`. -/
def angle_of_points (p1 p2 p3 : P) : ℝ := angle_of_vectors (p1 -ᵥ p2 : V) (p3 -ᵥ p2)

notation `∠` := angle_of_points

/-- The angle at a point is nonnegative. -/
lemma angle_of_points_nonneg (p1 p2 p3 : P) : 0 ≤ ∠ V p1 p2 p3 :=
angle_of_vectors_nonneg _ _

/-- The angle at a point is at most π. -/
lemma angle_of_points_le_pi (p1 p2 p3 : P) : ∠ V p1 p2 p3 ≤ real.pi :=
angle_of_vectors_le_pi _ _

/-- Pythagorean theorem, if-and-only-if angle-at-point form. -/
lemma dist_square_eq_dist_square_add_dist_square_iff_angle_eq_pi_div_two (p1 p2 p3 : P) :
  dist p1 p3 * dist p1 p3 = dist p1 p2 * dist p1 p2 + dist p3 p2 * dist p3 p2 ↔
    ∠ V p1 p2 p3 = real.pi / 2 :=
by erw [metric_space.dist_comm p3 p2, euclidean_dist V p1 p3, euclidean_dist V p1 p2,
        euclidean_dist V p2 p3,
        ←norm_sub_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two,
        affine_space.sub_vsub_vsub_cancel V p1, affine_space.vsub_rev_eq_neg_vsub V p2 p3,
        norm_neg]

end euclidean
