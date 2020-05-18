import algebra.big_operators
import analysis.normed_space.real_inner_product
import normed_add_comm_torsor

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
over an `inner_product_space V`. -/
class euclidean_affine_space (V : Type*) (P : Type*) [inner_product_space V] [nonempty P]
    [has_dist P] extends normed_add_comm_torsor V P

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

/-- The undirected angle between two vectors. If either vector is 0,
this is π/2. -/
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

/-- Law of cosines (cosine rule), vector angle form. -/
lemma norm_sub_square_eq_norm_square_add_norm_square_sub_two_mul_norm_mul_norm_mul_angle
    (x y : V) :
  ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ - 2 * ∥x∥ * ∥y∥ * (angle_of_vectors x y).cos :=
begin
  rw [(show 2 * ∥x∥ * ∥y∥ * (angle_of_vectors x y).cos =
            2 * ((angle_of_vectors x y).cos * (∥x∥ * ∥y∥)), by ring),
      cos_angle_of_vectors_mul_norm_mul_norm, ←inner_self_eq_norm_square,
      ←inner_self_eq_norm_square, ←inner_self_eq_norm_square, inner_sub_left, inner_sub_right,
      inner_sub_right, inner_comm y x],
  ring
end

/-- Pons asinorum, vector angle form. -/
lemma angle_sub_eq_angle_sub_rev_of_norm_eq (x y : V) (h : ∥x∥ = ∥y∥) :
  angle_of_vectors x (x - y) = angle_of_vectors y (y - x) :=
begin
  refine real.cos_inj_of_nonneg_of_le_pi (angle_of_vectors_nonneg _ _)
                                         (angle_of_vectors_le_pi _ _)
                                         (angle_of_vectors_nonneg _ _)
                                         (angle_of_vectors_le_pi _ _) _,
  rw [cos_angle_of_vectors, cos_angle_of_vectors, h, ←neg_sub, norm_neg, neg_sub,
      inner_sub_right, inner_sub_right, inner_self_eq_norm_square, inner_self_eq_norm_square, h,
      inner_comm x y]
end

end real_inner_product

section euclidean

variables (V : Type*) {P : Type*} [inner_product_space V] [nonempty P] [has_dist P]
    [euclidean_affine_space V P]
include V

/-- The undirected angle at `p2` between the line segments to `p1` and
`p3`. If either of those points equals `p2`, this is π/2. -/
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
by erw [metric_space.dist_comm p3 p2, norm_dist V p1 p3, norm_dist V p1 p2, norm_dist V p2 p3,
        ←norm_sub_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two,
        add_comm_torsor.sub_vsub_vsub_cancel_right V p1,
        add_comm_torsor.vsub_rev_eq_neg_vsub V p2 p3, norm_neg]

/-- Law of cosines (cosine rule), angle-at-point form. -/
lemma dist_square_eq_dist_square_add_dist_square_sub_two_mul_dist_mul_dist_mul_angle
    (p1 p2 p3 : P) :
  dist p1 p3 * dist p1 p3 = dist p1 p2 * dist p1 p2 + dist p3 p2 * dist p3 p2 - 2 * dist p1 p2 * dist p3 p2 * (∠ V p1 p2 p3).cos :=
begin
  rw [norm_dist V p1 p3, norm_dist V p1 p2, norm_dist V p3 p2],
  unfold angle_of_points,
  convert norm_sub_square_eq_norm_square_add_norm_square_sub_two_mul_norm_mul_norm_mul_angle
          (p1 -ᵥ p2 : V) (p3 -ᵥ p2 : V),
  { exact (add_comm_torsor.sub_vsub_vsub_cancel_right V p1 p3 p2).symm },
  { exact (add_comm_torsor.sub_vsub_vsub_cancel_right V p1 p3 p2).symm }
end

/-- Pons asinorum, angle-at-point form. -/
lemma angle_eq_angle_of_dist_eq (p1 p2 p3 : P) (h : dist p1 p2 = dist p1 p3) :
  ∠ V p1 p2 p3 = ∠ V p1 p3 p2 :=
begin
  rw [norm_dist V p1 p2, norm_dist V p1 p3] at h,
  unfold angle_of_points,
  convert angle_sub_eq_angle_sub_rev_of_norm_eq (p1 -ᵥ p2 : V) (p1 -ᵥ p3 : V) h,
  { exact (add_comm_torsor.sub_vsub_vsub_cancel_left V p3 p2 p1).symm },
  { exact (add_comm_torsor.sub_vsub_vsub_cancel_left V p2 p3 p1).symm }
end

end euclidean
