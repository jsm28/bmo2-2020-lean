import algebra.big_operators
import analysis.normed_space.real_inner_product
import affine_space

noncomputable theory
open_locale big_operators

/-!
# Euclidean spaces

This file defines Euclidean vector spaces and affine spaces.

## References

* https://en.wikipedia.org/wiki/Euclidean_space

-/

/-- A `euclidean_vector_space V` is a finite-dimensional real inner
product space structure on the vectors `V`. -/
class euclidean_vector_space (V : Type*) [inner_product_space V] [finite_dimensional ℝ V]

/-- A `euclidean_affine_space V P` is an affine space with points `P`
over a `euclidean_vector_space V` -/
class euclidean_affine_space (V : Type*) (P : Type*) [inner_product_space V]
    [finite_dimensional ℝ V] [euclidean_vector_space V] [nonempty P] [has_vadd V P]
    [affine_space ℝ V P]

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
instance standard_euclidean_space_finite_dimensional (n : ℕ) :
  finite_dimensional ℝ (fin n → ℝ) :=
by apply_instance
instance standard_euclidean_vector_space (n : ℕ) : euclidean_vector_space (fin n → ℝ) :=
⟨⟩
instance standard_euclidean_affine_space (n : ℕ) :
  euclidean_affine_space (fin n → ℝ) (fin n → ℝ) :=
⟨⟩

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

/-- Pythagorean theorem, if-and-only-if vector angle form. -/
lemma norm_add_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two (x y : V) :
  ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ ↔ angle_of_vectors x y = real.pi / 2 :=
begin
  rw norm_add_square_eq_norm_square_add_norm_square_iff_inner_eq_zero,
  exact inner_eq_zero_iff_angle_eq_pi_div_two x y
end

end real_inner_product

section euclidean

variables (V : Type*) {P : Type*} [inner_product_space V]
    [finite_dimensional ℝ V] [euclidean_vector_space V] [nonempty P] [has_vadd V P]
    [affine_space ℝ V P] [euclidean_affine_space V P]

/-- The undirected angle at `p2` between the line segments to `p1` and
`p3`. -/
def angle_of_points (p1 p2 p3 : P) : ℝ := angle_of_vectors (p2 -ᵥ p1 : V) (p3 -ᵥ p1)

notation `∠` := angle_of_points

/-- The angle at a point is nonnegative. -/
lemma angle_of_points_nonneg (p1 p2 p3 : P) : 0 ≤ ∠ V p1 p2 p3 :=
angle_of_vectors_nonneg _ _

/-- The angle at a point is at most π. -/
lemma angle_of_points_le_pi (p1 p2 p3 : P) : ∠ V p1 p2 p3 ≤ real.pi :=
angle_of_vectors_le_pi _ _

end euclidean
