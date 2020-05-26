import algebra.big_operators
import analysis.normed_space.real_inner_product
import affine_space
import normed_add_torsor
import tactic.apply_fun

noncomputable theory
open_locale big_operators
open_locale classical

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
class euclidean_affine_space (V : Type*) (P : Type*) [inner_product_space V] [metric_space P]
  extends normed_add_torsor V P

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
instance standard_euclidean_affine_space_normed_group (n : ℕ) : normed_group (fin n → ℝ) :=
inner_product_space_is_normed_group
instance standard_euclidean_affine_space_metric_space (n : ℕ) : metric_space (fin n → ℝ) :=
normed_group.to_metric_space
instance standard_euclidean_affine_space (n : ℕ) :
  euclidean_affine_space (fin n → ℝ) (fin n → ℝ) :=
{ norm_dist' := normed_group.dist_eq }

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

/-- The inner product of a vector with a multiple of itself. -/
lemma inner_smul_self_left (x : V) (r : ℝ) : inner (r • x) x = r * (∥x∥ * ∥x∥) :=
by rw [inner_smul_left, ←inner_self_eq_norm_square]

/-- The inner product of a vector with a multiple of itself. -/
lemma inner_smul_self_right (x : V) (r : ℝ) : inner x (r • x) = r * (∥x∥ * ∥x∥) :=
by rw [inner_smul_right, ←inner_self_eq_norm_square]

/-- The inner product of a nonzero vector with a nonzero multiple of
itself, divided by the product of their norms, has absolute value
1. -/
lemma abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul
  (x : V) (r : ℝ) (hx : x ≠ 0) (hr : r ≠ 0) : abs (inner x (r • x) / (∥x∥ * ∥r • x∥)) = 1 :=
begin
  rw [inner_smul_self_right, norm_smul, real.norm_eq_abs, ←mul_assoc ∥x∥, mul_comm _ (abs r),
      mul_assoc, abs_div, abs_mul r, abs_mul (abs r), abs_abs, div_self],
  exact mul_ne_zero (λ h, hr (eq_zero_of_abs_eq_zero h))
    (λ h, hx (norm_eq_zero.1 (eq_zero_of_mul_self_eq_zero (eq_zero_of_abs_eq_zero h))))
end

/-- The inner product of a nonzero vector with a positive multiple of
itself, divided by the product of their norms, has value 1. -/
lemma inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul
  (x : V) (r : ℝ) (hx : x ≠ 0) (hr : 0 < r) : inner x (r • x) / (∥x∥ * ∥r • x∥) = 1 :=
begin
  rw [inner_smul_self_right, norm_smul, real.norm_eq_abs, ←mul_assoc ∥x∥, mul_comm _ (abs r),
      mul_assoc, abs_of_nonneg (le_of_lt hr), div_self],
  exact mul_ne_zero (ne_of_gt hr)
    (λ h, hx (norm_eq_zero.1 (eq_zero_of_mul_self_eq_zero h)))
end

/-- The inner product of a nonzero vector with a negative multiple of
itself, divided by the product of their norms, has value -1. -/
lemma inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul
  (x : V) (r : ℝ) (hx : x ≠ 0) (hr : r < 0) : inner x (r • x) / (∥x∥ * ∥r • x∥) = -1 :=
begin
  rw [inner_smul_self_right, norm_smul, real.norm_eq_abs, ←mul_assoc ∥x∥, mul_comm _ (abs r),
      mul_assoc, abs_of_neg hr, ←neg_mul_eq_neg_mul, div_neg_eq_neg_div, div_self],
  exact mul_ne_zero (ne_of_lt hr)
    (λ h, hx (norm_eq_zero.1 (eq_zero_of_mul_self_eq_zero h)))
end

/-- The inner product of two vectors, divided by the product of their
norms, has absolute value 1 if and only if they are nonzero and one is
a multiple of the other. One form of equality case for Cauchy-Schwarz. -/
lemma abs_inner_div_norm_mul_norm_eq_one_iff (x y : V) :
  abs (inner x y / (∥x∥ * ∥y∥)) = 1 ↔ (x ≠ 0 ∧ ∃ (r : ℝ), r ≠ 0 ∧ y = r • x) :=
begin
  split,
  { intro h,
    have hx0 : x ≠ 0,
    { intro hx0,
      rw [hx0, inner_zero_left, zero_div] at h,
      norm_num at h,
      exact h },
    refine and.intro hx0 _,
    set r := inner x y / (∥x∥ * ∥x∥) with hr,
    use r,
    set t := y - r • x with ht,
    have ht0 : inner x t = 0,
    { rw [ht, inner_sub_right, inner_smul_right, hr, ←inner_self_eq_norm_square,
          div_mul_cancel _ (λ h, hx0 ((inner_self_eq_zero x).1 h)), sub_self] },
    rw [←sub_add_cancel y (r • x), ←ht, inner_add_right, ht0, zero_add, inner_smul_right,
        inner_self_eq_norm_square, ←mul_assoc, mul_comm,
        mul_div_mul_left _ _ (λ h, hx0 (norm_eq_zero.1 h)), abs_div, abs_mul,
        abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _), ←real.norm_eq_abs,
        ←norm_smul] at h,
    have hr0 : r ≠ 0,
    { intro hr0,
      rw [hr0, zero_smul, norm_zero, zero_div] at h,
      norm_num at h },
    refine and.intro hr0 _,
    have h2 : ∥r • x∥ ^ 2 = ∥t + r • x∥ ^ 2,
    { congr' 1,
      refine eq_of_div_eq_one _ _ h,
      intro h0,
      rw [h0, div_zero] at h,
      norm_num at h },
    rw [pow_two, pow_two, ←inner_self_eq_norm_square, ←inner_self_eq_norm_square,
        inner_add_add_self] at h2,
    conv_rhs at h2 {
      congr,
      congr,
      skip,
      rw [inner_smul_right, inner_comm, ht0, mul_zero, mul_zero]
    },
    symmetry' at h2,
    rw [add_zero, add_left_eq_self, inner_self_eq_zero] at h2,
    rw h2 at ht,
    exact eq_of_sub_eq_zero ht.symm },
  { intro h,
    rcases h with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩,
    rw hy,
    exact abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul x r hx hr }
end

/-- The inner product of two vectors, divided by the product of their
norms, has value 1 if and only if they are nonzero and one is
a positive multiple of the other. -/
lemma inner_div_norm_mul_norm_eq_one_iff (x y : V) :
  inner x y / (∥x∥ * ∥y∥) = 1 ↔ (x ≠ 0 ∧ ∃ (r : ℝ), 0 < r ∧ y = r • x) :=
begin
  split,
  { intro h,
    have ha := h,
    apply_fun abs at ha,
    norm_num at ha,
    rcases (abs_inner_div_norm_mul_norm_eq_one_iff x y).1 ha with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩,
    use hx,
    use r,
    refine and.intro _ hy,
    by_contradiction hrneg,
    rw hy at h,
    rw inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul x r hx
      (lt_of_le_of_ne' (le_of_not_lt hrneg) hr) at h,
    norm_num at h },
  { intro h,
    rcases h with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩,
    rw hy,
    exact inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul x r hx hr }
end

/-- The inner product of two vectors, divided by the product of their
norms, has value -1 if and only if they are nonzero and one is
a negative multiple of the other. -/
lemma inner_div_norm_mul_norm_eq_neg_one_iff (x y : V) :
  inner x y / (∥x∥ * ∥y∥) = -1 ↔ (x ≠ 0 ∧ ∃ (r : ℝ), r < 0 ∧ y = r • x) :=
begin
  split,
  { intro h,
    have ha := h,
    apply_fun abs at ha,
    norm_num at ha,
    rcases (abs_inner_div_norm_mul_norm_eq_one_iff x y).1 ha with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩,
    use hx,
    use r,
    refine and.intro _ hy,
    by_contradiction hrpos,
    rw hy at h,
    rw inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul x r hx
      (lt_of_le_of_ne' (le_of_not_lt hrpos) hr.symm) at h,
    norm_num at h },
  { intro h,
    rcases h with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩,
    rw hy,
    exact inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul x r hx hr }
end

/-- The undirected angle between two vectors. If either vector is 0,
this is π/2. -/
def angle_of_vectors (x y : V) : ℝ := (inner x y / (∥x∥ * ∥y∥)).arccos

/-- The angle between two vectors does not depend on their order. -/
lemma angle_of_vectors_comm (x y : V) : angle_of_vectors x y = angle_of_vectors y x :=
begin
  unfold angle_of_vectors,
  rw [inner_comm, mul_comm]
end

/-- The angle between the negation of two vectors. -/
@[simp] lemma angle_of_vectors_of_neg_of_neg (x y : V) :
  angle_of_vectors (-x) (-y) = angle_of_vectors x y :=
begin
  unfold angle_of_vectors,
  rw [inner_neg_neg, norm_neg, norm_neg]
end

/-- The angle between two vectors is nonnegative. -/
lemma angle_of_vectors_nonneg (x y : V) : 0 ≤ angle_of_vectors x y :=
real.arccos_nonneg _

/-- The angle between two vectors is at most π. -/
lemma angle_of_vectors_le_pi (x y : V) : angle_of_vectors x y ≤ real.pi :=
real.arccos_le_pi _

/-- The angle between a vector and the negation of another vector. -/
lemma angle_of_vectors_of_neg_right (x y : V) :
  angle_of_vectors x (-y) = real.pi - angle_of_vectors x y :=
begin
  unfold angle_of_vectors,
  rw ←real.arccos_neg,
  congr,
  rw [norm_neg, inner_neg_right, neg_div]
end

/-- The angle between the negation of a vector and another vector. -/
lemma angle_of_vectors_of_neg_left (x y : V) :
  angle_of_vectors (-x) y = real.pi - angle_of_vectors x y :=
by rw [←angle_of_vectors_of_neg_of_neg, neg_neg, angle_of_vectors_of_neg_right]

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

/-- The angle between two vectors is zero if and only if they are
nonzero and one is a positive multiple of the other. -/
lemma angle_of_vectors_eq_zero_iff (x y : V) :
  angle_of_vectors x y = 0 ↔ (x ≠ 0 ∧ ∃ (r : ℝ), 0 < r ∧ y = r • x) :=
begin
  unfold angle_of_vectors,
  rw [←inner_div_norm_mul_norm_eq_one_iff, ←real.arccos_one],
  split,
  { intro h,
    exact real.arccos_inj (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).1
                          (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).2
                          (by norm_num)
                          (by norm_num)
                          h },
  { intro h,
    rw h }
end

/-- The angle between two vectors is π if and only if they are nonzero
and one is a negative multiple of the other. -/
lemma angle_of_vectors_eq_pi_iff (x y : V) :
  angle_of_vectors x y = real.pi ↔ (x ≠ 0 ∧ ∃ (r : ℝ), r < 0 ∧ y = r • x) :=
begin
  unfold angle_of_vectors,
  rw [←inner_div_norm_mul_norm_eq_neg_one_iff, ←real.arccos_neg_one],
  split,
  { intro h,
    exact real.arccos_inj (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).1
                          (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).2
                          (by norm_num)
                          (by norm_num)
                          h },
  { intro h,
    rw h }
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
lemma norm_sub_square_eq_norm_square_add_norm_square_sub_two_mul_norm_mul_norm_mul_cos_angle
    (x y : V) :
  ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ - 2 * ∥x∥ * ∥y∥ * (angle_of_vectors x y).cos :=
by rw [(show 2 * ∥x∥ * ∥y∥ * (angle_of_vectors x y).cos =
             2 * ((angle_of_vectors x y).cos * (∥x∥ * ∥y∥)), by ring),
       cos_angle_of_vectors_mul_norm_mul_norm, ←inner_self_eq_norm_square,
       ←inner_self_eq_norm_square, ←inner_self_eq_norm_square, inner_sub_sub_self,
       sub_add_eq_add_sub]

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

/-- Multiplying `a` by itself and then by its inverse results in `a`
(whether or not `a` is zero). -/
lemma mul_self_mul_inv (a : ℝ) : a * a * a⁻¹ = a :=
begin
  by_cases h : a = 0,
  { rw [h, inv_zero, mul_zero] },
  { rw [mul_assoc, mul_inv_cancel h, mul_one] }
end

/-- Converse of pons asinorum, vector angle form. -/
lemma norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi (x y : V)
    (h : angle_of_vectors x (x - y) = angle_of_vectors y (y - x))
    (hpi : angle_of_vectors x y ≠ real.pi) : ∥x∥ = ∥y∥ :=
begin
  replace h := real.arccos_inj (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x (x - y))).1
                               (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x (x - y))).2
                               (abs_le.mp (abs_inner_div_norm_mul_norm_le_one y (y - x))).1
                               (abs_le.mp (abs_inner_div_norm_mul_norm_le_one y (y - x))).2
                               h,
  by_cases hxy : x = y,
  { rw hxy },
  { rw [←norm_neg (y - x), neg_sub, mul_comm, mul_comm ∥y∥, div_eq_mul_inv, div_eq_mul_inv,
        mul_inv', mul_inv', ←mul_assoc, ←mul_assoc] at h,
    replace h :=
      mul_right_cancel' (inv_ne_zero (λ hz, hxy (eq_of_sub_eq_zero (norm_eq_zero.1 hz)))) h,
    rw [inner_sub_right, inner_sub_right, inner_comm y x, inner_self_eq_norm_square,
        inner_self_eq_norm_square, mul_sub_right_distrib, mul_sub_right_distrib,
        mul_self_mul_inv, mul_self_mul_inv, sub_eq_sub_iff_sub_eq_sub,
        ←mul_sub_left_distrib] at h,
    by_cases hx0 : x = 0,
    { rw [hx0, norm_zero, inner_zero_left, zero_mul, zero_sub, neg_eq_zero] at h,
      rw [hx0, norm_zero, h] },
    { by_cases hy0 : y = 0,
      { rw [hy0, norm_zero, inner_zero_right, zero_mul, sub_zero] at h,
        rw [hy0, norm_zero, h] },
      { rw [inv_sub_inv (λ hz, hx0 (norm_eq_zero.1 hz)) (λ hz, hy0 (norm_eq_zero.1 hz)),
            ←neg_sub, ←mul_div_assoc, mul_comm, mul_div_assoc, ←mul_neg_one] at h,
        symmetry,
        by_contradiction hyx,
        replace h := (mul_left_cancel' (sub_ne_zero_of_ne hyx) h).symm,
        rw [inner_div_norm_mul_norm_eq_neg_one_iff, ←angle_of_vectors_eq_pi_iff] at h,
        exact hpi h } } }
end

end real_inner_product

section isometry
/-!
### Euclidean isometries

This section develops properties of isometries in Euclidean space,
showing that they are affine maps that preserve the inner product.
-/

open add_action add_torsor

variables (V1 : Type*) {P1 : Type*} [inner_product_space V1] [metric_space P1]
    [S1 : euclidean_affine_space V1 P1] (V2 : Type*) {P2 : Type*} [inner_product_space V2]
    [metric_space P2] [S2 : euclidean_affine_space V2 P2]

/-- The inner product, in terms of the norm. -/
lemma inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (x y : V2) :
  inner x y = (∥x + y∥ * ∥x + y∥ - ∥x∥ * ∥x∥ - ∥y∥ * ∥y∥) / 2 :=
begin
  rw norm_add_mul_self,
  ring
end

/-- The inner product, in terms of the norm. -/
lemma inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x y : V2) :
  inner x y = (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ - ∥x - y∥ * ∥x - y∥) / 2 :=
begin
  rw norm_sub_mul_self,
  ring
end

/-- Whether a map on vectors preserves the inner product. -/
def preserves_inner (f : V1 → V2) : Prop := ∀ x y, inner (f x) (f y) = inner x y

/-- A function that preserves the inner product preserves addition. -/
lemma fn_of_add_eq_add_of_fn_of_preserves_inner (f : V1 → V2)
    (h : preserves_inner V1 V2 f) (x y : V1) : f (x + y) = f x + f y :=
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
lemma fn_of_smul_eq_smul_of_fn_of_preserves_inner (f : V1 → V2)
    (h : preserves_inner V1 V2 f) (r : ℝ) (x : V1) :  f (r • x) = r • f x :=
begin
  apply eq_of_sub_eq_zero,
  rw [←inner_self_eq_zero, inner_sub_right, inner_sub_left, inner_sub_left, inner_smul_right,
      inner_smul_right, inner_smul_left, inner_smul_left, h, h, h, h, inner_smul_right,
      inner_smul_right, inner_smul_left],
  ring
end

/-- A function that preserves the inner product is a linear map. -/
def linear_map_of_preserves_inner (f : V1 → V2) (h : preserves_inner V1 V2 f) :
  linear_map ℝ V1 V2 :=
{ to_fun := f,
  add := fn_of_add_eq_add_of_fn_of_preserves_inner V1 V2 f h,
  smul := fn_of_smul_eq_smul_of_fn_of_preserves_inner V1 V2 f h }

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
lemma preserves_inner_of_isometry (f : P1 → P2) (h : isometry f) (p : P1) :
  preserves_inner V1 V2 (vector_map_of_point_map V1 V2 f p) :=
begin
  unfold preserves_inner,
  intros x y,
  rw [←neg_vector_map_of_point_map_of_add, inner_neg_left,
      inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
      inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two],
  unfold vector_map_of_point_map,
  rw [vadd_assoc, neg_add_self, zero_vadd, add_comm, vsub_add_vsub_cancel, ←norm_dist,
      ←norm_dist, ←norm_dist, isometry.dist_eq h, isometry.dist_eq h, isometry.dist_eq h,
      norm_dist V1 _ p, norm_dist V1 _ (x +ᵥ p), norm_dist V1 _ (x +ᵥ p), vadd_vsub,
      vsub_vadd_eq_vsub_sub, vsub_vadd_eq_vsub_sub, vsub_self, vadd_vsub, zero_sub, norm_neg,
      norm_sub_rev],
  ring
end

/-- An isometry induces the same map on vectors with any base
point. -/
lemma vector_map_of_isometry_eq (f : P1 → P2) (h : isometry f) (p1 p2 : P1) :
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
  rw ←vsub_sub_vsub_right_cancel V2 (f (x +ᵥ p2 -ᵥ p1 +ᵥ p1)) _ (f p1),
  change vector_map_of_point_map V1 V2 f p1 x =
    vector_map_of_point_map V1 V2 f p1 (x +ᵥ p2 -ᵥ p1) -
      vector_map_of_point_map V1 V2 f p1 (p2 -ᵥ p1),
  apply eq_sub_of_add_eq,
  symmetry,
  rw vadd_vsub_assoc,
  exact fn_of_add_eq_add_of_fn_of_preserves_inner V1 V2 (vector_map_of_point_map V1 V2 f p1)
                                                  (preserves_inner_of_isometry V1 V2 f h p1) _ _
end

/-- The map on vectors corresponding to a map from P1 to P2, for an
isometry. -/
def vector_map_of_isometry (f : P1 → P2) (h : isometry f) : V1 → V2 :=
vector_map_of_point_map V1 V2 f (classical.choice S1.nonempty)

/-- The linear map on vectors corresponding to a map from P1 to P2,
for an isometry. -/
def linear_map_of_isometry (f : P1 → P2) (h : isometry f) : linear_map ℝ V1 V2 :=
linear_map_of_preserves_inner V1 V2 (vector_map_of_isometry V1 V2 f h)
                                    (preserves_inner_of_isometry V1 V2 f h _)

/-- An isometry is an affine map. -/
def affine_map_of_isometry (f : P1 → P2) (h : isometry f) : affine_map ℝ V1 P1 V2 P2 :=
{ to_fun := f,
  linear := linear_map_of_isometry V1 V2 f h,
  add := begin
    intros p v,
    unfold vector_map_of_isometry,
    rw vector_map_of_isometry_eq V1 V2 f h _ p,
    exact (vsub_vadd V2 (f (v +ᵥ p)) (f p)).symm
  end }

end isometry

section euclidean

open add_torsor

variables (V : Type*) {P : Type*} [inner_product_space V] [metric_space P]
    [euclidean_affine_space V P]
include V

/-- The undirected angle at `p2` between the line segments to `p1` and
`p3`. If either of those points equals `p2`, this is π/2. -/
def angle_of_points (p1 p2 p3 : P) : ℝ := angle_of_vectors (p1 -ᵥ p2 : V) (p3 -ᵥ p2)

notation `∠` := angle_of_points

/-- The angle at a point does not depend on the order of the other two
points. -/
lemma angle_of_points_comm (p1 p2 p3 : P) : ∠ V p1 p2 p3 = ∠ V p3 p2 p1 :=
angle_of_vectors_comm _ _

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
        vsub_sub_vsub_right_cancel V p1, ←neg_vsub_eq_vsub_rev V p2 p3, norm_neg]

/-- Law of cosines (cosine rule), angle-at-point form. -/
lemma dist_square_eq_dist_square_add_dist_square_sub_two_mul_dist_mul_dist_mul_cos_angle
    (p1 p2 p3 : P) :
  dist p1 p3 * dist p1 p3 =
    dist p1 p2 * dist p1 p2 + dist p3 p2 * dist p3 p2 -
      2 * dist p1 p2 * dist p3 p2 * (∠ V p1 p2 p3).cos :=
begin
  rw [norm_dist V p1 p3, norm_dist V p1 p2, norm_dist V p3 p2],
  unfold angle_of_points,
  convert norm_sub_square_eq_norm_square_add_norm_square_sub_two_mul_norm_mul_norm_mul_cos_angle
          (p1 -ᵥ p2 : V) (p3 -ᵥ p2 : V),
  { exact (vsub_sub_vsub_right_cancel V p1 p3 p2).symm },
  { exact (vsub_sub_vsub_right_cancel V p1 p3 p2).symm }
end

/-- Pons asinorum, angle-at-point form. -/
lemma angle_eq_angle_of_dist_eq (p1 p2 p3 : P) (h : dist p1 p2 = dist p1 p3) :
  ∠ V p1 p2 p3 = ∠ V p1 p3 p2 :=
begin
  rw [norm_dist V p1 p2, norm_dist V p1 p3] at h,
  unfold angle_of_points,
  convert angle_sub_eq_angle_sub_rev_of_norm_eq (p1 -ᵥ p2 : V) (p1 -ᵥ p3 : V) h,
  { exact (vsub_sub_vsub_left_cancel V p3 p2 p1).symm },
  { exact (vsub_sub_vsub_left_cancel V p2 p3 p1).symm }
end

/-- Converse of pons asinorum, angle-at-point form. -/
lemma dist_eq_of_angle_eq_angle_of_angle_ne_pi (p1 p2 p3 : P)
    (h : ∠ V p1 p2 p3 = ∠ V p1 p3 p2)
    (hpi : ∠ V p2 p1 p3 ≠ real.pi) : dist p1 p2 = dist p1 p3 :=
begin
  unfold angle_of_points at h hpi,
  rw [norm_dist V p1 p2, norm_dist V p1 p3],
  rw [←angle_of_vectors_of_neg_of_neg, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev] at hpi,
  rw [←vsub_sub_vsub_left_cancel V p3 p2 p1, ←vsub_sub_vsub_left_cancel V p2 p3 p1] at h,
  exact norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi (p1 -ᵥ p2 : V) (p1 -ᵥ p3 : V) h hpi
end

end euclidean
