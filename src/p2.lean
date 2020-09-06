-- BMO2 2020 problem 2.

-- Choices made for formalization: the original problem refers to
-- "collections", which we take as meaning sets.  We take "no three
-- points are collinear" as meaning "any three points are affinely
-- independent", in the absence of a specific definition of
-- "collinear" in mathlib (a possible such definition would be "affine
-- span has dimension at most 1", which would then need proving
-- equivalent to not being affinely independent; another possible
-- definition would be "there exists a subspace of dimension 1
-- containing those points", but that's more awkward in the case where
-- the affine space has dimension 0; a third possible definition,
-- covering the case of affine spaces over arbitrary modules, would be
-- that there exist a point and a vector such that all points in the
-- subspace are multiples of that vector added to that point).

import data.matrix.notation
import geometry.euclidean

noncomputable theory
open_locale big_operators
open_locale classical

section ite

lemma apply_dite2 {α β γ : Type*} (f : α → β → γ) (P : Prop) [decidable P] (a : P → α)
  (b : ¬P → α) (c : P → β) (d : ¬P → β) :
  f (dite P a b) (dite P c d) = dite P (λ h, f (a h) (c h)) (λ h, f (b h) (d h)) :=
by { by_cases h : P; simp [h] }

lemma apply_ite2 {α β γ : Type*} (f : α → β → γ) (P : Prop) [decidable P] (a b : α) (c d : β) :
  f (ite P a b) (ite P c d) = ite P (f a c) (f b d) :=
apply_dite2 f P (λ _, a) (λ _, b) (λ _, c) (λ _, d)

end ite

section inner_product

variables {α : Type*} [inner_product_space α]

-- mathlib PR #4045.

/-- A family of vectors is linearly independent if they are nonzero
and orthogonal. -/
lemma linear_independent_of_ne_zero_of_inner_eq_zero {ι : Type*} {v : ι → α}
  (hz : ∀ i, v i ≠ 0) (ho : ∀ i j, i ≠ j → inner (v i) (v j) = 0) : linear_independent ℝ v :=
begin
  rw linear_independent_iff',
  intros s g hg i hi,
  have h' : g i * inner (v i) (v i) = inner (∑ j in s, g j • v j) (v i),
  { rw sum_inner,
    symmetry,
    convert finset.sum_eq_single i _ _,
    { rw inner_smul_left },
    { intros j hj hji,
      rw [inner_smul_left, ho j i hji, mul_zero] },
    { exact λ h, false.elim (h hi) } },
  simpa [hg, hz] using h'
end

end inner_product

section affine

variables (k : Type*) {V : Type*} {P : Type*} [ring k] [add_comm_group V] [module k V]
variables [affine_space V P]
include V

/-- A set is contained in its affine span. -/
lemma subset_affine_span (s : set P) : s ⊆ affine_span k s :=
subset_span_points k s

-- When this is added, simplify
-- exists_unique_dist_eq_of_affine_independent accordingly.

open affine_subspace

/-- Taking the affine span of a set, adding a point and taking the
span again produces the same results as adding the point to the set
and taking the span. -/
@[simp] lemma affine_span_insert_affine_span {p : P} {ps : set P} :
  affine_span k (insert p (affine_span k ps : set P)) = affine_span k (insert p ps) :=
by rw [set.insert_eq, set.insert_eq, span_union, span_union, affine_span_coe]

end affine

-- Geometrical definitions and results that should go in mathlib in
-- some form (possibly more general).

namespace affine
namespace simplex

open affine affine_subspace finite_dimensional euclidean_geometry

variables {V : Type*} {P : Type*} [inner_product_space V] [metric_space P]
    [normed_add_torsor V P]
include V

/-- If there exists a distance that a point has from all vertices of a
simplex, the orthogonal projection of that point onto the subspace
spanned by that simplex is its circumcenter.  Version with distance
condition using `set.range`. -/
lemma orthogonal_projection_eq_circumcenter_of_exists_dist_eq {n : ℕ} (s : simplex ℝ P n)
  {p : P} (hr : ∃ r, ∀ p₁ ∈ set.range s.points, dist p₁ p = r) :
  orthogonal_projection (affine_span ℝ (set.range s.points)) p = s.circumcenter :=
begin
  rw exists_dist_eq_iff_exists_dist_orthogonal_projection_eq (subset_affine_span ℝ _) p at hr,
  cases hr with r hr,
  rw set.forall_range_iff at hr,
  exact s.eq_circumcenter_of_dist_eq
    (orthogonal_projection_mem
      ((affine_span_nonempty ℝ _).2 (set.range_nonempty _))
      (submodule.complete_of_finite_dimensional _)
      p) hr
end

/-- If there exists a distance that a point has from all vertices of a
simplex, the orthogonal projection of that point onto the subspace
spanned by that simplex is its circumcenter.  Version with distance
condition being for all indicies in `fin (n + 1)`. -/
lemma orthogonal_projection_eq_circumcenter_of_exists_dist_eq' {n : ℕ} (s : simplex ℝ P n)
  {p : P} (hr : ∃ r, ∀ i, dist (s.points i) p = r) :
  orthogonal_projection (affine_span ℝ (set.range s.points)) p = s.circumcenter :=
begin
  have h : ∃ r, ∀ p₁ ∈ set.range s.points, dist p₁ p = r,
  { simp_rw [set.forall_range_iff],
    exact hr },
  exact s.orthogonal_projection_eq_circumcenter_of_exists_dist_eq h
end

/-- If a point has the same distance from all vertices of a simplex,
the orthogonal projection of that point onto the subspace spanned by
that simplex is its circumcenter.  Version with distance condition
using `set.range`. -/
lemma orthogonal_projection_eq_circumcenter_of_dist_eq {n : ℕ} (s : simplex ℝ P n) {p : P}
  {r : ℝ} (hr : ∀ p₁ ∈ set.range s.points, dist p₁ p = r) :
  orthogonal_projection (affine_span ℝ (set.range s.points)) p = s.circumcenter :=
s.orthogonal_projection_eq_circumcenter_of_exists_dist_eq ⟨r, hr⟩

/-- If a point has the same distance from all vertices of a simplex,
the orthogonal projection of that point onto the subspace spanned by
that simplex is its circumcenter.  Version with distance condition
being for all indices in `fin (n + 1)`. -/
lemma orthogonal_projection_eq_circumcenter_of_dist_eq' {n : ℕ} (s : simplex ℝ P n) {p : P}
  {r : ℝ} (hr : ∀ i, dist (s.points i) p = r) :
  orthogonal_projection (affine_span ℝ (set.range s.points)) p = s.circumcenter :=
s.orthogonal_projection_eq_circumcenter_of_exists_dist_eq' ⟨r, hr⟩

end simplex

end affine

namespace euclidean_geometry

open affine affine_subspace finite_dimensional euclidean_geometry

variables {V : Type*} {P : Type*} [inner_product_space V] [metric_space P]
    [normed_add_torsor V P]

/-- Reflecting an orthogonal vector plus a point in the subspace
produces the negation of that vector plus the point. -/
lemma reflection_orthogonal_vadd {s : affine_subspace ℝ P}
  (hc : is_complete (s.direction : set V)) {p : P} (hp : p ∈ s) {v : V}
  (hv : v ∈ s.direction.orthogonal) : reflection s (v +ᵥ p) = -v +ᵥ p :=
begin
  rw [reflection_apply, orthogonal_projection_vadd_eq_self hc hp hv, vsub_vadd_eq_vsub_sub],
  simp
end

/-- Reflecting a vector plus a point in the subspace produces the
negation of that vector plus the point if the vector is a multiple of
the result of subtracting a point's orthogonal projection from that
point. -/
lemma reflection_vadd_smul_vsub_orthogonal_projection {s : affine_subspace ℝ P}
  (hc : is_complete (s.direction : set V)) {p₁ : P} (p₂ : P) (r : ℝ) (hp₁ : p₁ ∈ s) :
  reflection s (r • (p₂ -ᵥ orthogonal_projection s p₂) +ᵥ p₁) =
    -(r • (p₂ -ᵥ orthogonal_projection s p₂)) +ᵥ p₁ :=
reflection_orthogonal_vadd hc hp₁
  (submodule.smul_mem _ _ (vsub_orthogonal_projection_mem_direction_orthogonal s _))

-- A set of points is cospherical.  Should add relations between
-- versions with or without centre constrained to be in a given
-- subspace containing the points, and with versions with bundled
-- spheres in nondegenerate cases.
def cospherical (s : set P) : Prop :=
∃ (centre : P) (radius : ℝ), ∀ p ∈ s, dist p centre = radius

include V

/-- Suppose that `c₁` is equidistant from `p₁` and `p₂`, and the same
applies to `c₂`.  Then the vector between `c₁` and `c₂` is orthogonal
to that between `p₁` and `p₂`.  (In two dimensions, this says that the
diagonals of a kite are orthogonal.) -/
lemma inner_vsub_vsub_of_dist_eq_of_dist_eq {c₁ c₂ p₁ p₂ : P} (hc₁ : dist p₁ c₁ = dist p₂ c₁)
  (hc₂ : dist p₁ c₂ = dist p₂ c₂) : inner (c₂ -ᵥ c₁) (p₂ -ᵥ p₁) = 0 :=
begin
  have h : inner ((c₂ -ᵥ c₁) + (c₂ -ᵥ c₁)) (p₂ -ᵥ p₁) = 0,
  { conv_lhs { congr, congr, rw ←vsub_sub_vsub_cancel_right c₂ c₁ p₁,
               skip, rw ←vsub_sub_vsub_cancel_right c₂ c₁ p₂ },
    rw [←add_sub_comm, inner_sub_left],
    conv_lhs { congr, rw ←vsub_sub_vsub_cancel_right p₂ p₁ c₂,
               skip, rw ←vsub_sub_vsub_cancel_right p₂ p₁ c₁ },
    rw [dist_comm p₁, dist_comm p₂, dist_eq_norm_vsub V _ p₁,
        dist_eq_norm_vsub V _ p₂, ←inner_add_sub_eq_zero_iff] at hc₁ hc₂,
    simp_rw [←neg_vsub_eq_vsub_rev c₁, ←neg_vsub_eq_vsub_rev c₂, sub_neg_eq_add,
             neg_add_eq_sub, hc₁, hc₂, sub_zero] },
  simpa [inner_add_left, ←mul_two, (by norm_num : (2 : ℝ) ≠ 0)] using h
end

/-- The squared distance between points on a line (expressed as a
multiple of a fixed vector added to a point) and another point,
expressed as a quadratic. -/
lemma dist_smul_vadd_square (r : ℝ) (v : V) (p₁ p₂ : P) :
  dist (r • v +ᵥ p₁) p₂ * dist (r • v +ᵥ p₁) p₂ =
    inner v v * r * r + 2 * inner v (p₁ -ᵥ p₂) * r + inner (p₁ -ᵥ p₂) (p₁ -ᵥ p₂) :=
begin
  rw [dist_eq_norm_vsub V _ p₂, ←inner_self_eq_norm_square, vadd_vsub_assoc, inner_add_add_self,
      inner_smul_left, inner_smul_left, inner_smul_right],
  ring
end

/-- The condition for two points on a line to be equidistant from
another point. -/
lemma dist_smul_vadd_eq_dist {v : V} (p₁ p₂ : P) (hv : v ≠ 0) (r : ℝ) :
  dist (r • v +ᵥ p₁) p₂ = dist p₁ p₂ ↔ (r = 0 ∨ r = -2 * inner v (p₁ -ᵥ p₂) / inner v v) :=
begin
  conv_lhs { rw [←mul_self_inj_of_nonneg dist_nonneg dist_nonneg, dist_smul_vadd_square,
                 ←sub_eq_zero_iff_eq, add_sub_assoc, dist_eq_norm_vsub V p₁ p₂,
                 ←inner_self_eq_norm_square, sub_self] },
  have hvi : inner v v ≠ 0, by simpa using hv,
  have hd : discrim (inner v v) (2 * inner v (p₁ -ᵥ p₂)) 0 =
    (2 * inner v (p₁ -ᵥ p₂)) * (2 * inner v (p₁ -ᵥ p₂)),
  { rw discrim, ring },
  rw [quadratic_eq_zero_iff hvi hd, add_left_neg, zero_div, neg_mul_eq_neg_mul,
      ←mul_sub_right_distrib, sub_eq_add_neg, ←mul_two, mul_assoc, mul_div_assoc,
      mul_div_mul_left, mul_div_assoc],
  norm_num
end

/-- Distances from two different points determine at most two points
in a two-dimensional subspace containing those points (two circles
intersect in at most two points). -/
lemma eq_of_dist_eq_of_dist_eq_of_mem_of_findim_eq_two {s : affine_subspace ℝ P}
  [finite_dimensional ℝ s.direction] (hd : findim ℝ s.direction = 2) {c₁ c₂ p₁ p₂ p : P}
  (hc₁s : c₁ ∈ s) (hc₂s : c₂ ∈ s) (hp₁s : p₁ ∈ s) (hp₂s : p₂ ∈ s) (hps : p ∈ s) {r₁ r₂ : ℝ}
  (hc : c₁ ≠ c₂) (hp : p₁ ≠ p₂) (hp₁c₁ : dist p₁ c₁ = r₁) (hp₂c₁ : dist p₂ c₁ = r₁)
  (hpc₁ : dist p c₁ = r₁) (hp₁c₂ : dist p₁ c₂ = r₂) (hp₂c₂ : dist p₂ c₂ = r₂)
  (hpc₂ : dist p c₂ = r₂) : p = p₁ ∨ p = p₂ :=
begin
  have ho : inner (c₂ -ᵥ c₁) (p₂ -ᵥ p₁) = 0 :=
    inner_vsub_vsub_of_dist_eq_of_dist_eq (by cc) (by cc),
  let b : fin 2 → V := ![c₂ -ᵥ c₁, p₂ -ᵥ p₁],
  have hb : linear_independent ℝ b,
  { refine linear_independent_of_ne_zero_of_inner_eq_zero _ _,
    { intro i,
      fin_cases i; simp [b, hc.symm, hp.symm] },
    { intros i j hij,
      fin_cases i; fin_cases j; try { exact false.elim (hij rfl) },
      { exact ho },
      { rw inner_comm, exact ho } } },
  have hbs : submodule.span ℝ (set.range b) = s.direction,
  { refine eq_of_le_of_findim_eq _ _,
    { rw [submodule.span_le, set.range_subset_iff],
      intro i,
      fin_cases i,
      { exact vsub_mem_direction hc₂s hc₁s },
      { exact vsub_mem_direction hp₂s hp₁s } },
    { rw [findim_span_eq_card hb, fintype.card_fin, hd] } },
  have hv : ∀ v ∈ s.direction, ∃ t₁ t₂ : ℝ, v = t₁ • (c₂ -ᵥ c₁) + t₂ • (p₂ -ᵥ p₁),
  { intros v hv,
    have hr : set.range b = {c₂ -ᵥ c₁, p₂ -ᵥ p₁},
    { have hu : (finset.univ : finset (fin 2)) = {0, 1}, by dec_trivial,
      rw [←fintype.coe_image_univ, hu],
      simp,
      refl },
    rw [←hbs, hr, submodule.mem_span_insert] at hv,
    rcases hv with ⟨t₁, v', hv', hv⟩,
    rw submodule.mem_span_singleton at hv',
    rcases hv' with ⟨t₂, rfl⟩,
    exact ⟨t₁, t₂, hv⟩ },
  rcases hv (p -ᵥ p₁) (vsub_mem_direction hps hp₁s) with ⟨t₁, t₂, hpt⟩,
  have hop : inner (c₂ -ᵥ c₁) (p -ᵥ p₁) = 0 :=
    inner_vsub_vsub_of_dist_eq_of_dist_eq (by cc) (by cc),
  simp only [hpt, inner_add_right, inner_smul_right, ho, mul_zero, add_zero, mul_eq_zero,
             inner_self_eq_zero, vsub_eq_zero_iff_eq, hc.symm, or_false] at hop,
  rw [hop, zero_smul, zero_add, ←eq_vadd_iff_vsub_eq] at hpt,
  subst hpt,
  have hp' : (p₂ -ᵥ p₁ : V) ≠ 0, { simp [hp.symm] },
  have hp₂ : dist ((1 : ℝ) • (p₂ -ᵥ p₁) +ᵥ p₁) c₁ = r₁, { simp [hp₂c₁] },
  rw [←hp₁c₁, dist_smul_vadd_eq_dist _ _ hp'] at hpc₁ hp₂,
  simp only [one_ne_zero, false_or] at hp₂,
  rw hp₂.symm at hpc₁,
  cases hpc₁; simp [hpc₁]
end

/-- Distances from two different points determine at most two points
in two-dimensional space (two circles intersect in at most two
points). -/
lemma eq_of_dist_eq_of_dist_eq_of_findim_eq_two [finite_dimensional ℝ V] (hd : findim ℝ V = 2)
    {c₁ c₂ p₁ p₂ p : P} {r₁ r₂ : ℝ} (hc : c₁ ≠ c₂) (hp : p₁ ≠ p₂) (hp₁c₁ : dist p₁ c₁ = r₁)
    (hp₂c₁ : dist p₂ c₁ = r₁) (hpc₁ : dist p c₁ = r₁) (hp₁c₂ : dist p₁ c₂ = r₂)
    (hp₂c₂ : dist p₂ c₂ = r₂) (hpc₂ : dist p c₂ = r₂) :
  p = p₁ ∨ p = p₂ :=
begin
  have hd' : findim ℝ (⊤ : affine_subspace ℝ P).direction = 2,
  { rw [direction_top, findim_top],
    exact hd },
  exact eq_of_dist_eq_of_dist_eq_of_mem_of_findim_eq_two hd'
    (mem_top ℝ V _) (mem_top ℝ V _) (mem_top ℝ V _) (mem_top ℝ V _) (mem_top ℝ V _)
    hc hp hp₁c₁ hp₂c₁ hpc₁ hp₁c₂ hp₂c₂ hpc₂
end

/-- Suppose all distances from `p₁` and `p₂` to the points of a
simplex are equal, and that `p₁` and `p₂` lie in the affine span of
`p` with the vertices of that simplex.  Then `p₁` and `p₂` are equal
or reflections of each other in the affine span of the vertices of the
simplex. -/
lemma eq_or_eq_reflection_of_dist_eq {n : ℕ} {s : simplex ℝ P n} {p p₁ p₂ : P} {r : ℝ}
    (hp₁ : p₁ ∈ affine_span ℝ (insert p (set.range s.points)))
    (hp₂ : p₂ ∈ affine_span ℝ (insert p (set.range s.points)))
    (h₁ : ∀ i, dist (s.points i) p₁ = r) (h₂ : ∀ i, dist (s.points i) p₂ = r) :
  p₁ = p₂ ∨ p₁ = reflection (affine_span ℝ (set.range s.points)) p₂ :=
begin
  have h₁' := s.orthogonal_projection_eq_circumcenter_of_dist_eq' h₁,
  have h₂' := s.orthogonal_projection_eq_circumcenter_of_dist_eq' h₂,
  have hn : (affine_span ℝ (set.range s.points) : set P).nonempty :=
    (affine_span_nonempty ℝ _).2 (set.range_nonempty _),
  have hc : is_complete ((affine_span ℝ (set.range s.points)).direction : set V) :=
    submodule.complete_of_finite_dimensional _,
  rw [←affine_span_insert_affine_span,
      mem_affine_span_insert_iff (orthogonal_projection_mem hn hc p)] at hp₁ hp₂,
  rcases hp₁ with ⟨r₁, p₁o, hp₁o, hp₁⟩,
  rcases hp₂ with ⟨r₂, p₂o, hp₂o, hp₂⟩,
  have hp₁o' : orthogonal_projection (affine_span ℝ (set.range s.points)) p₁ = p₁o,
  { rw hp₁,
    exact orthogonal_projection_vadd_smul_vsub_orthogonal_projection hc _ _ hp₁o },
  subst hp₁o',
  rw h₁' at hp₁,
  have hp₂o' : orthogonal_projection (affine_span ℝ (set.range s.points)) p₂ = p₂o,
  { rw hp₂,
    exact orthogonal_projection_vadd_smul_vsub_orthogonal_projection hc _ _ hp₂o },
  subst hp₂o',
  rw h₂' at hp₂,
  have h : s.points 0 ∈ affine_span ℝ (set.range s.points) :=
    mem_affine_span ℝ (set.mem_range_self _),
  have hd₁ : dist p₁ s.circumcenter * dist p₁ s.circumcenter =
    r * r - s.circumradius * s.circumradius,
  { rw [dist_comm, ←h₁ 0,
        dist_square_eq_dist_orthogonal_projection_square_add_dist_orthogonal_projection_square p₁ h],
    simp [h₁', dist_comm p₁] },
  have hd₂ : dist p₂ s.circumcenter * dist p₂ s.circumcenter =
    r * r - s.circumradius * s.circumradius,
  { rw [dist_comm, ←h₂ 0,
        dist_square_eq_dist_orthogonal_projection_square_add_dist_orthogonal_projection_square p₂ h],
    simp [h₂', dist_comm p₂] },
  rw [←hd₂, hp₁, hp₂, dist_eq_norm_vsub V _ s.circumcenter,
      dist_eq_norm_vsub V _ s.circumcenter, vadd_vsub, vadd_vsub, ←inner_self_eq_norm_square,
      ←inner_self_eq_norm_square, inner_smul_left, inner_smul_left, inner_smul_right,
      inner_smul_right, ←mul_assoc, ←mul_assoc] at hd₁,
  by_cases hp : p = orthogonal_projection (affine_span ℝ (set.range s.points)) p,
  { rw [hp₁, hp₂, ←hp],
    simp },
  { have hz : inner (p -ᵥ orthogonal_projection (affine_span ℝ (set.range s.points)) p)
                    (p -ᵥ orthogonal_projection (affine_span ℝ (set.range s.points)) p) ≠ 0,
    { simpa using hp },
    rw [mul_left_inj' hz, mul_self_eq_mul_self_iff] at hd₁,
    rw [hp₁, hp₂],
    cases hd₁,
    { left,
      rw hd₁ },
    { right,
      rw [hd₁,
          reflection_vadd_smul_vsub_orthogonal_projection hc p r₂ s.circumcenter_mem_affine_span,
          neg_smul] } }
end

-- All n-simplices among cospherical points in n-space have the same
-- circumradius.  This should go in mathlib in some form.
lemma exists_circumradius_eq_of_cospherical {ps : set P} {n : ℕ} [finite_dimensional ℝ V]
    (hd : findim ℝ V = n) (hc : cospherical ps) :
  ∃ r : ℝ, ∀ s : simplex ℝ P n, set.range s.points ⊆ ps → s.circumradius = r :=
begin
  rcases hc with ⟨c, r, hcr⟩,
  use r,
  intros s hsps,
  have hs : affine_span ℝ (set.range s.points) = ⊤,
  { refine affine_span_eq_top_of_affine_independent_of_card_eq_findim_add_one s.independent _,
    simp [hd] },
  have hc : c ∈ affine_span ℝ (set.range s.points) := hs.symm ▸ mem_top ℝ V c,
  exact (s.eq_circumradius_of_dist_eq
    hc
    (λ i, hcr (s.points i) (hsps (set.mem_range_self i)))).symm
end

-- All n-simplices among cospherical points in n-space have the same
-- circumcenter.  This should go in mathlib in some form.
lemma exists_circumcenter_eq_of_cospherical {ps : set P} {n : ℕ} [finite_dimensional ℝ V]
    (hd : findim ℝ V = n) (hc : cospherical ps) :
  ∃ c : P, ∀ s : simplex ℝ P n, set.range s.points ⊆ ps → s.circumcenter = c :=
begin
  rcases hc with ⟨c, r, hcr⟩,
  use c,
  intros s hsps,
  have hs : affine_span ℝ (set.range s.points) = ⊤,
  { refine affine_span_eq_top_of_affine_independent_of_card_eq_findim_add_one s.independent _,
    simp [hd] },
  have hc : c ∈ affine_span ℝ (set.range s.points) := hs.symm ▸ mem_top ℝ V c,
  exact (s.eq_circumcenter_of_dist_eq
    hc
    (λ i, hcr (s.points i) (hsps (set.mem_range_self i)))).symm
end

-- Any three points in a cospherical set are affinely independent.
-- Should go in mathlib in some form.
lemma affine_independent_of_cospherical {s : set P} (hs : cospherical s) {p : fin 3 → P}
    (hps : set.range p ⊆ s) (hpi : function.injective p) :
  affine_independent ℝ p :=
begin
  sorry
end

-- A set of points forms an orthocentric system.  This should go in
-- mathlib, along with various properties thereof.
def orthocentric_system (s : set P) : Prop :=
∃ t : triangle ℝ P,
  t.orthocenter ∉ set.range t.points ∧ s = insert t.orthocenter (set.range t.points)

-- Any three points in an orthocentric system are affinely
-- independent.  This should go in mathlib.
lemma affine_independent_of_orthocentric_system {s : set P} (ho : orthocentric_system s)
    {p : fin 3 → P} (hps : set.range p ⊆ s) (hpi : function.injective p) :
  affine_independent ℝ p :=
begin
  sorry
end

-- All triangles in an orthocentric system have the same circumradius.
-- This should go in mathlib.
lemma exists_circumradius_eq_of_orthocentric_system {s : set P} (ho : orthocentric_system s) :
  ∃ r : ℝ, ∀ t : triangle ℝ P, set.range t.points ⊆ s → t.circumradius = r :=
begin
  rcases ho with ⟨t, hto, hts⟩,
  use t.circumradius,
  intros t₂ ht₂,
  sorry
end

-- Given any triangle in an orthocentric system, the fourth point is
-- its orthocenter.  This should go in mathlib.
lemma eq_insert_orthocenter_of_orthocentric_system {s : set P} (ho : orthocentric_system s)
    {t : triangle ℝ P} (ht : set.range t.points ⊆ s) :
  s = insert t.orthocenter (set.range t.points) :=
begin
  sorry
end

end euclidean_geometry

namespace affine
namespace simplex

open affine affine_subspace finite_dimensional euclidean_geometry points_with_circumcenter_index
open finset

variables {V : Type*} {P : Type*} [inner_product_space V] [metric_space P]
    [normed_add_torsor V P]

/-- The weights for the reflection of the circumcenter in an edge of a
simplex.  This definition is only valid with `i₁ ≠ i₂`. -/
def reflection_circumcenter_weights_with_circumcenter {n : ℕ} (i₁ i₂ : fin (n + 1)) :
  points_with_circumcenter_index n → ℝ
| (point_index i) := if i = i₁ ∨ i = i₂ then 1 else 0
| circumcenter_index := -1

/-- `reflection_circumcenter_weights_with_circumcenter` sums to 1. -/
@[simp] lemma sum_reflection_circumcenter_weights_with_circumcenter {n : ℕ} {i₁ i₂ : fin (n + 1)}
  (h : i₁ ≠ i₂) : ∑ i, reflection_circumcenter_weights_with_circumcenter i₁ i₂ i = 1 :=
begin
  simp_rw [sum_points_with_circumcenter, reflection_circumcenter_weights_with_circumcenter,
           sum_ite, sum_const, filter_or, filter_eq'],
  rw card_union_eq,
  { simp },
  { simp [h.symm] }
end

include V

/-- The reflection of the circumcenter of a simplex in an edge, in
terms of `points_with_circumcenter`. -/
lemma reflection_circumcenter_eq_affine_combination_of_points_with_circumcenter {n : ℕ}
  (s : simplex ℝ P n) {i₁ i₂ : fin (n + 1)} (h : i₁ ≠ i₂) :
  reflection (affine_span ℝ (s.points '' {i₁, i₂})) s.circumcenter =
    (univ : finset (points_with_circumcenter_index n)).affine_combination
      s.points_with_circumcenter (reflection_circumcenter_weights_with_circumcenter i₁ i₂) :=
begin
  have hc : card ({i₁, i₂} : finset (fin (n + 1))) = 2,
  { simp [h] },
  rw [reflection_apply, ←coe_singleton, ←coe_insert, s.orthogonal_projection_circumcenter hc,
      circumcenter_eq_centroid, s.face_centroid_eq_centroid hc,
      centroid_eq_affine_combination_of_points_with_circumcenter,
      circumcenter_eq_affine_combination_of_points_with_circumcenter, ←@vsub_eq_zero_iff_eq V,
      affine_combination_vsub, weighted_vsub_vadd_affine_combination, affine_combination_vsub,
      weighted_vsub_apply, sum_points_with_circumcenter],
  simp_rw [pi.sub_apply, pi.add_apply, pi.sub_apply, sub_smul, add_smul, sub_smul,
           centroid_weights_with_circumcenter, circumcenter_weights_with_circumcenter,
           reflection_circumcenter_weights_with_circumcenter, ite_smul, zero_smul, sub_zero,
           apply_ite2 (+), add_zero, ←add_smul, hc, zero_sub, neg_smul, sub_self, add_zero],
  convert sum_const_zero,
  norm_num
end

/-- The distance from the orthocenter to the reflection of the
circumcenter in a side equals the circumradius. -/
lemma dist_orthocenter_reflection_circumcenter (t : triangle ℝ P) {i₁ i₂ : fin 3} (h : i₁ ≠ i₂) :
  dist t.orthocenter (reflection (affine_span ℝ (t.points '' {i₁, i₂})) t.circumcenter) =
    t.circumradius :=
begin
  rw [←mul_self_inj_of_nonneg dist_nonneg t.circumradius_nonneg,
      t.reflection_circumcenter_eq_affine_combination_of_points_with_circumcenter h,
      t.orthocenter_eq_monge_point,
      monge_point_eq_affine_combination_of_points_with_circumcenter,
      dist_affine_combination t.points_with_circumcenter
        (sum_monge_point_weights_with_circumcenter _)
        (sum_reflection_circumcenter_weights_with_circumcenter h)],
  simp_rw [sum_points_with_circumcenter, pi.sub_apply, monge_point_weights_with_circumcenter,
           reflection_circumcenter_weights_with_circumcenter],
  have hu : ({i₁, i₂} : finset (fin 3)) ⊆ univ := subset_univ _,
  obtain ⟨i₃, hi₃, hi₃₁, hi₃₂⟩ :
    ∃ i₃, univ \ ({i₁, i₂} : finset (fin 3)) = {i₃} ∧ i₃ ≠ i₁ ∧ i₃ ≠ i₂, by dec_trivial!,
  simp_rw [←sum_sdiff hu, hi₃],
  simp [hi₃₁, hi₃₂],
  norm_num
end

/-- The distance from the orthocenter to the reflection of the
circumcenter in a side equals the circumradius, variant using a
finset. -/
lemma dist_orthocenter_reflection_circumcenter_finset (t : triangle ℝ P) {i₁ i₂ : fin 3}
    (h : i₁ ≠ i₂) :
  dist t.orthocenter (reflection (affine_span ℝ (t.points '' ↑({i₁, i₂} : finset (fin 3))))
                                 t.circumcenter) =
    t.circumradius :=
begin
  convert dist_orthocenter_reflection_circumcenter t h,
  simp
end

end simplex
end affine

-- Content specific to this problem starts here.

open affine affine_subspace finite_dimensional euclidean_geometry

variables {V : Type*} {P : Type*} [inner_product_space V] [metric_space P]
    [normed_add_torsor V P]

-- Properties of sets of points in the problem.

def at_least_four_points (s : set P) : Prop := 4 ≤ cardinal.mk s

include V

def no_three_points_collinear (s : set P) : Prop :=
∀ p : fin 3 → P, function.injective p → set.range p ⊆ s → affine_independent ℝ p

def same_circumradius (s : set P) : Prop :=
∃ r : ℝ, ∀ t : triangle ℝ P, set.range t.points ⊆ s → t.circumradius = r

-- The description given in the problem.
def p2_problem_desc (s : set P) : Prop :=
at_least_four_points s ∧ no_three_points_collinear s ∧ same_circumradius s

-- Properties of sets of points in the answer.

-- The description given as an answer to the problem.
def p2_answer_desc (s : set P) : Prop :=
at_least_four_points s ∧ (cospherical s ∨ orthocentric_system s)

omit V

-- This was not needed as of mathlib commit
-- e21675586b974322f8221ee42b384a6932d75440 (although even with that
-- commit, simp didn't prove this reduced lemma, only the larger
-- result required after `fin_cases`), but as of mathlib commit
-- eaaac992d0a564071242d08fadffeee3043f91d7 it was needed for simp to
-- reduce extraction of elements of `fin 3`-indexed families
-- automatically.

@[simp] lemma p2_fin3_3 {α : Type*} (a b c : α) : ![a, b, c] 2 = c :=
rfl

include V

-- Given three points in a set with no three collinear, pairwise
-- unequal, they are affinely independent.
theorem p2_affine_independent_of_ne {s : set P} (hn3 : no_three_points_collinear s)
    {p1 p2 p3 : P} (h1 : p1 ∈ s) (h2 : p2 ∈ s) (h3 : p3 ∈ s) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3)
    (h23 : p2 ≠ p3) :
  affine_independent ℝ ![p1, p2, p3] :=
begin
  have hi : function.injective ![p1, p2, p3],
  { intros i1 i2 hi12,
    fin_cases i1; fin_cases i2;
      simpa [h12, h13, h23, h12.symm, h13.symm, h23.symm] using hi12 },
  have hps : set.range ![p1, p2, p3] ⊆ s,
  { rw set.range_subset_iff,
    intro i,
    fin_cases i; simp [h1, h2, h3] },
  exact hn3 _ hi hps
end

-- Given three points in a set with no three collinear, pairwise
-- unequal, the triangle with those as vertices.
def p2_triangle_of_ne {s : set P} (hn3 : no_three_points_collinear s)
    {p1 p2 p3 : P} (h1 : p1 ∈ s) (h2 : p2 ∈ s) (h3 : p3 ∈ s) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3)
    (h23 : p2 ≠ p3) :
  triangle ℝ P :=
⟨![p1, p2, p3], p2_affine_independent_of_ne hn3 h1 h2 h3 h12 h13 h23⟩

-- Given three points in a set with no three collinear, pairwise
-- unequal, the triangle with those as vertices has vertices in the
-- set.
lemma p2_triangle_of_ne_range_subset {s : set P} (hn3 : no_three_points_collinear s)
    {p1 p2 p3 : P} (h1 : p1 ∈ s) (h2 : p2 ∈ s) (h3 : p3 ∈ s) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3)
    (h23 : p2 ≠ p3) :
  set.range (p2_triangle_of_ne hn3 h1 h2 h3 h12 h13 h23).points ⊆ s :=
begin
  rw set.range_subset_iff,
  intro i,
  fin_cases i; simp [p2_triangle_of_ne, h1, h2, h3]
end

-- Any set with at least four points, no three collinear, contains a
-- triangle.
theorem p2_contains_triangle {s : set P} (h4 : at_least_four_points s)
    (hn3 : no_three_points_collinear s) :
  ∃ t : triangle ℝ P, set.range t.points ⊆ s :=
begin
  unfold at_least_four_points at h4,
  rw cardinal.le_mk_iff_exists_subset at h4,
  rcases h4 with ⟨s', hs', h4⟩,
  have hf : s'.finite,
  { refine cardinal.lt_omega_iff_finite.1 _,
    rw h4,
    simp },
  haveI : fintype s' := hf.fintype,
  rw [cardinal.fintype_card, ←finset.card_univ] at h4,
  norm_cast at h4,
  obtain ⟨p1', hp1'⟩ : (finset.univ : finset s').nonempty,
  { simp [←finset.card_pos, h4] },
  let s3 : finset s' := finset.univ.erase p1',
  obtain ⟨p2', hp2'⟩ : s3.nonempty,
  { simp [←finset.card_pos, h4, finset.card_erase_of_mem] },
  have h12 : p1' ≠ p2' := (finset.ne_of_mem_erase hp2').symm,
  let s2 : finset s' := s3.erase p2',
  obtain ⟨p3', hp3'⟩ : s2.nonempty,
  { simp [←finset.card_pos, h4, finset.card_erase_of_mem, hp2'] },
  have h23 : p2' ≠ p3' := (finset.ne_of_mem_erase hp3').symm,
  have h13 : p1' ≠ p3' := (finset.ne_of_mem_erase (finset.mem_of_mem_erase hp3')).symm,
  cases p1' with p1 hp1s',
  cases p2' with p2 hp2s',
  cases p3' with p3 hp3s',
  rw [ne.def, subtype.ext_iff, subtype.coe_mk, subtype.coe_mk, ←ne.def] at h12,
  rw [ne.def, subtype.ext_iff, subtype.coe_mk, subtype.coe_mk, ←ne.def] at h23,
  rw [ne.def, subtype.ext_iff, subtype.coe_mk, subtype.coe_mk, ←ne.def] at h13,
  let t := p2_triangle_of_ne hn3 (hs' hp1s') (hs' hp2s') (hs' hp3s') h12 h13 h23,
  use [t, p2_triangle_of_ne_range_subset hn3 (hs' hp1s') (hs' hp2s') (hs' hp3s') h12 h13 h23]
end

variables [finite_dimensional ℝ V]

-- Given a triangle in a set with the properties of the problem, any
-- point in that set that is not on the circumcircle of the triangle
-- must have distance to the reflection of the circumcentre in a side
-- equal to the circumradius.
theorem p2_dist_reflection_circumcentre {s : set P} (hd2 : findim ℝ V = 2)
    (hn3 : no_three_points_collinear s) {t0 : triangle ℝ P} {p : P}
    (ht0s : set.range t0.points ⊆ s)
    (hr : ∀ (t : triangle ℝ P), set.range t.points ⊆ s → t.circumradius = t0.circumradius)
    (hp : p ∈ s) (hpn : dist p t0.circumcenter ≠ t0.circumradius) {i1 i2 : fin 3}
    (hi12 : i1 ≠ i2) :
  dist p (reflection (affine_span ℝ (t0.points '' ↑({i1, i2} : finset (fin 3)))) t0.circumcenter) =
    t0.circumradius :=
begin
  -- Let i3 be the index of the third vertex of t0.
  obtain ⟨i3, h13, h23, heq⟩ : ∃ i3, i1 ≠ i3 ∧ i2 ≠ i3 ∧ ∀ i, i ∈ ({i3, i1, i2} : finset (fin 3)),
  { dec_trivial! },
  rw ←finset.eq_univ_iff_forall at heq,
  -- Construct the triangle t1 whose vertices are vertices i1 and i2
  -- of t0, together with p.
  have h0s : ∀ i : fin 3, t0.points i ∈ s,
  { rwa set.range_subset_iff at ht0s },
  have h12 := (injective_of_affine_independent t0.independent).ne hi12,
  have hnp : ∀ i : fin 3, t0.points i ≠ p,
  { intros i he,
    rw ←he at hpn,
    exact hpn (t0.dist_circumcenter_eq_circumradius _) },
  let t1 := p2_triangle_of_ne hn3 (h0s i1) (h0s i2) hp h12 (hnp i1) (hnp i2),
  -- t1 has the same circumradius as t0, but different circumcenter.
  have ht1cr := hr t1 (p2_triangle_of_ne_range_subset
    hn3 (h0s i1) (h0s i2) hp h12 (hnp i1) (hnp i2)),
  have ht1cc : t1.circumcenter ≠ t0.circumcenter,
  { intro h,
    have hpc : dist p t1.circumcenter = t1.circumradius := t1.dist_circumcenter_eq_circumradius 2,
    rw [h, ht1cr] at hpc,
    exact hpn hpc },
  -- Consider the side with vertices i1 and i2 as a 1-simplex.
  let t12 : simplex ℝ P 1 := ⟨![t0.points i1, t0.points i2], affine_independent_of_ne ℝ h12⟩,
  -- Vertex i3 together with those of t12 spans the whole space.
  have hu2f : (finset.univ : finset (fin 2)) = {0, 1}, { dec_trivial },
  have hu2 : (set.univ : set (fin 2)) = {0, 1},
  { rw [←finset.coe_univ, hu2f],
    simp },
  have hu3 : (set.univ : set (fin 3)) = {i3, i1, i2},
  { rw [←finset.coe_univ, ←heq],
    simp },
  have h123 : affine_span ℝ (insert (t0.points i3) (set.range t12.points)) = ⊤,
  { have ht0span : affine_span ℝ (set.range t0.points) = ⊤,
    { refine affine_span_eq_top_of_affine_independent_of_card_eq_findim_add_one t0.independent _,
      simp [hd2] },
    rw ←ht0span,
    congr,
    rw [←set.image_univ, ←set.image_univ, hu2, hu3, set.image_insert_eq, set.image_singleton,
        set.image_insert_eq, set.image_insert_eq, set.image_singleton],
    refl },
  -- So the circumcentres of t1 and t2 are in that span.
  have hc0s : t0.circumcenter ∈ affine_span ℝ (insert (t0.points i3) (set.range t12.points)),
  { simp [h123] },
  have hc1s : t1.circumcenter ∈ affine_span ℝ (insert (t0.points i3) (set.range t12.points)),
  { simp [h123] },
  -- All points of t12 have distance from the circumcentres of t0 and
  -- t1 equal to the circumradius of t1.
  have hr0 : ∀ i, dist (t12.points i) t0.circumcenter = t0.circumradius,
  { intro i,
    fin_cases i; simp [t12] },
  have hr1 : ∀ i, dist (t12.points i) t1.circumcenter = t0.circumradius,
  { intro i,
    fin_cases i,
    { change dist (t1.points 0) _ = _,
      simp [←ht1cr] },
    { change dist (t1.points 1) _ = _,
      simp [←ht1cr] } },
  -- So the circumcentres are the same or reflections of each other.
  cases eq_or_eq_reflection_of_dist_eq hc1s hc0s hr1 hr0,
  { exact false.elim (ht1cc h) },
  { have hr : t0.points '' ↑({i1, i2} : finset (fin 3)) = set.range t12.points,
    { rw [←set.image_univ, hu2],
      simp [t12, set.image_insert_eq] },
    rw [hr, ←h],
    change dist (t1.points 2) _ = _,
    simp [ht1cr] }
end

-- Given a triangle in a set with the properties of the problem, any
-- point in that set that is not on the circumcircle of the triangle
-- must be its orthocentre.
theorem p2_eq_orthocentre {s : set P} (hd2 : findim ℝ V = 2) (hn3 : no_three_points_collinear s)
    {t0 : triangle ℝ P} {p : P} (ht0s : set.range t0.points ⊆ s)
    (hr : ∀ (t : triangle ℝ P), set.range t.points ⊆ s → t.circumradius = t0.circumradius)
    (hp : p ∈ s) (hpn : dist p t0.circumcenter ≠ t0.circumradius) :
  p = t0.orthocenter :=
begin
  -- First find a vertex not equal to the orthocentre.
  obtain ⟨i1 : fin 3, hi1o⟩ :=
    (injective_of_affine_independent t0.independent).exists_ne t0.orthocenter,
  obtain ⟨i2, i3, h12, h23, h13, hc12, hc13, h1213⟩ :
    ∃ i2 i3, i1 ≠ i2 ∧ i2 ≠ i3 ∧ i1 ≠ i3 ∧ finset.card ({i1, i2} : finset (fin 3)) = 2 ∧
      finset.card ({i1, i3} : finset (fin 3)) = 2 ∧ ({i1, i2} : finset (fin 3)) ≠ {i1, i3},
  { clear hi1o, dec_trivial! },
  -- We have the distance of p from the reflection of the circumcentre
  -- in the relevant sides.
  have hp12 := p2_dist_reflection_circumcentre hd2 hn3 ht0s hr hp hpn h12,
  have hp13 := p2_dist_reflection_circumcentre hd2 hn3 ht0s hr hp hpn h13,
  -- Also the distance of vertex i1 from those reflections.
  have hi12 : dist (t0.points i1)
                   (reflection (affine_span ℝ (t0.points '' ↑({i1, i2} : finset (fin 3))))
                               t0.circumcenter) = t0.circumradius,
  { rw dist_reflection_eq_of_mem _ (mem_affine_span ℝ (set.mem_image_of_mem _
         (finset.mem_coe.2 (finset.mem_insert_self _ _)))),
    exact t0.dist_circumcenter_eq_circumradius i1 },
  have hi13 : dist (t0.points i1)
                   (reflection (affine_span ℝ (t0.points '' ↑({i1, i3} : finset (fin 3))))
                               t0.circumcenter) = t0.circumradius,
  { rw dist_reflection_eq_of_mem _ (mem_affine_span ℝ (set.mem_image_of_mem _
         (finset.mem_coe.2 (finset.mem_insert_self _ _)))),
    exact t0.dist_circumcenter_eq_circumradius i1 },
  -- Also the distance of the orthocentre from those reflection.
  have ho2 := affine.simplex.dist_orthocenter_reflection_circumcenter_finset t0 h12,
  have ho3 := affine.simplex.dist_orthocenter_reflection_circumcenter_finset t0 h13,
  -- The reflections of the circumcentre in the relevant sides are not
  -- the same point.
  have hrne : reflection (affine_span ℝ (t0.points '' ↑({i1, i2} : finset (fin 3))))
                         t0.circumcenter ≠
              reflection (affine_span ℝ (t0.points '' ↑({i1, i3} : finset (fin 3))))
                         t0.circumcenter,
  { intro h,
    rw [reflection_eq_iff_orthogonal_projection_eq, t0.orthogonal_projection_circumcenter hc12,
        t0.orthogonal_projection_circumcenter hc13, (t0.face hc12).circumcenter_eq_centroid,
        (t0.face hc13).circumcenter_eq_centroid, t0.face_centroid_eq_iff] at h,
    exact h1213 h },
  -- Thus p is either vertex i1 or the orthocentre.
  have hpeq :=
    eq_of_dist_eq_of_dist_eq_of_findim_eq_two hd2 hrne hi1o hi12 ho2 hp12 hi13 ho3 hp13,
  cases hpeq,
  { rw [hpeq, t0.dist_circumcenter_eq_circumradius] at hpn,
    exact false.elim (hpn rfl) },
  { exact hpeq }
end

-- Given p on the circumcircle of t0, not a vertex, not the
-- orthocentre, the orthocentre not on the circumcircle; derive a
-- contradiction.
theorem p2_orthocentre_extra {s : set P} (hd2 : findim ℝ V = 2)
    (hn3 : no_three_points_collinear s) {t0 : triangle ℝ P} (ht0s : set.range t0.points ⊆ s)
    (hr : ∀ (t : triangle ℝ P), set.range t.points ⊆ s → t.circumradius = t0.circumradius)
    (hos : t0.orthocenter ∈ s) (hor : dist t0.orthocenter t0.circumcenter ≠ t0.circumradius)
    {p : P} (hp : p ∈ s) (hpno : p ≠ t0.orthocenter) (hpnt0 : p ∉ set.range t0.points)
    (hpr : dist p t0.circumcenter = t0.circumradius) :
  false :=
begin
  -- Consider a triangle t1 made of two of the vertices of t0 plus the
  -- orthocentre of t0.
  have h0s : ∀ (i : fin 3), t0.points i ∈ s,
  { rwa set.range_subset_iff at ht0s },
  have h0no : ∀ (i : fin 3), t0.points i ≠ t0.orthocenter,
  { intros i h,
    rw ←h at hor,
    apply hor,
    simp },
  have h0np : ∀ (i : fin 3), t0.points i ≠ p,
  { intros i h,
    apply hpnt0,
    rw set.mem_range,
    exact ⟨i, h⟩ },
  have h01 : t0.points 0 ≠ t0.points 1,
  { intro h,
    have hi := injective_of_affine_independent t0.independent h,
    exact fin.ne_of_vne dec_trivial hi },
  let t1 : triangle ℝ P := p2_triangle_of_ne hn3 (h0s 0) (h0s 1) hos h01 (h0no 0) (h0no 1),
  have ht1s : set.range t1.points ⊆ s :=
    p2_triangle_of_ne_range_subset hn3 (h0s 0) (h0s 1) hos h01 (h0no 0) (h0no 1),
  -- Then the two circumcircles meet only at the two shared vertices,
  -- so p1 does not lie on the circumcircle of t1, so must be its
  -- orthocentre, but that is the third vertex of t0.
  have hpt1 : dist p t1.circumcenter ≠ t1.circumradius,
  { intro heq,
    let t2 : triangle ℝ P := p2_triangle_of_ne hn3 (h0s 0) (h0s 1) hp h01 (h0np 0) (h0np 1),
    have ht2s : set.range t2.points ⊆ s :=
      p2_triangle_of_ne_range_subset hn3 (h0s 0) (h0s 1) hp h01 (h0np 0) (h0np 1),
    have ht0span : affine_span ℝ (set.range t0.points) = ⊤,
    { refine affine_span_eq_top_of_affine_independent_of_card_eq_findim_add_one t0.independent _,
      simp [hd2] },
    have ht1span : affine_span ℝ (set.range t1.points) = ⊤,
    { refine affine_span_eq_top_of_affine_independent_of_card_eq_findim_add_one t1.independent _,
      simp [hd2] },
    have ht2span : affine_span ℝ (set.range t2.points) = ⊤,
    { refine affine_span_eq_top_of_affine_independent_of_card_eq_findim_add_one t2.independent _,
      simp [hd2] },
    have ht02cc : t0.circumcenter = t2.circumcenter,
    { have h : ∀ (i : fin 3), dist (t2.points i) t0.circumcenter = t0.circumradius,
      { intro i,
        fin_cases i; simp [t2, p2_triangle_of_ne, hpr] },
      exact t2.eq_circumcenter_of_dist_eq (ht2span.symm ▸ mem_top ℝ V _) h },
    have ht12cc : t1.circumcenter = t2.circumcenter,
    { have h : ∀ (i : fin 3), dist (t2.points i) t1.circumcenter = t1.circumradius,
      { intro i,
        fin_cases i,
        { change dist (t1.points 0) _ = _,
          simp },
        { change dist (t1.points 1) _ = _,
          simp },
        { simp [t2, p2_triangle_of_ne, heq] } },
      exact t2.eq_circumcenter_of_dist_eq (ht2span.symm ▸ mem_top ℝ V _) h },
    rw [ht02cc, ←ht12cc, ←hr t1 ht1s] at hor,
    change dist (t1.points 2) _ ≠ _ at hor,
    simpa using hor },
  have hpt1o : p = t1.orthocenter,
  { refine p2_eq_orthocentre hd2 hn3 ht1s _ hp hpt1,
    intros t ht,
    rw [hr t ht, hr t1 ht1s] },
  let s' := insert t0.orthocenter (set.range t0.points),
  have hs'o : orthocentric_system s',
  { refine ⟨t0, _, rfl⟩,
    intro h,
    rw set.mem_range at h,
    rcases h with ⟨i, hi⟩,
    exact h0no i hi },
  have ht1s' : set.range t1.points ⊆ s',
  { rw set.range_subset_iff,
    intro i,
    fin_cases i; simp [t1, p2_triangle_of_ne] },
  have hs' := eq_insert_orthocenter_of_orthocentric_system hs'o ht1s',
  rw ←hpt1o at hs',
  have hps' : p ∈ insert t0.orthocenter (set.range t0.points),
  { change p ∈ s',
    rw hs',
    exact set.mem_insert _ _ },
  simpa [hpno, h0np] using hps'
end

-- The main part of the solution: a set with the given property is as
-- described.
theorem p2_result_main {s : set P} (hd2 : findim ℝ V = 2) (h4 : at_least_four_points s)
    (hn3 : no_three_points_collinear s) {r : ℝ}
    (hr : ∀ (t : triangle ℝ P), set.range t.points ⊆ s → simplex.circumradius t = r) :
  cospherical s ∨ orthocentric_system s :=
begin
  obtain ⟨t0, ht0s⟩ := p2_contains_triangle h4 hn3,
  -- TODO: consider subsequent rework using bundled circumcircles.
  by_cases hc : ∀ p ∈ s, dist p t0.circumcenter = t0.circumradius,
  { -- The easier case: all points lie on the circumcircle of t0.
    left,
    exact ⟨t0.circumcenter, t0.circumradius, hc⟩ },
  { -- The harder case: some point does not lie on the circumcircle of
    -- t0.
    right,
    use t0,
    push_neg at hc,
    simp_rw ←ne.def at hc,
    simp_rw ←hr t0 ht0s at hr,
    rcases hc with ⟨p, hps, hpr⟩,
    have hpo := p2_eq_orthocentre hd2 hn3 ht0s hr hps hpr,
    split,
    { rw ←hpo,
      rintros ⟨i, rfl⟩,
      apply hpr,
      simp },
    { have hsub : insert t0.orthocenter (set.range t0.points) ⊆ s,
      { rw [←hpo, set.insert_subset],
        exact ⟨hps, ht0s⟩ },
      refine set.subset.antisymm _ hsub,
      rw set.subset_def,
      rintros p1 hp1,
      rw set.mem_insert_iff,
      by_contradiction hp1c,
      push_neg at hp1c,
      rcases hp1c with ⟨hp1no, hp1nt0⟩,
      by_cases hp1r : dist p1 t0.circumcenter = t0.circumradius,
      { rw hpo at hpr hps,
        exact p2_orthocentre_extra hd2 hn3 ht0s hr hps hpr hp1 hp1no hp1nt0 hp1r },
      { exact hp1no (p2_eq_orthocentre hd2 hn3 ht0s hr hp1 hp1r) } } }
end

-- The result of the problem.
theorem p2_result (s : set P) (hd2 : findim ℝ V = 2) :
  p2_problem_desc s ↔ p2_answer_desc s :=
begin
  unfold p2_problem_desc p2_answer_desc,
  rw and.congr_right_iff,
  intro h4,
  split,
  { -- The main part of the solution: a set with the given property is
    -- as described.
    rintro ⟨hn3, r, hr⟩,
    exact p2_result_main hd2 h4 hn3 hr },
  { -- The easy part of the solution: a set as described satisfies the
    -- conditions of the problem.
    rintro (hc | ho),
    { split,
      { exact λ p hpi hps, affine_independent_of_cospherical hc hps hpi },
      { exact exists_circumradius_eq_of_cospherical hd2 hc } },
    { split,
      { exact λ p hpi hps, affine_independent_of_orthocentric_system ho hps hpi },
      { exact exists_circumradius_eq_of_orthocentric_system ho } } }
end
