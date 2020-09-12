-- BMO2 2020 problem 2.

-- Choices made for formalization: the original problem refers to
-- "collections", which we take as meaning sets.

import data.matrix.notation
import geometry.euclidean

noncomputable theory
open_locale big_operators
open_locale classical

section affine

variables (k : Type*) {V : Type*} {P : Type*} [ring k] [add_comm_group V] [module k V]
          [affine_space V P]
include V

-- When upstreaming, also changes places using submodule.span_mono
-- with vsub_set_mono.

/-- `vector_span` is monotone. -/
lemma vector_span_mono {s₁ s₂ : set P} (h : s₁ ⊆ s₂) : vector_span k s₁ ≤ vector_span k s₂ :=
submodule.span_mono (vsub_set_mono h)

end affine

namespace affine_subspace

variables {k : Type*} {V : Type*} {P : Type*} [ring k] [add_comm_group V] [module k V]
          [affine_space V P]
include V

/-- Two affine subspaces with nonempty intersection are equal if and
only if their directions are equal. -/
lemma eq_iff_direction_eq_of_mem {s₁ s₂ : affine_subspace k P} {p : P} (h₁ : p ∈ s₁)
  (h₂ : p ∈ s₂) : s₁ = s₂ ↔ s₁.direction = s₂.direction :=
⟨λ h, h ▸ rfl, λ h, ext_of_direction_eq h ⟨p, h₁, h₂⟩⟩

end affine_subspace

section affine_space'

variables (k : Type*) {V : Type*} {P : Type*} [field k] [add_comm_group V] [module k V]
          [affine_space V P]
variables {ι : Type*}
include V

-- When upstreaming these, adjust proofs of corresponding affine_span
-- lemmas in mathlib.

open finite_dimensional

/-- The `vector_span` of a family indexed by a `fintype` is
finite-dimensional. -/
instance finite_dimensional_direction_vector_span_of_fintype [fintype ι] (p : ι → P) :
  finite_dimensional k (vector_span k (set.range p)) :=
finite_dimensional_vector_span_of_finite k (set.finite_range _)

/-- The `vector_span` of a subset of a family indexed by a `fintype`
is finite-dimensional. -/
instance finite_dimensional_vector_span_image_of_fintype [fintype ι] (p : ι → P)
  (s : set ι) : finite_dimensional k (vector_span k (p '' s)) :=
finite_dimensional_vector_span_of_finite k ((set.finite.of_fintype _).image _)

-- When upstreaming, adjust proof of
-- findim_vector_span_of_affine_independent to use this one.

variables {k}

/-- The `vector_span` of a finite subset of an affinely independent
family has dimension one less than its cardinality. -/
lemma findim_vector_span_image_finset_of_affine_independent {p : ι → P}
  (hi : affine_independent k p) (s : finset ι) {n : ℕ} (hc : finset.card s = n + 1) :
  findim k (vector_span k (p '' ↑s)) = n :=
begin
  have hi' := affine_independent_of_subset_affine_independent
    (affine_independent_set_of_affine_independent hi) (set.image_subset_range p ↑s),
  have hc' : fintype.card (p '' ↑s) = n + 1,
  { rwa [set.card_image_of_injective ↑s (injective_of_affine_independent hi), fintype.card_coe] },
  have hn : (p '' ↑s).nonempty,
  { simp [hc, ←finset.card_pos] },
  rcases hn with ⟨p₁, hp₁⟩,
  rw affine_independent_set_iff_linear_independent_vsub k hp₁ at hi',
  have hfr : (p '' ↑s \ {p₁}).finite := ((set.finite_mem_finset _).image _).subset
    (set.diff_subset _ _),
  haveI := hfr.fintype,
  have hf : set.finite ((λ (p : P), p -ᵥ p₁) '' (p '' ↑s \ {p₁})) := hfr.image _,
  haveI := hf.fintype,
  have hc : hf.to_finset.card = n,
  { rw [hf.card_to_finset,
        set.card_image_of_injective (p '' ↑s \ {p₁}) (vsub_left_injective _)],
    have hd : insert p₁ (p '' ↑s \ {p₁}) = p '' ↑s,
    { rw [set.insert_diff_singleton, set.insert_eq_of_mem hp₁] },
    have hc'' : fintype.card ↥(insert p₁ (p '' ↑s \ {p₁})) = n + 1,
    { convert hc' },
    rw set.card_insert (p '' ↑s \ {p₁}) (λ h, ((set.mem_diff p₁).2 h).2 rfl) at hc'',
    simpa using hc'' },
  rw [vector_span_eq_span_vsub_set_right_ne k hp₁, findim_span_set_eq_card _ hi', ←hc],
  congr
end

end affine_space'

namespace finite_dimensional

variables {K : Type*} {V : Type*} [field K] [add_comm_group V] [vector_space K V]

/-- A submodule contained in a finite-dimensional submodule is
finite-dimensional. -/
lemma finite_dimensional_of_le {S₁ S₂ : submodule K V} [finite_dimensional K S₂] (h : S₁ ≤ S₂) :
  finite_dimensional K S₁ :=
finite_dimensional_iff_dim_lt_omega.2 (lt_of_le_of_lt (dim_le_of_submodule _ _ h)
                                                      (dim_lt_omega K S₂))

/-- The inf of two submodules, the first finite-dimensional, is
finite-dimensional. -/
instance finite_dimensional_inf_left (S₁ S₂ : submodule K V) [finite_dimensional K S₁] :
  finite_dimensional K (S₁ ⊓ S₂ : submodule K V) :=
finite_dimensional_of_le inf_le_left

/-- The inf of two submodules, the second finite-dimensional, is
finite-dimensional. -/
instance finite_dimensional_inf_right (S₁ S₂ : submodule K V) [finite_dimensional K S₂] :
  finite_dimensional K (S₁ ⊓ S₂ : submodule K V) :=
finite_dimensional_of_le inf_le_right

/-- The sup of two finite-dimensional submodules is
finite-dimensional. -/
instance finite_dimensional_sup (S₁ S₂ : submodule K V) [h₁ : finite_dimensional K S₁]
  [h₂ : finite_dimensional K S₂] : finite_dimensional K (S₁ ⊔ S₂ : submodule K V) :=
begin
  rw ←submodule.fg_iff_finite_dimensional at *,
  exact submodule.fg_sup h₁ h₂
end

end finite_dimensional

section inner_product

variables {α : Type*} [inner_product_space α]

open finite_dimensional

/-- `submodule.orthogonal` reverses the `≤` ordering of two
subspaces. -/
lemma submodule.orthogonal_le {K₁ K₂ : submodule ℝ α} (h : K₁ ≤ K₂) :
  K₂.orthogonal ≤ K₁.orthogonal :=
(submodule.orthogonal_gc α).monotone_l h

/-- If `K₁` is complete and contained in `K₂`, `K₁` and `K₁.orthogonal ⊓ K₂` span `K₂`. -/
lemma submodule.sup_orthogonal_inf_of_is_complete {K₁ K₂ : submodule ℝ α} (h : K₁ ≤ K₂)
  (hc : is_complete (K₁ : set α)) : K₁ ⊔ (K₁.orthogonal ⊓ K₂) = K₂ :=
begin
  ext x,
  rw submodule.mem_sup,
  rcases exists_norm_eq_infi_of_complete_subspace K₁ hc x with ⟨v, hv, hvm⟩,
  rw norm_eq_infi_iff_inner_eq_zero K₁ hv at hvm,
  split,
  { rintro ⟨y, hy, z, hz, rfl⟩,
    exact K₂.add_mem (h hy) hz.2 },
  { exact λ hx, ⟨v, hv, x - v, ⟨(K₁.mem_orthogonal' _).2 hvm, K₂.sub_mem hx (h hv)⟩,
                 add_sub_cancel'_right _ _⟩ }
end

-- For upstreaming to mathlib, replace the proof of
-- submodule.sup_orthogonal_of_is_complete using the above.

/-- Given a finite-dimensional subspace `K₂`, and a subspace `K₁`
containined in it, the dimensions of `K₁` and the intersection of its
orthogonal subspace with `K₂` add to that of `K₂`. -/
lemma submodule.findim_add_inf_findim_orthogonal {K₁ K₂ : submodule ℝ α}
  [finite_dimensional ℝ K₂] (h : K₁ ≤ K₂) :
  findim ℝ K₁ + findim ℝ (K₁.orthogonal ⊓ K₂ : submodule ℝ α) = findim ℝ K₂ :=
begin
  haveI := finite_dimensional_of_le h,
  have hd := dim_sup_add_dim_inf_eq K₁ (K₁.orthogonal ⊓ K₂),
  rw [←findim_eq_dim, ←findim_eq_dim, ←findim_eq_dim,  ←findim_eq_dim, ←inf_assoc,
      (submodule.orthogonal_disjoint K₁).eq_bot, bot_inf_eq, findim_bot,
      submodule.sup_orthogonal_inf_of_is_complete h
        (submodule.complete_of_finite_dimensional _)] at hd,
  norm_cast at hd,
  rw add_zero at hd,
  exact hd.symm
end

end inner_product

namespace finset

variables (k : Type*) {V : Type*} {P : Type*} [division_ring k] [add_comm_group V] [module k V]
variables [affine_space V P] {ι : Type*} (s : finset ι) {ι₂ : Type*} (s₂ : finset ι₂)

include V

-- mathlib PR #4116.

/-- An indexed family of points that is injective on the given
`finset` has the same centroid as the image of that `finset`.  This is
stated in terms of a set equal to the image to provide control of
definitional equality for the index type used for the centroid of the
image. -/
lemma centroid_eq_centroid_image_of_inj_on {p : ι → P} (hi : ∀ i j ∈ s, p i = p j → i = j)
  {ps : set P} [fintype ps] (hps : ps = p '' ↑s) :
  s.centroid k p = (univ : finset ps).centroid k (λ x, x) :=
begin
  let f : p '' ↑s → ι := λ x, x.property.some,
  have hf : ∀ x, f x ∈ s ∧ p (f x) = x := λ x, x.property.some_spec,
  let f' : ps → ι := λ x, f ⟨x, hps ▸ x.property⟩,
  have hf' : ∀ x, f' x ∈ s ∧ p (f' x) = x := λ x, hf ⟨x, hps ▸ x.property⟩,
  have hf'i : function.injective f',
  { intros x y h,
    rw [subtype.ext_iff, ←(hf' x).2, ←(hf' y).2, h] },
  let f'e : ps ↪ ι := ⟨f', hf'i⟩,
  have hu : finset.univ.map f'e = s,
  { ext x,
    rw mem_map,
    split,
    { rintros ⟨i, _, rfl⟩,
      exact (hf' i).1 },
    { intro hx,
      use [⟨p x, hps.symm ▸ set.mem_image_of_mem _ hx⟩, mem_univ _],
      refine hi _ _ (hf' _).1 hx _,
      rw (hf' _).2,
      refl } },
  rw [←hu, centroid_map],
  congr' with x,
  change p (f' x) = ↑x,
  rw (hf' x).2
end

/-- Two indexed families of points that are injective on the given
`finset`s and with the same points in the image of those `finset`s
have the same centroid. -/
lemma centroid_eq_of_inj_on_of_image_eq {p : ι → P} (hi : ∀ i j ∈ s, p i = p j → i = j)
  {p₂ : ι₂ → P} (hi₂ : ∀ i j ∈ s₂, p₂ i = p₂ j → i = j) (he : p '' ↑s = p₂ '' ↑s₂) :
  s.centroid k p = s₂.centroid k p₂ :=
by rw [s.centroid_eq_centroid_image_of_inj_on k hi rfl,
       s₂.centroid_eq_centroid_image_of_inj_on k hi₂ he]

end finset

namespace affine
namespace simplex

variables {k : Type*} {V : Type*} {P : Type*} [division_ring k]
          [add_comm_group V] [module k V] [affine_space V P]
include V

/-- Two simplices with the same points have the same centroid. -/
lemma centroid_eq_of_range_eq {n : ℕ} {s₁ s₂ : simplex k P n}
  (h : set.range s₁.points = set.range s₂.points) :
  finset.univ.centroid k s₁.points = finset.univ.centroid k s₂.points :=
begin
  rw [←set.image_univ, ←set.image_univ, ←finset.coe_univ] at h,
  exact finset.univ.centroid_eq_of_inj_on_of_image_eq k _
    (λ _ _ _ _ he, injective_of_affine_independent s₁.independent he)
    (λ _ _ _ _ he, injective_of_affine_independent s₂.independent he) h
end

end simplex
end affine

section collinear

variables (k : Type*) {V : Type*} {P : Type*} [ring k] [add_comm_group V] [module k V]
variables [affine_space V P]
include V

-- TODO: would be better (avoid a long special-case proof for `fin 3`)
-- to prove affine independent of n+1 points iff findim = n, not
-- affine independent iff findim < n, then deduce these existence
-- forms as equivalent to findim <= 1.

/-- A set of points is collinear if they can all be expressed as
multiples of the same vector, added to the same base point. -/
def collinear (s : set P) : Prop := ∃ (p₀ : P) (v : V), ∀ p ∈ s, ∃ r : k, p = r • v +ᵥ p₀

/-- The definition of `collinear`. -/
lemma collinear_def (s : set P) :
  collinear k s ↔ ∃ (p₀ : P) (v : V), ∀ p ∈ s, ∃ r : k, p = r • v +ᵥ p₀ :=
iff.rfl

variables (P)

/-- The empty set is collinear. -/
lemma collinear_empty : collinear k (∅ : set P) :=
begin
  use add_torsor.nonempty.some,
  simp
end

variables {P}

/-- A single point is collinear. -/
lemma collinear_singleton (p : P) : collinear k ({p} : set P) :=
begin
  use [p, 0],
  simp
end

/-- Two points are collinear. -/
lemma collinear_insert_singleton (p₁ p₂ : P) : collinear k ({p₁, p₂} : set P) :=
begin
  use [p₁, p₂ -ᵥ p₁],
  intros p hp,
  rw [set.mem_insert_iff, set.mem_singleton_iff] at hp,
  cases hp,
  { use 0,
    simp [hp] },
  { use 1,
    simp [hp] }
end

/-- Given a point `p₀` in a set of points, that set is collinear if and
only if the points can all be expressed as multiples of the same
vector, added to `p₀`. -/
lemma collinear_iff_of_mem {s : set P} {p₀ : P} (h : p₀ ∈ s) :
  collinear k s ↔ ∃ v : V, ∀ p ∈ s, ∃ r : k, p = r • v +ᵥ p₀ :=
begin
  split,
  { rintros ⟨p, v, hv⟩,
    use v,
    intros p₁ hp₁,
    rcases hv p₁ hp₁ with ⟨r, rfl⟩,
    rcases hv p₀ h with ⟨r₀, rfl⟩,
    use r - r₀,
    simp [vadd_assoc, ←add_smul] },
  { exact λ h, ⟨p₀, h⟩ }
end

end collinear

section collinear_division_ring

variables (k : Type*) {V : Type*} {P : Type*} [division_ring k] [add_comm_group V] [module k V]
variables [affine_space V P]
include V

/-- Three points are affinely independent if and only if they are not
collinear. -/
lemma affine_independent_iff_not_collinear (p : fin 3 → P) :
  affine_independent k p ↔ ¬ collinear k (set.range p) :=
begin
  split,
  { intros ha hc,
    rw collinear_iff_of_mem k (set.mem_range_self (0 : fin 3)) at hc,
    rcases hc with ⟨v, hv⟩,
    rcases hv (p 1) (set.mem_range_self 1) with ⟨r₁, hr₁⟩,
    rcases hv (p 2) (set.mem_range_self 2) with ⟨r₂, hr₂⟩,
    by_cases h : (r₁ = 0 ∨ r₂ = 0),
    { cases h,
      { rw [h, zero_smul, zero_vadd] at hr₁,
        exact (dec_trivial : (1 : fin 3) ≠ 0) (injective_of_affine_independent ha hr₁) },
      { rw [h, zero_smul, zero_vadd] at hr₂,
        exact (dec_trivial : (2 : fin 3) ≠ 0) (injective_of_affine_independent ha hr₂) } },
    { push_neg at h,
      let w : fin 3 → k := ![r₁⁻¹ - r₂⁻¹, -r₁⁻¹, r₂⁻¹],
      have hu : (finset.univ : finset (fin 3)) = {0, 1, 2}, by dec_trivial,
      have hw : ∑ i, w i = 0,
      { simp_rw [w, hu],
        rw [finset.sum_insert (dec_trivial : 0 ∉ ({1, 2} : finset (fin 3))),
            finset.sum_insert (dec_trivial : 1 ∉ ({2} : finset (fin 3))), finset.sum_singleton],
        change r₁⁻¹ - r₂⁻¹ + (-r₁⁻¹ + r₂⁻¹) = 0,
        abel },
      have hp : finset.univ.weighted_vsub p w = (0 : V),
      { rw [finset.univ.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero w p hw (p 0),
            finset.weighted_vsub_of_point_apply],
        simp_rw [w, hu],
        rw [finset.sum_insert (dec_trivial : 0 ∉ ({1, 2} : finset (fin 3))),
            finset.sum_insert (dec_trivial : 1 ∉ ({2} : finset (fin 3))), finset.sum_singleton],
        change (r₁⁻¹ - r₂⁻¹) • (p 0 -ᵥ p 0) + (-r₁⁻¹ • (p 1 -ᵥ p 0) + r₂⁻¹ • (p 2 -ᵥ p 0)) =
          (0 : V),
        simp [hr₁, hr₂, smul_smul, h] },
      exact h.2 (inv_eq_zero.1 (ha finset.univ w hw hp 2 (finset.mem_univ _))) } },
  { contrapose!,
    intro hna,
    rw affine_independent_iff_of_fintype at hna,
    push_neg at hna,
    rcases hna with ⟨w, hw, hs, i₁, hi₁⟩,
    obtain ⟨i₂, h₂₁, hi₂⟩ : ∃ i₂, i₂ ≠ i₁ ∧ w i₂ ≠ 0,
    { by_contradiction h,
      push_neg at h,
      rw finset.sum_eq_single i₁ (λ i _, h i) (λ hnu, false.elim (hnu (finset.mem_univ _))) at hw,
      exact hi₁ hw },
    obtain ⟨i₃, h₁₃, h₂₃, hu, hu', h₁, h₂⟩ :
      ∃ i₃ : fin 3, i₁ ≠ i₃ ∧ i₂ ≠ i₃ ∧ finset.univ = ({i₁, i₂, i₃} : finset (fin 3)) ∧
        (∀ i, i = i₁ ∨ i = i₂ ∨ i = i₃) ∧ i₁ ∉ ({i₂, i₃} : finset (fin 3)) ∧
        i₂ ∉ ({i₃} : finset (fin 3)),
    { clear hi₁ hi₂, dec_trivial! },
    rw [finset.univ.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero w p hw (p i₃),
        finset.weighted_vsub_of_point_apply, hu, finset.sum_insert h₁, finset.sum_insert h₂,
        finset.sum_singleton, vsub_self, smul_zero, add_zero] at hs,
    use [p i₃, p i₁ -ᵥ p i₃],
    rw set.forall_range_iff,
    intro i,
    replace hu' := hu' i,
    repeat { cases hu' },
    { use 1, simp },
    { use -(w i₂)⁻¹ * w i₁,
      rw add_eq_zero_iff_eq_neg at hs,
      rw [←smul_smul, hs],
      simp [hi₂, smul_smul] },
    { use 0, simp } }
end

/-- Three points are collinear if and only if they are not affinely
independent. -/
lemma collinear_iff_not_affine_independent (p : fin 3 → P) :
  collinear k (set.range p) ↔ ¬ affine_independent k p :=
(not_iff_comm.1 (affine_independent_iff_not_collinear k p).symm).symm

end collinear_division_ring

-- Geometrical definitions and results that should go in mathlib in
-- some form (possibly more general).

namespace affine
namespace simplex

open affine affine_subspace finite_dimensional euclidean_geometry

variables {V : Type*} {P : Type*} [inner_product_space V] [metric_space P]
    [normed_add_torsor V P]
include V

-- mathlib PR #4116.

/-- Two simplices with the same points have the same circumcenter. -/
lemma circumcenter_eq_of_range_eq {n : ℕ} {s₁ s₂ : simplex ℝ P n}
  (h : set.range s₁.points = set.range s₂.points) : s₁.circumcenter = s₂.circumcenter :=
begin
  have hs : s₁.circumcenter ∈ affine_span ℝ (set.range s₂.points) :=
    h ▸ s₁.circumcenter_mem_affine_span,
  have hr : ∀ i, dist (s₂.points i) s₁.circumcenter = s₁.circumradius,
  { intro i,
    have hi : s₂.points i ∈ set.range s₂.points := set.mem_range_self _,
    rw [←h, set.mem_range] at hi,
    rcases hi with ⟨j, hj⟩,
    rw [←hj, s₁.dist_circumcenter_eq_circumradius j] },
  exact s₂.eq_circumcenter_of_dist_eq hs hr
end

/-- Two simplices with the same points have the same Monge point. -/
lemma monge_point_eq_of_range_eq {n : ℕ} {s₁ s₂ : simplex ℝ P n}
  (h : set.range s₁.points = set.range s₂.points) : s₁.monge_point = s₂.monge_point :=
by simp_rw [monge_point_eq_smul_vsub_vadd_circumcenter, centroid_eq_of_range_eq h,
            circumcenter_eq_of_range_eq h]

end simplex

namespace triangle

open finset simplex

variables {V : Type*} {P : Type*} [inner_product_space V] [metric_space P]
    [normed_add_torsor V P]

include V

/-- Two triangles with the same points have the same orthocenter. -/
lemma orthocenter_eq_of_range_eq {t₁ t₂ : triangle ℝ P}
  (h : set.range t₁.points = set.range t₂.points) : t₁.orthocenter = t₂.orthocenter :=
monge_point_eq_of_range_eq h

end triangle

end affine

namespace euclidean_geometry

open affine affine_subspace finite_dimensional euclidean_geometry

variables {V : Type*} {P : Type*} [inner_product_space V] [metric_space P]
    [normed_add_torsor V P]

-- TODO: for adding to mathlib, should add relations between versions
-- with or without centre constrained to be in a given subspace
-- containing the points, and with versions with bundled spheres in
-- nondegenerate cases.

/-- A set of points is cospherical if they are equidistant from some
point.  In two dimensions, this is the same thing as being
concyclic. -/
def cospherical (s : set P) : Prop :=
∃ (centre : P) (radius : ℝ), ∀ p ∈ s, dist p centre = radius

include V

-- mathlib PR #4088.

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

-- TODO (for when these next two results go in mathlib): variants of
-- these results using a finite-dimensional subspace not the full
-- space.

/-- All n-simplices among cospherical points in n-space have the same
circumradius. -/
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

/-- All n-simplices among cospherical points in n-space have the same
circumcenter. -/
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

/-- Any three points in a cospherical set are affinely independent. -/
lemma affine_independent_of_cospherical {s : set P} (hs : cospherical s) {p : fin 3 → P}
    (hps : set.range p ⊆ s) (hpi : function.injective p) :
  affine_independent ℝ p :=
begin
  rw affine_independent_iff_not_collinear,
  intro hc,
  rw collinear_iff_of_mem ℝ (set.mem_range_self (0 : fin 3)) at hc,
  rcases hc with ⟨v, hv⟩,
  rw set.forall_range_iff at hv,
  have hv0 : v ≠ 0,
  { intro h,
    have he : p 1 = p 0,
    { have hv1 := hv 1,
      simpa [h] using hv1 },
    exact (dec_trivial : (1 : fin 3) ≠ 0) (hpi he) },
  rcases hs with ⟨c, r, hs⟩,
  have hs' := λ i, hs (p i) (set.mem_of_mem_of_subset (set.mem_range_self _) hps),
  choose f hf using hv,
  have hsd : ∀ i, dist ((f i • v) +ᵥ p 0) c = r,
  { intro i,
    rw ←hf,
    exact hs' i },
  have hf0 : f 0 = 0,
  { have hf0' := hf 0,
    rw [eq_comm, ←@vsub_eq_zero_iff_eq V, vadd_vsub, smul_eq_zero] at hf0',
    simpa [hv0] using hf0' },
  have hfi : function.injective f,
  { intros i j h,
    have hi := hf i,
    rw [h, ←hf j] at hi,
    exact hpi hi },
  simp_rw [←hsd 0, hf0, zero_smul, zero_vadd] at hsd,
  simp_rw [dist_smul_vadd_eq_dist (p 0) c hv0] at hsd,
  have hfn0 : ∀ i, i ≠ 0 → f i ≠ 0 := λ i, (hfi.ne_iff' hf0).2,
  have hfn0' : ∀ i, i ≠ 0 → f i = (-2) * inner v (p 0 -ᵥ c) / inner v v,
  { intros i hi,
    have hsdi := hsd i,
    simpa [hfn0, hi] using hsdi },
  have hf12 : f 1 = f 2, { rw [hfn0' 1 dec_trivial, hfn0' 2 dec_trivial] },
  exact (dec_trivial : (1 : fin 3) ≠ 2) (hfi hf12)
end

end euclidean_geometry

namespace affine
namespace simplex

open affine affine_subspace finite_dimensional euclidean_geometry points_with_circumcenter_index
open finset

variables {V : Type*} {P : Type*} [inner_product_space V] [metric_space P]
    [normed_add_torsor V P]

include V

/-- A vertex lies in the corresponding altitude. -/
lemma mem_altitude {n : ℕ} (s : simplex ℝ P (n + 1)) (i : fin (n + 2)) :
  s.points i ∈ s.altitude i :=
(mem_inf_iff _ _ _).2 ⟨self_mem_mk' _ _, mem_affine_span ℝ (set.mem_range_self _)⟩

/-- The direction of an altitude. -/
lemma direction_altitude {n : ℕ} (s : simplex ℝ P (n + 1)) (i : fin (n + 2)) :
  (s.altitude i).direction = (vector_span ℝ (s.points '' ↑(finset.univ.erase i))).orthogonal ⊓
    vector_span ℝ (set.range s.points) :=
by rw [altitude_def,
       direction_inf_of_mem (self_mem_mk' (s.points i) _)
         (mem_affine_span ℝ (set.mem_range_self _)), direction_mk', direction_affine_span,
       direction_affine_span]

/-- The vector span of the opposite face lies in the direction
orthogonal to an altitude. -/
lemma vector_span_le_altitude_direction_orthogonal  {n : ℕ} (s : simplex ℝ P (n + 1))
    (i : fin (n + 2)) :
  vector_span ℝ (s.points '' ↑(finset.univ.erase i)) ≤ (s.altitude i).direction.orthogonal :=
begin
  rw direction_altitude,
  exact le_trans
    (vector_span ℝ (s.points '' ↑(finset.univ.erase i))).le_orthogonal_orthogonal
    (submodule.orthogonal_le inf_le_left)
end

/-- An altitude is finite-dimensional. -/
instance finite_dimensional_direction_altitude {n : ℕ} (s : simplex ℝ P (n + 1))
  (i : fin (n + 2)) : finite_dimensional ℝ ((s.altitude i).direction) :=
begin
  rw direction_altitude,
  apply_instance
end

/-- An altitude is one-dimensional (i.e., a line). -/
@[simp] lemma findim_direction_altitude {n : ℕ} (s : simplex ℝ P (n + 1)) (i : fin (n + 2)) :
  findim ℝ ((s.altitude i).direction) = 1 :=
begin
  rw direction_altitude,
  have h := submodule.findim_add_inf_findim_orthogonal
    (vector_span_mono ℝ (set.image_subset_range s.points ↑(univ.erase i))),
  have hc : card (univ.erase i) = n + 1, { rw card_erase_of_mem (mem_univ _), simp },
  rw [findim_vector_span_of_affine_independent s.independent (fintype.card_fin _),
      findim_vector_span_image_finset_of_affine_independent s.independent _ hc] at h,
  simpa using h
end

/-- A line through a vertex is the altitude through that vertex if and
only if it is orthogonal to the opposite face. -/
lemma affine_span_insert_singleton_eq_altitude_iff {n : ℕ} (s : simplex ℝ P (n + 1))
    (i : fin (n + 2)) (p : P) :
  affine_span ℝ {p, s.points i} = s.altitude i ↔ (p ≠ s.points i ∧
    p ∈ affine_span ℝ (set.range s.points) ∧
    p -ᵥ s.points i ∈ (affine_span ℝ (s.points '' ↑(finset.univ.erase i))).direction.orthogonal) :=
begin
  rw [eq_iff_direction_eq_of_mem
        (mem_affine_span ℝ (set.mem_insert_of_mem _ (set.mem_singleton _))) (s.mem_altitude _),
      ←vsub_right_mem_direction_iff_mem (mem_affine_span ℝ (set.mem_range_self i)) p,
      direction_affine_span, direction_affine_span, direction_affine_span],
  split,
  { intro h,
    split,
    { intro heq,
      rw [heq, set.pair_eq_singleton, vector_span_singleton] at h,
      have hd : findim ℝ (s.altitude i).direction = 0,
      { rw [←h, findim_bot] },
      simpa using hd },
    { rw [←submodule.mem_inf, inf_comm, ←direction_altitude, ←h],
      exact vsub_mem_vector_span ℝ (set.mem_insert _ _)
                                   (set.mem_insert_of_mem _ (set.mem_singleton _)) } },
  { rintro ⟨hne, h⟩,
    rw [←submodule.mem_inf, inf_comm, ←direction_altitude] at h,
    rw [vector_span_eq_span_vsub_set_left_ne ℝ (set.mem_insert _ _),
        set.insert_diff_of_mem _ (set.mem_singleton _),
        set.diff_singleton_eq_self (λ h, hne (set.mem_singleton_iff.1 h)), set.image_singleton],
    refine eq_of_le_of_findim_eq _ _,
    { rw submodule.span_le,
      simpa using h },
    { rw [findim_direction_altitude, findim_span_set_eq_card],
      { simp },
      { refine linear_independent_singleton _,
        simpa using hne } } }
end

end simplex
end affine

namespace euclidean_geometry

open affine affine_subspace finite_dimensional euclidean_geometry

variables {V : Type*} {P : Type*} [inner_product_space V] [metric_space P]
    [normed_add_torsor V P]

include V

/-- Four points form an orthocentric system if they consist of the
vertices of a triangle and its orthocenter. -/
def orthocentric_system (s : set P) : Prop :=
∃ t : triangle ℝ P,
  t.orthocenter ∉ set.range t.points ∧ s = insert t.orthocenter (set.range t.points)

/-- This is an auxiliary lemma giving information about the relation
of two triangles in an orthocentric system; it abstracts some
reasoning, with no geometric content, that is common to some other
lemmas.  Suppose the orthocentric system is generated by triangle `t`,
and we are given three points `p` in the orthocentric system.  Then
either we can find indices `i₁`, `i₂` and `i₃` for `p` such that `p
i₁` is the orthocenter of `t` and `p i₂` and `p i₃` are points `j₂`
and `j₃` of `t`, or `p` has the same points as `t`. -/
lemma exists_of_range_subset_orthocentric_system {t : triangle ℝ P}
  (ho : t.orthocenter ∉ set.range t.points) {p : fin 3 → P}
  (hps : set.range p ⊆ insert t.orthocenter (set.range t.points)) (hpi : function.injective p) :
  (∃ (i₁ i₂ i₃ j₂ j₃ : fin 3), i₁ ≠ i₂ ∧ i₁ ≠ i₃ ∧ i₂ ≠ i₃ ∧
    (∀ i : fin 3, i = i₁ ∨ i = i₂ ∨ i = i₃) ∧ p i₁ = t.orthocenter ∧ j₂ ≠ j₃ ∧
    t.points j₂ = p i₂ ∧ t.points j₃ = p i₃) ∨ set.range p = set.range t.points :=
begin
  by_cases h : t.orthocenter ∈ set.range p,
  { left,
    rcases h with ⟨i₁, h₁⟩,
    obtain ⟨i₂, i₃, h₁₂, h₁₃, h₂₃, h₁₂₃⟩ :
      ∃ (i₂ i₃ : fin 3), i₁ ≠ i₂ ∧ i₁ ≠ i₃ ∧ i₂ ≠ i₃ ∧ ∀ i : fin 3, i = i₁ ∨ i = i₂ ∨ i = i₃,
    { clear h₁, dec_trivial! },
    have h : ∀ i, i₁ ≠ i → ∃ (j : fin 3), t.points j = p i,
    { intros i hi,
      replace hps := set.mem_of_mem_insert_of_ne
        (set.mem_of_mem_of_subset (set.mem_range_self i) hps) (h₁ ▸ hpi.ne hi.symm),
      exact hps },
    rcases h i₂ h₁₂ with ⟨j₂, h₂⟩,
    rcases h i₃ h₁₃ with ⟨j₃, h₃⟩,
    have hj₂₃ : j₂ ≠ j₃,
    { intro he,
      rw [he, h₃] at h₂,
      exact h₂₃.symm (hpi h₂) },
    exact ⟨i₁, i₂, i₃, j₂, j₃, h₁₂, h₁₃, h₂₃, h₁₂₃, h₁, hj₂₃, h₂, h₃⟩ },
  { right,
    have hs := set.subset_diff_singleton hps h,
    rw set.insert_diff_self_of_not_mem ho at hs,
    refine set.eq_of_subset_of_card_le hs _,
    rw [set.card_range_of_injective hpi,
        set.card_range_of_injective (injective_of_affine_independent t.independent)] }
end

/-- For any three points in an orthocentric system generated by
triangle `t`, there is a point in the subspace spanned by the triangle
from which the distance of all those three points equals the
circumradius. -/
lemma exists_dist_eq_circumradius_of_subset_insert_orthocenter {t : triangle ℝ P}
  (ho : t.orthocenter ∉ set.range t.points) {p : fin 3 → P}
  (hps : set.range p ⊆ insert t.orthocenter (set.range t.points)) (hpi : function.injective p) :
  ∃ c ∈ affine_span ℝ (set.range t.points), ∀ p₁ ∈ set.range p, dist p₁ c = t.circumradius :=
begin
  rcases exists_of_range_subset_orthocentric_system ho hps hpi with
    ⟨i₁, i₂, i₃, j₂, j₃, h₁₂, h₁₃, h₂₃, h₁₂₃, h₁, hj₂₃, h₂, h₃⟩ | hs,
  { use [reflection (affine_span ℝ (t.points '' {j₂, j₃})) t.circumcenter,
         reflection_mem_of_le_of_mem (affine_span_mono ℝ (set.image_subset_range _ _))
                                     t.circumcenter_mem_affine_span],
    intros p₁ hp₁,
    rcases hp₁ with ⟨i, rfl⟩,
    replace h₁₂₃ := h₁₂₃ i,
    repeat { cases h₁₂₃ },
    { rw h₁,
      exact triangle.dist_orthocenter_reflection_circumcenter t hj₂₃ },
    { rw [←h₂,
          dist_reflection_eq_of_mem _
            (mem_affine_span ℝ (set.mem_image_of_mem _ (set.mem_insert _ _)))],
      exact t.dist_circumcenter_eq_circumradius _ },
    { rw [←h₃,
          dist_reflection_eq_of_mem _
            (mem_affine_span ℝ (set.mem_image_of_mem _
              (set.mem_insert_of_mem _ (set.mem_singleton _))))],
      exact t.dist_circumcenter_eq_circumradius _ } },
  { use [t.circumcenter, t.circumcenter_mem_affine_span],
    intros p₁ hp₁,
    rw hs at hp₁,
    rcases hp₁ with ⟨i, rfl⟩,
    exact t.dist_circumcenter_eq_circumradius _ }
end

/-- Any three points in an orthocentric system are affinely
independent. -/
lemma affine_independent_of_orthocentric_system {s : set P} (ho : orthocentric_system s)
    {p : fin 3 → P} (hps : set.range p ⊆ s) (hpi : function.injective p) :
  affine_independent ℝ p :=
begin
  rcases ho with ⟨t, hto, hst⟩,
  rw hst at hps,
  rcases exists_dist_eq_circumradius_of_subset_insert_orthocenter hto hps hpi with ⟨c, hcs, hc⟩,
  exact affine_independent_of_cospherical ⟨c, t.circumradius, hc⟩ set.subset.rfl hpi
end

/-- Any three points in an orthocentric system span the same subspace
as the whole orthocentric system. -/
lemma affine_span_of_orthocentric_system {s : set P} (ho : orthocentric_system s)
    {p : fin 3 → P} (hps : set.range p ⊆ s) (hpi : function.injective p) :
  affine_span ℝ (set.range p) = affine_span ℝ s :=
begin
  have ha := affine_independent_of_orthocentric_system ho hps hpi,
  rcases ho with ⟨t, hto, hts⟩,
  have hs : affine_span ℝ s = affine_span ℝ (set.range t.points),
  { rw [hts, affine_span_insert_eq_affine_span ℝ t.orthocenter_mem_affine_span] },
  refine ext_of_direction_eq _
    ⟨p 0, mem_affine_span ℝ (set.mem_range_self _), mem_affine_span ℝ (hps (set.mem_range_self _))⟩,
  have hfd : finite_dimensional ℝ (affine_span ℝ s).direction, { rw hs, apply_instance },
  haveI := hfd,
  refine eq_of_le_of_findim_eq (direction_le (affine_span_mono ℝ hps)) _,
  rw [hs, direction_affine_span, direction_affine_span,
      findim_vector_span_of_affine_independent ha (fintype.card_fin _),
      findim_vector_span_of_affine_independent t.independent (fintype.card_fin _)]
end

/-- All triangles in an orthocentric system have the same
circumradius. -/
lemma exists_circumradius_eq_of_orthocentric_system {s : set P} (ho : orthocentric_system s) :
  ∃ r : ℝ, ∀ t : triangle ℝ P, set.range t.points ⊆ s → t.circumradius = r :=
begin
  rcases ho with ⟨t, hto, hts⟩,
  use t.circumradius,
  intros t₂ ht₂,
  have ht₂s := ht₂,
  rw hts at ht₂,
  rcases exists_dist_eq_circumradius_of_subset_insert_orthocenter hto ht₂
    (injective_of_affine_independent t₂.independent) with ⟨c, hc, h⟩,
  rw set.forall_range_iff at h,
  have hs : set.range t.points ⊆ s,
  { rw hts,
    exact set.subset_insert _ _ },
  rw [affine_span_of_orthocentric_system ⟨t, hto, hts⟩ hs
        (injective_of_affine_independent t.independent),
      ←affine_span_of_orthocentric_system ⟨t, hto, hts⟩ ht₂s
        (injective_of_affine_independent t₂.independent)] at hc,
  exact (t₂.eq_circumradius_of_dist_eq hc h).symm
end

/-- The affine span of the orthocenter and a vertex is contained in
the altitude. -/
lemma affine_span_orthocenter_point_le_altitude (t : triangle ℝ P) (i : fin 3) :
  affine_span ℝ {t.orthocenter, t.points i} ≤ t.altitude i :=
begin
  refine span_points_subset_coe_of_subset_coe _,
  rw [set.insert_subset, set.singleton_subset_iff],
  exact ⟨t.orthocenter_mem_altitude, t.mem_altitude i⟩
end

/-- Suppose we are given a triangle `t₁`, and replace one of its
vertices by its orthocenter, yielding triangle `t₂` (with vertices not
necessarily listed in the same order).  Then an altitude of `t₂` from
a vertex that was not replaced is the corresponding side of `t₁`. -/
lemma altitude_replace_orthocenter_eq_affine_span {t₁ t₂ : triangle ℝ P} {i₁ i₂ i₃ j₁ j₂ j₃ : fin 3}
    (hi₁₂ : i₁ ≠ i₂) (hi₁₃ : i₁ ≠ i₃) (hi₂₃ : i₂ ≠ i₃) (hj₁₂ : j₁ ≠ j₂) (hj₁₃ : j₁ ≠ j₃)
    (hj₂₃ : j₂ ≠ j₃) (h₁ : t₂.points j₁ = t₁.orthocenter) (h₂ : t₂.points j₂ = t₁.points i₂)
    (h₃ : t₂.points j₃ = t₁.points i₃) :
  t₂.altitude j₂ = affine_span ℝ {t₁.points i₁, t₁.points i₂} :=
begin
  symmetry,
  rw [←h₂, t₂.affine_span_insert_singleton_eq_altitude_iff],
  rw [h₂],
  use (injective_of_affine_independent t₁.independent).ne hi₁₂,
  have he : affine_span ℝ (set.range t₂.points) = affine_span ℝ (set.range t₁.points),
  { refine ext_of_direction_eq _
      ⟨t₁.points i₃, mem_affine_span ℝ ⟨j₃, h₃⟩, mem_affine_span ℝ (set.mem_range_self _)⟩,
    refine eq_of_le_of_findim_eq (direction_le (span_points_subset_coe_of_subset_coe _)) _,
    { have hu : (finset.univ : finset (fin 3)) = {j₁, j₂, j₃}, { clear h₁ h₂ h₃, dec_trivial! },
      rw [←set.image_univ, ←finset.coe_univ, hu, finset.coe_insert, finset.coe_insert,
          finset.coe_singleton, set.image_insert_eq, set.image_insert_eq, set.image_singleton,
          h₁, h₂, h₃, set.insert_subset, set.insert_subset, set.singleton_subset_iff],
      exact ⟨t₁.orthocenter_mem_affine_span,
             mem_affine_span ℝ (set.mem_range_self _),
             mem_affine_span ℝ (set.mem_range_self _)⟩ },
    { rw [direction_affine_span, direction_affine_span,
          findim_vector_span_of_affine_independent t₁.independent (fintype.card_fin _),
          findim_vector_span_of_affine_independent t₂.independent (fintype.card_fin _)] } },
  rw he,
  use mem_affine_span ℝ (set.mem_range_self _),
  have hu : finset.univ.erase j₂ = {j₁, j₃}, { clear h₁ h₂ h₃, dec_trivial! },
  rw [hu, finset.coe_insert, finset.coe_singleton, set.image_insert_eq, set.image_singleton,
      h₁, h₃],
  have hle : (t₁.altitude i₃).direction.orthogonal ≤
    (affine_span ℝ ({t₁.orthocenter, t₁.points i₃} : set P)).direction.orthogonal :=
      submodule.orthogonal_le (direction_le (affine_span_orthocenter_point_le_altitude _ _)),
  refine hle ((t₁.vector_span_le_altitude_direction_orthogonal i₃) _),
  have hui : finset.univ.erase i₃ = {i₁, i₂}, { clear hle h₂ h₃, dec_trivial! },
  rw [hui, finset.coe_insert, finset.coe_singleton, set.image_insert_eq, set.image_singleton],
  refine vsub_mem_vector_span ℝ (set.mem_insert _ _)
    (set.mem_insert_of_mem _ (set.mem_singleton _))
end

/-- Suppose we are given a triangle `t₁`, and replace one of its
vertices by its orthocenter, yielding triangle `t₂` (with vertices not
necessarily listed in the same order).  Then the orthocenter of `t₂`
is the vertex of `t₁` that was replaced. -/
lemma orthocenter_replace_orthocenter_eq_point {t₁ t₂ : triangle ℝ P} {i₁ i₂ i₃ j₁ j₂ j₃ : fin 3}
    (hi₁₂ : i₁ ≠ i₂) (hi₁₃ : i₁ ≠ i₃) (hi₂₃ : i₂ ≠ i₃) (hj₁₂ : j₁ ≠ j₂) (hj₁₃ : j₁ ≠ j₃)
    (hj₂₃ : j₂ ≠ j₃) (h₁ : t₂.points j₁ = t₁.orthocenter) (h₂ : t₂.points j₂ = t₁.points i₂)
    (h₃ : t₂.points j₃ = t₁.points i₃) :
  t₂.orthocenter = t₁.points i₁ :=
begin
  refine (triangle.eq_orthocenter_of_forall_mem_altitude hj₂₃ _ _).symm,
  { rw altitude_replace_orthocenter_eq_affine_span hi₁₂ hi₁₃ hi₂₃ hj₁₂ hj₁₃ hj₂₃ h₁ h₂ h₃,
    exact mem_affine_span ℝ (set.mem_insert _ _) },
  { rw altitude_replace_orthocenter_eq_affine_span hi₁₃ hi₁₂ hi₂₃.symm hj₁₃ hj₁₂ hj₂₃.symm h₁ h₃ h₂,
    exact mem_affine_span ℝ (set.mem_insert _ _) }
end

/-- Given any triangle in an orthocentric system, the fourth point is
its orthocenter. -/
lemma eq_insert_orthocenter_of_orthocentric_system {s : set P} (ho : orthocentric_system s)
    {t : triangle ℝ P} (ht : set.range t.points ⊆ s) :
  s = insert t.orthocenter (set.range t.points) :=
begin
  rcases ho with ⟨t₀, ht₀o, ht₀s⟩,
  rw ht₀s at ht,
  rcases exists_of_range_subset_orthocentric_system ht₀o ht
    (injective_of_affine_independent t.independent) with
    ⟨i₁, i₂, i₃, j₂, j₃, h₁₂, h₁₃, h₂₃, h₁₂₃, h₁, hj₂₃, h₂, h₃⟩ | hs,
  { obtain ⟨j₁, hj₁₂, hj₁₃, hj₁₂₃⟩ :
      ∃ j₁ : fin 3, j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ ∀ j : fin 3, j = j₁ ∨ j = j₂ ∨ j = j₃,
    { clear h₂ h₃, dec_trivial! },
    suffices h : t₀.points j₁ = t.orthocenter,
    { have hui : (set.univ : set (fin 3)) = {i₁, i₂, i₃}, { ext x, simpa using h₁₂₃ x },
      have huj : (set.univ : set (fin 3)) = {j₁, j₂, j₃}, { ext x, simpa using hj₁₂₃ x },
      rw [←h, ht₀s, ←set.image_univ, huj, ←set.image_univ, hui],
      simp_rw [set.image_insert_eq, set.image_singleton, h₁, ←h₂, ←h₃],
      rw set.insert_comm },
    exact (orthocenter_replace_orthocenter_eq_point
      hj₁₂ hj₁₃ hj₂₃ h₁₂ h₁₃ h₂₃ h₁ h₂.symm h₃.symm).symm },
  { rw hs,
    convert ht₀s using 2,
    exact triangle.orthocenter_eq_of_range_eq hs }
end

end euclidean_geometry

-- Content specific to this problem starts here.

open affine affine_subspace finite_dimensional euclidean_geometry

variables {V : Type*} {P : Type*} [inner_product_space V] [metric_space P]
    [normed_add_torsor V P]

-- Properties of sets of points in the problem.

def at_least_four_points (s : set P) : Prop := 4 ≤ cardinal.mk s

include V

def no_three_points_collinear (s : set P) : Prop :=
∀ p : fin 3 → P, function.injective p → set.range p ⊆ s → ¬ collinear ℝ (set.range p)

lemma no_three_points_collinear_iff (s : set P) :
  no_three_points_collinear s ↔
    ∀ p : fin 3 → P, function.injective p → set.range p ⊆ s → affine_independent ℝ p :=
begin
  simp_rw affine_independent_iff_not_collinear,
  refl
end

def same_circumradius (s : set P) : Prop :=
∃ r : ℝ, ∀ t : triangle ℝ P, set.range t.points ⊆ s → t.circumradius = r

-- The description given in the problem.
def p2_problem_desc (s : set P) : Prop :=
at_least_four_points s ∧ no_three_points_collinear s ∧ same_circumradius s

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
  rw no_three_points_collinear_iff at hn3,
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
  have ho2 := affine.triangle.dist_orthocenter_reflection_circumcenter_finset t0 h12,
  have ho3 := affine.triangle.dist_orthocenter_reflection_circumcenter_finset t0 h13,
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
      { rw no_three_points_collinear_iff,
        exact λ p hpi hps, affine_independent_of_cospherical hc hps hpi },
      { exact exists_circumradius_eq_of_cospherical hd2 hc } },
    { split,
      { rw no_three_points_collinear_iff,
        exact λ p hpi hps, affine_independent_of_orthocentric_system ho hps hpi },
      { exact exists_circumradius_eq_of_orthocentric_system ho } } }
end
