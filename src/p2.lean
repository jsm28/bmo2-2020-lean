-- BMO2 2020 problem 2.

-- Choices made for formalization: the original problem refers to
-- "collections", which we take as meaning sets.

import data.matrix.notation
import geometry.euclidean

noncomputable theory
open_locale big_operators
open_locale classical
open_locale real_inner_product_space

-- For linear_algebra.affine_space.basic.

section affine

variables (k : Type*) {V : Type*} {P : Type*} [ring k] [add_comm_group V] [module k V]
          [affine_space V P]
variables {ι : Type*}
include V

/-- The `vector_span` of an indexed family is the span of the pairwise
subtractions with a given point on the left, excluding the subtraction
of that point from itself. -/
lemma vector_span_range_eq_span_range_vsub_left_ne (p : ι → P) (i₀ : ι) :
  vector_span k (set.range p) = submodule.span k (set.range (λ (i : {x // x ≠ i₀}), p i₀ -ᵥ p i)) :=
begin
  rw [←set.image_univ, vector_span_image_eq_span_vsub_set_left_ne k _ (set.mem_univ i₀)],
  congr' with v,
  simp only [set.mem_range, set.mem_image, set.mem_diff, set.mem_singleton_iff, subtype.exists,
             subtype.coe_mk],
  split,
  { rintros ⟨x, ⟨i₁, ⟨⟨hi₁u, hi₁⟩, rfl⟩⟩, hv⟩,
    exact ⟨i₁, hi₁, hv⟩ },
  { exact λ ⟨i₁, hi₁, hv⟩, ⟨p i₁, ⟨i₁, ⟨set.mem_univ _, hi₁⟩, rfl⟩, hv⟩ }
end

/-- The `vector_span` of an indexed family is the span of the pairwise
subtractions with a given point on the right, excluding the subtraction
of that point from itself. -/
lemma vector_span_range_eq_span_range_vsub_right_ne (p : ι → P) (i₀ : ι) :
  vector_span k (set.range p) = submodule.span k (set.range (λ (i : {x // x ≠ i₀}), p i -ᵥ p i₀)) :=
begin
  rw [←set.image_univ, vector_span_image_eq_span_vsub_set_right_ne k _ (set.mem_univ i₀)],
  congr' with v,
  simp only [set.mem_range, set.mem_image, set.mem_diff, set.mem_singleton_iff, subtype.exists,
             subtype.coe_mk],
  split,
  { rintros ⟨x, ⟨i₁, ⟨⟨hi₁u, hi₁⟩, rfl⟩⟩, hv⟩,
    exact ⟨i₁, hi₁, hv⟩ },
  { exact λ ⟨i₁, hi₁, hv⟩, ⟨p i₁, ⟨i₁, ⟨set.mem_univ _, hi₁⟩, rfl⟩, hv⟩ }
end

end affine

-- For linear_algebra.affine_space.finite_dimensional.

section affine

variables {k : Type*} {V : Type*} {P : Type*} [field k] [add_comm_group V] [module k V]
          [affine_space V P]
variables {ι : Type*}
include V

open finite_dimensional

variables (k)

/-- The `vector_span` of `n + 1` points in an indexed family has
dimension at most `n`. -/
lemma findim_vector_span_image_finset_le (p : ι → P) (s : finset ι) {n : ℕ}
  (hc : finset.card s = n + 1) : findim k (vector_span k (p '' ↑s)) ≤ n :=
begin
  have hn : (p '' ↑s).nonempty,
  { simp [hc, ←finset.card_pos] },
  rcases hn with ⟨p₁, hp₁⟩,
  rw [vector_span_eq_span_vsub_set_right_ne k hp₁],
  have hfp₁ : (p '' ↑s \ {p₁}).finite :=
    ((finset.finite_to_set _).image _).subset (set.diff_subset _ _),
  haveI := hfp₁.fintype,
  have hf : ((λ p, p -ᵥ p₁) '' (p '' ↑s \ {p₁})).finite := hfp₁.image _,
  haveI := hf.fintype,
  convert le_trans (findim_span_le_card ((λ p, p -ᵥ p₁) '' (p '' ↑s \ {p₁}))) _,
  have hm : p₁ ∉ p '' ↑s \ {p₁}, by simp,
  haveI := set.fintype_insert' (p '' ↑s \ {p₁}) hm,
  rw [set.to_finset_card, set.card_image_of_injective (p '' ↑s \ {p₁}) (vsub_left_injective p₁),
      ←add_le_add_iff_right 1, ←set.card_fintype_insert' _ hm],
  have h : fintype.card (↑(s.image p) : set P) ≤ n + 1,
  { rw [fintype.card_coe, ←hc],
    exact finset.card_image_le },
  convert h,
  simp [hp₁]
end

/-- The `vector_span` of an indexed family of `n + 1` points has
dimension at most `n`. -/
lemma findim_vector_span_range_le [fintype ι] (p : ι → P) {n : ℕ}
  (hc : fintype.card ι = n + 1) : findim k (vector_span k (set.range p)) ≤ n :=
begin
  rw [←set.image_univ, ←finset.coe_univ],
  rw ←finset.card_univ at hc,
  exact findim_vector_span_image_finset_le _ _ _ hc
end

/-- `n + 1` points are affinely independent if and only if their
`vector_span` has dimension `n`. -/
lemma affine_independent_iff_findim_vector_span_eq [fintype ι] (p : ι → P) {n : ℕ}
  (hc : fintype.card ι = n + 1) :
  affine_independent k p ↔ findim k (vector_span k (set.range p)) = n :=
begin
  have hn : nonempty ι, by simp [←fintype.card_pos_iff, hc],
  cases hn with i₁,
  rw [affine_independent_iff_linear_independent_vsub _ _ i₁,
      linear_independent_iff_card_eq_findim_span, eq_comm,
      vector_span_range_eq_span_range_vsub_right_ne k p i₁],
  congr',
  rw ←finset.card_univ at hc,
  rw fintype.subtype_card,
  simp [finset.filter_ne', finset.card_erase_of_mem, hc]
end

/-- `n + 1` points are affinely independent if and only if their
`vector_span` has dimension at least `n`. -/
lemma affine_independent_iff_le_findim_vector_span [fintype ι] (p : ι → P) {n : ℕ}
  (hc : fintype.card ι = n + 1) :
  affine_independent k p ↔ n ≤ findim k (vector_span k (set.range p)) :=
begin
  rw affine_independent_iff_findim_vector_span_eq k p hc,
  split,
  { rintro rfl,
    refl },
  { exact λ hle, le_antisymm (findim_vector_span_range_le k p hc) hle }
end

/-- `n + 2` points are affinely independent if and only if their
`vector_span` does not have dimension at most `n`. -/
lemma affine_independent_iff_not_findim_vector_span_le [fintype ι] (p : ι → P) {n : ℕ}
  (hc : fintype.card ι = n + 2) :
  affine_independent k p ↔ ¬ findim k (vector_span k (set.range p)) ≤ n :=
by rw [affine_independent_iff_le_findim_vector_span k p hc, ←nat.lt_iff_add_one_le, lt_iff_not_ge]

/-- `n + 2` points have a `vector_span` with dimension at most `n` if
and only if they are not affinely independent. -/
lemma findim_vector_span_le_iff_not_affine_independent [fintype ι] (p : ι → P) {n : ℕ}
  (hc : fintype.card ι = n + 2) :
  findim k (vector_span k (set.range p)) ≤ n ↔ ¬ affine_independent k p :=
(not_iff_comm.1 (affine_independent_iff_not_findim_vector_span_le k p hc).symm).symm

end affine

namespace set

variables {α : Type*}

/-- `s`, coerced to a type, is a subsingleton type if and only if `s`
is a subsingleton set. -/
@[simp] lemma subsingleton_coe (s : set α) : subsingleton s ↔ s.subsingleton :=
begin
  split,
  { refine λ h, (λ a ha b hb, _),
    rw set.set_coe_eq_subtype at h,
    haveI := h,
    exact subtype.ext_iff.1 (subsingleton.elim ⟨a, ha⟩ ⟨b, hb⟩) },
  { exact λ h, subsingleton.intro (λ a b, subtype.ext (h a.property b.property)) }
end

end set

section dim_one

variables (K : Type*) (V : Type*) [field K] [add_comm_group V] [vector_space K V]

/-- A vector space has dimension at most `1` if and only if there is a
single vector of which all vectors are multiples. -/
lemma dim_le_one_iff : vector_space.dim K V ≤ 1 ↔ ∃ v₀ : V, ∀ v, ∃ r : K, r • v₀ = v :=
begin
  obtain ⟨b, h⟩ := exists_is_basis K V,
  split,
  { intro hd,
    rw [←is_basis.mk_eq_dim'' h, cardinal.le_one_iff_subsingleton, set.subsingleton_coe] at hd,
    rcases set.eq_empty_or_nonempty b with rfl | ⟨⟨v₀, hv₀⟩⟩,
    { use 0,
      have h' : ∀ v : V, v = 0, { simpa [submodule.eq_bot_iff] using h.2.symm },
      intro v,
      simp [h' v] },
    { use v₀,
      have h' : submodule.span K {v₀} = ⊤, { simpa [hd.eq_singleton_of_mem hv₀] using h.2 },
      intro v,
      have hv : v ∈ (⊤ : submodule K V) := submodule.mem_top,
      rwa [←h', submodule.mem_span_singleton] at hv } },
  { rintros ⟨v₀, hv₀⟩,
    have h : submodule.span K ({v₀} : set V) = ⊤,
    { ext, simp [submodule.mem_span_singleton, hv₀] },
    rw [←dim_top, ←h],
    convert dim_span_le _,
    simp }
end

/-- A submodule has dimension at most `1` if and only if there is a
single vector of which all vectors are multiples. -/
lemma dim_submodule_le_one_iff (s : submodule K V) :
  vector_space.dim K s ≤ 1 ↔ ∃ v₀ ∈ s, ∀ v ∈ s, ∃ r : K, r • v₀ = v :=
begin
  rw dim_le_one_iff,
  split,
  { rintro ⟨⟨v₀, hv₀⟩, h⟩,
    use [v₀, hv₀],
    intros v hv,
    obtain ⟨r, hr⟩ := h ⟨v, hv⟩,
    use r,
    simp_rw [subtype.ext_iff, submodule.coe_smul, submodule.coe_mk] at hr,
    exact hr },
  { rintro ⟨v₀, hv₀, h⟩,
    use ⟨v₀, hv₀⟩,
    rintro ⟨v, hv⟩,
    obtain ⟨r, hr⟩ := h v hv,
    use r,
    simp_rw [subtype.ext_iff, submodule.coe_smul, submodule.coe_mk],
    exact hr }
end

end dim_one

section collinear

variables (k : Type*) {V : Type*} {P : Type*} [field k] [add_comm_group V] [module k V]
variables [affine_space V P]
include V

open vector_space finite_dimensional

/-- A set of points is collinear if their `vector_span` has dimension
at most `1`. -/
def collinear (s : set P) : Prop := dim k (vector_span k s) ≤ 1

/-- The definition of `collinear`. -/
lemma collinear_iff_dim_le_one (s : set P) : collinear k s ↔ dim k (vector_span k s) ≤ 1 :=
iff.rfl

/-- A set of points, whose `vector_span` is finite-dimensional, is
collinear if and only if their `vector_span` has dimension at most
`1`. -/
lemma collinear_iff_findim_le_one (s : set P) [finite_dimensional k (vector_span k s)] :
  collinear k s ↔ findim k (vector_span k s) ≤ 1 :=
begin
  have h := collinear_iff_dim_le_one k s,
  rw ←findim_eq_dim at h,
  exact_mod_cast h
end

variables (P)

/-- The empty set is collinear. -/
lemma collinear_empty : collinear k (∅ : set P) :=
begin
  rw [collinear_iff_dim_le_one, vector_span_empty],
  simp
end

variables {P}

/-- A single point is collinear. -/
lemma collinear_singleton (p : P) : collinear k ({p} : set P) :=
begin
  rw [collinear_iff_dim_le_one, vector_span_singleton],
  simp
end

-- TODO: split out more lemmas.  E.g. mem_span_of_mem /
-- smul_mem_span_of_mem / span_singleton_smul_eq etc.

/-- Given a point `p₀` in a set of points, that set is collinear if and
only if the points can all be expressed as multiples of the same
vector, added to `p₀`. -/
lemma collinear_iff_of_mem {s : set P} {p₀ : P} (h : p₀ ∈ s) :
  collinear k s ↔ ∃ v : V, ∀ p ∈ s, ∃ r : k, p = r • v +ᵥ p₀ :=
begin
  rw [collinear_iff_dim_le_one, dim_submodule_le_one_iff],
  split,
  { rintro ⟨v₀, hv₀, hv⟩,
    use v₀,
    intros p hp,
    obtain ⟨r, hr⟩ := hv (p -ᵥ p₀) (vsub_mem_vector_span k hp h),
    use r,
    rw eq_vadd_iff_vsub_eq,
    exact hr.symm },
  { rintro ⟨v, hp₀v⟩,
    by_cases hz : ∃ p₁ ∈ s, p₁ ≠ p₀,
    { rcases hz with ⟨p₁, hp₁, hne⟩,
      use [p₁ -ᵥ p₀, vsub_mem_vector_span k hp₁ h],
      intros v₀ hv₀,
      have hp₀v' : ∀ p ∈ s, ∃ r : k, p -ᵥ p₀ = r • v,
      { intros p hp,
        rcases hp₀v p hp with ⟨r, hr⟩,
        use r,
        rw ←eq_vadd_iff_vsub_eq,
        exact hr },
      have hs : vector_span k s = submodule.span k {v},
      { rw vector_span_eq_span_vsub_set_right k h,
        refine le_antisymm _ _,
        { rw submodule.span_le,
          intros v₁ hv₁,
          rw set.mem_image at hv₁,
          rcases hv₁ with ⟨p, hp, rfl⟩,
          rcases hp₀v' p hp with ⟨r, hr⟩,
          rw [hr, submodule.mem_coe, submodule.mem_span_singleton],
          use r },
        { have he : submodule.span k ({v} : set V) = submodule.span k {p₁ -ᵥ p₀},
          { rcases hp₀v' p₁ hp₁ with ⟨r, hr⟩,
            ext x,
            simp_rw submodule.mem_span_singleton,
            split,
            { rintro ⟨r', rfl⟩,
              use r' / r,
              have h0 : r ≠ 0,
              { rintro rfl,
                rw [zero_smul, @vsub_eq_zero_iff_eq V] at hr,
                simpa [hr] using hne },
              rw [hr, smul_smul, div_mul_cancel _ h0] },
            { rintro ⟨r', rfl⟩,
              use r' * r,
              rw [←smul_smul, hr] } },
          rw he,
          refine submodule.span_mono _,
          simp [hp₁] } },
      rw [hs, submodule.mem_span_singleton] at hv₀,
      rcases hv₀ with ⟨r', rfl⟩,
      rcases hp₀v' p₁ hp₁ with ⟨r'', hr''⟩,
      use r' / r'',
      have h0 : r'' ≠ 0,
      { rintro rfl,
        rw [zero_smul, @vsub_eq_zero_iff_eq V] at hr'',
        simpa [hr''] using hne },
      rw [hr'', smul_smul, div_mul_cancel _ h0] },
    { push_neg at hz,
      have hs : s = {p₀},
      { ext x,
        split,
        { exact hz x },
        { intro hx,
          rw set.mem_singleton_iff at hx,
          rwa hx } },
      subst hs,
      use [0, submodule.zero_mem _],
      intros v hv,
      use 0,
      symmetry,
      simpa using hv } }
end

/-- A set of points is collinear if and only if they can all be
expressed as multiples of the same vector, added to the same base
point. -/
lemma collinear_iff_exists_forall_eq_smul_vadd (s : set P) :
  collinear k s ↔ ∃ (p₀ : P) (v : V), ∀ p ∈ s, ∃ r : k, p = r • v +ᵥ p₀ :=
begin
  rcases set.eq_empty_or_nonempty s with rfl | ⟨⟨p₁, hp₁⟩⟩,
  { simp [collinear_empty] },
  { rw collinear_iff_of_mem k hp₁,
    split,
    { exact λ h, ⟨p₁, h⟩ },
    { rintros ⟨p, v, hv⟩,
      use v,
      intros p₂ hp₂,
      rcases hv p₂ hp₂ with ⟨r, rfl⟩,
      rcases hv p₁ hp₁ with ⟨r₁, rfl⟩,
      use r - r₁,
      simp [vadd_assoc, ←add_smul] } }
end

/-- Two points are collinear. -/
lemma collinear_insert_singleton (p₁ p₂ : P) : collinear k ({p₁, p₂} : set P) :=
begin
  rw collinear_iff_exists_forall_eq_smul_vadd,
  use [p₁, p₂ -ᵥ p₁],
  intros p hp,
  rw [set.mem_insert_iff, set.mem_singleton_iff] at hp,
  cases hp,
  { use 0,
    simp [hp] },
  { use 1,
    simp [hp] }
end

/-- Three points are affinely independent if and only if they are not
collinear. -/
lemma affine_independent_iff_not_collinear (p : fin 3 → P) :
  affine_independent k p ↔ ¬ collinear k (set.range p) :=
by rw [collinear_iff_findim_le_one,
       affine_independent_iff_not_findim_vector_span_le k p (fintype.card_fin 3)]

/-- Three points are collinear if and only if they are not affinely
independent. -/
lemma collinear_iff_not_affine_independent (p : fin 3 → P) :
  collinear k (set.range p) ↔ ¬ affine_independent k p :=
by rw [collinear_iff_findim_le_one,
       findim_vector_span_le_iff_not_affine_independent k p (fintype.card_fin 3)]

end collinear

-- Geometrical definitions and results that should go in mathlib in
-- some form (possibly more general).

namespace euclidean_geometry

open affine affine_subspace finite_dimensional euclidean_geometry

variables {V : Type*} {P : Type*} [inner_product_space ℝ V] [metric_space P]
    [normed_add_torsor V P]

include V

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
  have hfn0' : ∀ i, i ≠ 0 → f i = (-2) * ⟪v, (p 0 -ᵥ c)⟫ / ⟪v, v⟫,
  { intros i hi,
    have hsdi := hsd i,
    simpa [hfn0, hi] using hsdi },
  have hf12 : f 1 = f 2, { rw [hfn0' 1 dec_trivial, hfn0' 2 dec_trivial] },
  exact (dec_trivial : (1 : fin 3) ≠ 2) (hfi hf12)
end

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
    exact (triangle.orthocenter_replace_orthocenter_eq_point
      hj₁₂ hj₁₃ hj₂₃ h₁₂ h₁₃ h₂₃ h₁ h₂.symm h₃.symm).symm },
  { rw hs,
    convert ht₀s using 2,
    exact triangle.orthocenter_eq_of_range_eq hs }
end

end euclidean_geometry

-- Content specific to this problem starts here.

open affine affine_subspace finite_dimensional euclidean_geometry

variables {V : Type*} {P : Type*} [inner_product_space ℝ V] [metric_space P]
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
