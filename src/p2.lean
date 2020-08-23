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

import geometry.euclidean

import orthocenter

noncomputable theory
open_locale classical

namespace affine_subspace

variables {k : Type*} {V : Type*} {P : Type*} [ring k] [add_comm_group V] [module k V]
          [affine_space V P]
include V

-- Results to add to affine_space/basic.lean in mathlib.

/-- A nonempty affine subspace is `⊤` if and only if its direction is
`⊤`. -/
@[simp] lemma direction_eq_top_iff_of_nonempty {s : affine_subspace k P}
    (h : (s : set P).nonempty) :
  s.direction = ⊤ ↔ s = ⊤ :=
begin
  split,
  { intro hd,
    rw ←direction_top k V P at hd,
    refine ext_of_direction_eq hd _,
    simp [h] },
  { rintro rfl,
    simp }
end

end affine_subspace

section indep

-- Results to add to affine_space/independent.lean in mathlib.

variables {k : Type*} {V : Type*} {P : Type*} [ring k] [add_comm_group V] [module k V]
variables [affine_space V P] {ι : Type*}
include V

/-- An affinely independent family is injective, if the underlying
ring is nontrivial. -/
lemma injective_of_affine_independent [nontrivial k] {p : ι → P} (ha : affine_independent k p) :
  function.injective p :=
begin
  intros i₁ i₂ he,
  rw affine_independent_iff_indicator_eq_of_affine_combination_eq k p at ha,
  have hp : ({i₁} : finset ι).affine_combination p (function.const ι (1 : k)) =
    ({i₂} : finset ι).affine_combination p (function.const ι (1 : k)),
  { rw [({i₁} : finset ι).affine_combination_of_eq_one_of_eq_zero
          (function.const ι (1 : k))
          _
          (finset.mem_singleton_self i₁)
          rfl
          (λ i hi hin, false.elim (hin (finset.mem_singleton.1 hi))),
        ({i₂} : finset ι).affine_combination_of_eq_one_of_eq_zero
          (function.const ι (1 : k))
          _
          (finset.mem_singleton_self i₂)
          rfl
          (λ i hi hin, false.elim (hin (finset.mem_singleton.1 hi)))],
    exact he },
  replace ha := ha {i₁} {i₂} (function.const ι 1) (function.const ι 1)
    finset.sum_singleton finset.sum_singleton hp,
  simp_rw finset.coe_singleton at ha,
  have ha' : ({i₁} : set ι).indicator (function.const ι (1 : k)) i₁ =
    ({i₂} : set ι).indicator (function.const ι (1 : k)) i₁,
  { rw ha },
  simp only [set.mem_singleton, set.indicator_of_mem] at ha',
  change 1 = ({i₂} : set ι).indicator (function.const ι (1 : k)) i₁ at ha',
  have haz : ({i₂} : set ι).indicator (function.const ι (1 : k)) i₁ ≠ 0,
  { rw ←ha',
    exact one_ne_zero },
  have hm := set.mem_of_indicator_ne_zero haz,
  rw set.mem_singleton_iff at hm,
  exact hm
end

/-- If an indexed family of points is affinely independent, so is the
corresponding set of points. -/
lemma affine_independent_set_of_affine_independent {p : ι → P} (ha : affine_independent k p) :
  affine_independent k (λ x, x : set.range p → P) :=
begin
  let f : set.range p → ι := λ x, x.property.some,
  have hf : ∀ x, p (f x) = x := λ x, x.property.some_spec,
  let fe : set.range p ↪ ι := ⟨f, λ x₁ x₂ he, subtype.ext (hf x₁ ▸ hf x₂ ▸ he ▸ rfl)⟩,
  convert affine_independent_embedding_of_affine_independent fe ha,
  ext,
  simp [hf]
end

end indep

section affine

-- Results to add to affine_space/finite_dimensional.lean in mathlib.

variables {k : Type*} {V : Type*} {P : Type*} [field k] [add_comm_group V] [module k V]
          [affine_space V P]
variables {ι : Type*}
include V

open finite_dimensional

/-- The `vector_span` of a finite affinely independent family has
dimension one less than its cardinality. -/
lemma findim_vector_span_of_affine_independent [fintype ι] {p : ι → P}
    (hi : affine_independent k p) {n : ℕ} (hc : fintype.card ι = n + 1) :
  findim k (vector_span k (set.range p)) = n :=
begin
  have hi' := affine_independent_set_of_affine_independent hi,
  have hc' : fintype.card (set.range p) = n + 1,
  { rw set.card_range_of_injective (injective_of_affine_independent hi),
    exact hc },
  have hn : (set.range p).nonempty,
  { refine set.range_nonempty_iff_nonempty.2 (fintype.card_pos_iff.1 _),
    simp [hc] },
  rcases hn with ⟨p₁, hp₁⟩,
  rw affine_independent_set_iff_linear_independent_vsub k hp₁ at hi',
  haveI : fintype ((λ (p : P), p -ᵥ p₁) '' (set.range p \ {p₁})) := sorry,
  rw [vector_span_eq_span_vsub_set_right_ne k hp₁, findim_span_set_eq_card _ hi'],
  sorry
end

/-- The `vector_span` of a finite affinely independent family whose
cardinality is one more than that of the finite-dimensional space is
`⊤`. -/
lemma vector_span_eq_top_of_affine_independent_of_card_eq_findim_add_one [finite_dimensional k V]
    [fintype ι] {p : ι → P} (hi : affine_independent k p)
    (hc : fintype.card ι = findim k V + 1) :
  vector_span k (set.range p) = ⊤ :=
eq_top_of_findim_eq $ findim_vector_span_of_affine_independent hi hc

/-- The `affine_span` of a finite affinely independent family whose
cardinality is one more than that of the finite-dimensional space is
`⊤`. -/
lemma affine_span_eq_top_of_affine_independent_of_card_eq_findim_add_one [finite_dimensional k V]
    [fintype ι] {p : ι → P} (hi : affine_independent k p)
    (hc : fintype.card ι = findim k V + 1) :
  affine_span k (set.range p) = ⊤ :=
begin
  have hn : (set.range p).nonempty,
  { refine set.range_nonempty_iff_nonempty.2 (fintype.card_pos_iff.1 _),
    simp [hc] },
  rcases hn with ⟨p₁, hp₁⟩,
  have hn : (affine_span k (set.range p) : set P).nonempty := ⟨p₁, mem_affine_span k hp₁⟩,
  rw [←affine_subspace.direction_eq_top_iff_of_nonempty hn, direction_affine_span],
  exact vector_span_eq_top_of_affine_independent_of_card_eq_findim_add_one hi hc
end

end affine

open affine finite_dimensional

variables {V : Type*} {P : Type*} [inner_product_space V] [metric_space P]
    [normed_add_torsor V P] [finite_dimensional ℝ V]

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

omit V

-- Properties of sets of points in the answer.

-- A set of points is concyclic.  Should probably go in mathlib in
-- some form, with relations between versions with or without centre
-- constrained to be in a given subspace containing the points, and
-- with versions with bundled spheres in nondegenerate cases.
def concyclic (s : set P) : Prop :=
∃ (centre : P) (radius : ℝ), ∀ p ∈ s, dist p centre = radius

include V

-- Any three points in a concyclic set are affinely independent.
-- Should go in mathlib in some form.
lemma affine_independent_of_concyclic {s : set P} (hs : concyclic s) {p : fin 3 → P}
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

-- The description given as an answer to the problem.
def p2_answer_desc (s : set P) : Prop :=
at_least_four_points s ∧ (concyclic s ∨ orthocentric_system s)

-- The result of the problem.
theorem p2_result (s : set P) (hd2 : findim ℝ V = 2) :
  p2_problem_desc s ↔ p2_answer_desc s :=
begin
  unfold p2_problem_desc p2_answer_desc,
  rw and.congr_right_iff,
  intro h4,
  split,
  { rintro ⟨hn3, r, hr⟩,
    sorry },
  { rintro (hc | ho),
    { split,
      { exact λ p hpi hps, affine_independent_of_concyclic hc hps hpi },
      { rcases hc with ⟨c, r, hcr⟩,
        use r,
        intros t hts,
        have ht : affine_span ℝ (set.range t.points) = ⊤,
        { refine affine_span_eq_top_of_affine_independent_of_card_eq_findim_add_one
            t.independent _,
          simp [hd2] },
        have hc : c ∈ affine_span ℝ (set.range t.points) :=
          ht.symm ▸ affine_subspace.mem_top ℝ V c,
        exact (t.eq_circumradius_of_dist_eq
          hc
          (λ i, hcr (t.points i) (hts (set.mem_range_self i)))).symm } },
    { split,
      { exact λ p hpi hps, affine_independent_of_orthocentric_system ho hps hpi },
      { exact exists_circumradius_eq_of_orthocentric_system ho } } }
end
