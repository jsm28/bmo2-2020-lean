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

section affine

-- For mathlib.

variables (k : Type*) {V : Type*} {P : Type*} [field k] [add_comm_group V] [module k V]
          [affine_space V P]
variables {ι : Type*}
include V

/-- The direction of the affine span of a subset of a family indexed
by a `fintype` is finite-dimensional. -/
instance finite_dimensional_direction_affine_span_image_of_fintype [fintype ι] (p : ι → P)
    (s : set ι) :
  finite_dimensional k (affine_span k (p '' s)).direction :=
finite_dimensional_direction_affine_span_of_finite k ((set.finite.of_fintype _).image _)

end affine

section affine

-- For mathlib.

variables (k : Type*) {V : Type*} {P : Type*} [field k] [add_comm_group V] [module k V]
variables [affine_space V P] {ι : Type*}
include V

/-- Two different points are affinely independent. -/
lemma affine_independent_of_ne (p : ι → P) {i₁ i₂ : ι} (he : ∀ i, i = i₁ ∨ i = i₂)
    (hn : p i₁ ≠ p i₂) :
  affine_independent k p :=
begin
  rw affine_independent_iff_linear_independent_vsub k p i₁,
  have hne : i₂ ≠ i₁,
  { intro h,
    rw h at hn,
    exact hn rfl },
  let i₂' : {x // x ≠ i₁} := ⟨i₂, hne⟩,
  have he' : ∀ i, i = i₂' := λ ⟨i, hi⟩, subtype.mk_eq_mk.2 (or.resolve_left (he i) hi),
  haveI : unique {x // x ≠ i₁} := ⟨⟨i₂'⟩, he'⟩,
  have h : (p ↑(default {x // x ≠ i₁}) -ᵥ p i₁ : V) ≠ 0,
  { rw he' (default _),
    intro h,
    rw vsub_eq_zero_iff_eq at h,
    exact hn h.symm },
  exact linear_independent_unique h
end

/-- Two different points indexed by `fin 2` are affinely independent. -/
lemma affine_independent_of_ne_fin {p₁ p₂ : P} (h : p₁ ≠ p₂) :
  affine_independent k ![p₁, p₂] :=
affine_independent_of_ne k ![p₁, p₂] (dec_trivial : ∀ i : fin 2, i = 0 ∨ i = 1) h

end affine

namespace finset

variables {k : Type*} {V : Type*} {P : Type*} [ring k] [add_comm_group V] [module k V]
variables [S : affine_space V P]
include S
variables {ι : Type*} (s : finset ι)
variables {ι₂ : Type*} (s₂ : finset ι₂)

/-- A weighted sum combined with an embedding. -/
lemma weighted_vsub_of_point_map (e : ι₂ ↪ ι) (w : ι → k) (p : ι → P) (b : P) :
  (s₂.map e).weighted_vsub_of_point p b w = s₂.weighted_vsub_of_point (p ∘ e) b (w ∘ e) :=
begin
  simp_rw [weighted_vsub_of_point_apply],
  exact finset.sum_map _ _ _
end

/-- A weighted subtraction combined with an embedding. -/
lemma weighted_vsub_map (e : ι₂ ↪ ι) (w : ι → k) (p : ι → P) :
  (s₂.map e).weighted_vsub p w = s₂.weighted_vsub (p ∘ e) (w ∘ e) :=
s₂.weighted_vsub_of_point_map _ _ _ _

/-- An affine combination combined with an embedding. -/
lemma affine_combination_map (e : ι₂ ↪ ι) (w : ι → k) (p : ι → P) :
  (s₂.map e).affine_combination p w = s₂.affine_combination (p ∘ e) (w ∘ e) :=
by simp_rw [affine_combination_apply, weighted_vsub_of_point_map]

end finset

namespace finset

variables (k : Type*) {V : Type*} {P : Type*} [division_ring k] [add_comm_group V] [module k V]
variables [affine_space V P] {ι : Type*} (s : finset ι)
variables {ι₂ : Type*} (s₂ : finset ι₂)

include V

/-- The centroid combined with an embedding. -/
lemma centroid_map (e : ι₂ ↪ ι) (p : ι → P) : (s₂.map e).centroid k p = s₂.centroid k (p ∘ e) :=
by simp [centroid_def, affine_combination_map, centroid_weights]

omit V

/-- The weights for the centroid indexed by a `fintype`, for sums over
`univ`. -/
def centroid_weights_fintype [fintype ι] : ι → k := set.indicator ↑s (s.centroid_weights k)

/-- The definition of `centroid_weights_fintype`. -/
lemma centroid_weights_fintype_def [fintype ι] :
  s.centroid_weights_fintype k = set.indicator ↑s (s.centroid_weights k) :=
rfl

/-- The sum of the weights for the centroid indexed by a `fintype`. -/
lemma sum_centroid_weights_fintype [fintype ι] :
  ∑ i, s.centroid_weights_fintype k i = ∑ i in s, s.centroid_weights k i :=
(set.sum_indicator_subset _ (subset_univ _)).symm

/-- In the characteristic zero case, the weights in the centroid
indexed by a `fintype` sum to 1 if the number of points is not
zero. -/
lemma sum_centroid_weights_fintype_eq_one_of_card_ne_zero [char_zero k] [fintype ι]
    (h : card s ≠ 0) :
  ∑ i, s.centroid_weights_fintype k i = 1 :=
begin
  rw sum_centroid_weights_fintype,
  exact s.sum_centroid_weights_eq_one_of_card_ne_zero k h
end

/-- In the characteristic zero case, the weights in the centroid
indexed by a `fintype` sum to 1 if the set is nonempty. -/
lemma sum_centroid_weights_fintype_eq_one_of_nonempty [char_zero k] [fintype ι] (h : s.nonempty) :
  ∑ i, s.centroid_weights_fintype k i = 1 :=
begin
  rw sum_centroid_weights_fintype,
  exact s.sum_centroid_weights_eq_one_of_nonempty k h
end

/-- In the characteristic zero case, the weights in the centroid
indexed by a `fintype` sum to 1 if the number of points is `n + 1`. -/
lemma sum_centroid_weights_fintype_eq_one_of_card_eq_add_one [char_zero k] [fintype ι] {n : ℕ}
  (h : card s = n + 1) : ∑ i, s.centroid_weights_fintype k i = 1 :=
begin
  rw sum_centroid_weights_fintype,
  exact s.sum_centroid_weights_eq_one_of_card_eq_add_one k h
end

include V

/-- The centroid as an affine combination over a `fintype`. -/
lemma centroid_eq_affine_combination_fintype [fintype ι] (p : ι → P) :
  s.centroid k p = univ.affine_combination p (s.centroid_weights_fintype k) :=
affine_combination_indicator_subset _ _ (subset_univ _)

end finset

namespace affine
namespace simplex

-- For mathlib.

section ring

variables {k : Type*} {V : Type*} {P : Type*} [ring k]
          [add_comm_group V] [module k V] [affine_space V P]
include V

/-- The set of points of a face. -/
@[simp] lemma range_face_points {n : ℕ} (s : simplex k P n) {fs : finset (fin (n + 1))}
    {m : ℕ} (h : fs.card = m + 1) :
  set.range (s.face h).points = s.points '' ↑fs :=
begin
  rw [face, set.range_comp],
  simp
end

end ring

variables {k : Type*} {V : Type*} {P : Type*} [division_ring k]
          [add_comm_group V] [module k V] [affine_space V P]
include V

/-- The centroid of a face of a simplex as the centroid of a subset of
the points. -/
@[simp] lemma face_centroid_eq_centroid {n : ℕ} (s : simplex k P n) {fs : finset (fin (n + 1))}
    {m : ℕ} (h : fs.card = m + 1) :
  finset.univ.centroid k (s.face h).points = fs.centroid k s.points :=
begin
  convert (finset.univ.centroid_map k ⟨fs.mono_of_fin h, fs.mono_of_fin_injective h⟩ s.points).symm,
  rw [←finset.coe_inj, finset.coe_map, function.embedding.coe_fn_mk],
  simp
end

/-- Over a characteristic-zero division ring, the centroids of two
faces of a simplex are equal if and only if those faces are given by
the same subset of points. -/
@[simp] lemma face_centroid_eq_iff [char_zero k] {n : ℕ} (s : simplex k P n)
  {fs₁ fs₂ : finset (fin (n + 1))} {m₁ m₂ : ℕ} (h₁ : fs₁.card = m₁ + 1) (h₂ : fs₂.card = m₂ + 1) :
  finset.univ.centroid k (s.face h₁).points = finset.univ.centroid k (s.face h₂).points ↔
    fs₁ = fs₂ :=
begin
  split,
  { intro h,
    rw [face_centroid_eq_centroid, face_centroid_eq_centroid,
        finset.centroid_eq_affine_combination_fintype,
        finset.centroid_eq_affine_combination_fintype] at h,
    have ha := (affine_independent_iff_indicator_eq_of_affine_combination_eq k s.points).1
      s.independent _ _ _ _ (fs₁.sum_centroid_weights_fintype_eq_one_of_card_eq_add_one k h₁)
      (fs₂.sum_centroid_weights_fintype_eq_one_of_card_eq_add_one k h₂) h,
    simp_rw [finset.coe_univ, set.indicator_univ, function.funext_iff,
             finset.centroid_weights_fintype_def, finset.centroid_weights, h₁, h₂] at ha,
    ext i,
    replace ha := ha i,
    split,
    all_goals
    { intro hi,
      by_contradiction hni,
      simp [hi, hni] at ha,
      norm_cast at ha } },
  { intro h,
    have hm : m₁ = m₂,
    { subst h,
      simpa [h₁] using h₂ },
    subst hm,
    congr,
    exact h }
end

end simplex
end affine

open affine finite_dimensional euclidean_geometry

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

omit V

-- Properties of sets of points in the answer.

-- A set of points is cospherical.  Should probably go in mathlib in
-- some form, with relations between versions with or without centre
-- constrained to be in a given subspace containing the points, and
-- with versions with bundled spheres in nondegenerate cases.
def cospherical (s : set P) : Prop :=
∃ (centre : P) (radius : ℝ), ∀ p ∈ s, dist p centre = radius

include V

namespace affine
namespace simplex

/-- The circumradius is non-negative. -/
lemma circumradius_nonneg {n : ℕ} (s : simplex ℝ P n) : 0 ≤ s.circumradius :=
s.dist_circumcenter_eq_circumradius 0 ▸ dist_nonneg

/-- The circumradius of a simplex with at least two points is
positive. -/
lemma circumradius_pos {n : ℕ} (s : simplex ℝ P (n + 1)) : 0 < s.circumradius :=
begin
  refine lt_of_le_of_ne s.circumradius_nonneg _,
  intro h,
  have hr := s.dist_circumcenter_eq_circumradius,
  simp_rw [←h, dist_eq_zero] at hr,
  have h01 := (injective_of_affine_independent s.independent).ne
    (dec_trivial : (0 : fin (n + 2)) ≠ 1),
  simpa [hr] using h01
end

/-- The circumcenter of a 0-simplex equals its unique point. -/
lemma circumcenter_eq_point (s : simplex ℝ P 0) (i : fin 1) :
  s.circumcenter = s.points i :=
begin
  have h := s.circumcenter_mem_affine_span,
  rw [set.range_unique, affine_subspace.mem_affine_span_singleton] at h,
  rw h,
  congr
end

/-- The circumcenter of a 1-simplex equals its centroid. -/
lemma circumcenter_eq_centroid (s : simplex ℝ P 1) :
  s.circumcenter = finset.univ.centroid ℝ s.points :=
begin
  have hu : (finset.univ : finset (fin 2)) = {0, 1}, by dec_trivial,
  have h0 : (0 : fin 2) ∉ ({1} : finset (fin 2)), by dec_trivial,
  have hr : set.pairwise_on set.univ
    (λ i j : fin 2, dist (s.points i) (finset.univ.centroid ℝ s.points) =
                    dist (s.points j) (finset.univ.centroid ℝ s.points)),
  { intros i hi j hj hij,
    simp_rw [←mul_self_inj_of_nonneg dist_nonneg dist_nonneg,
             centroid_eq_affine_combination_of_points_with_circumcenter,
             point_eq_affine_combination_of_points_with_circumcenter,
             dist_affine_combination _ (sum_point_weights_with_circumcenter _)
               (sum_centroid_weights_with_circumcenter ⟨(0 : fin 2), finset.mem_univ _⟩),
             sum_points_with_circumcenter, pi.sub_apply, points_with_circumcenter,
             point_weights_with_circumcenter, centroid_weights_with_circumcenter,
             hu, finset.sum_insert h0, finset.sum_singleton],
    have hc0 : ((fin.mk 0 dec_trivial : fin 2) : ℕ) = 0, by dec_trivial,
    have hc1 : ((fin.mk 1 dec_trivial : fin 2) : ℕ) = 1, by dec_trivial,
    simp [dist_comm (s.points 0) (s.points 1), fin.ext_iff],
    fin_cases i; fin_cases j; simp [hc0, hc1]; ring },
  rw set.pairwise_on_eq_iff_exists_eq at hr,
  cases hr with r hr,
  exact (s.eq_circumcenter_of_dist_eq
          (centroid_mem_affine_span_of_card_eq_add_one ℝ _ (finset.card_fin 2))
          (λ i, hr i (set.mem_univ _))).symm
end

/-- The orthogonal projection of the circumcenter onto a face is the
circumcenter of that face. -/
lemma orthogonal_projection_circumcenter {n : ℕ} (s : simplex ℝ P n) {fs : finset (fin (n + 1))}
    {m : ℕ} (h : fs.card = m + 1) :
  orthogonal_projection (affine_span ℝ (s.points '' ↑fs)) s.circumcenter =
    (s.face h).circumcenter :=
begin
  have hr : ∃ r, ∀ p ∈ set.range (s.face h).points, dist p s.circumcenter = r,
  { use s.circumradius,
    intros p hp,
    rcases set.mem_range.1 hp with ⟨i, rfl⟩,
    simp [face_points] },
  have hs : set.range (s.face h).points ⊆ affine_span ℝ (s.points '' ↑fs),
  { rw s.range_face_points h,
    exact subset_span_points ℝ _ },
  rw exists_dist_eq_iff_exists_dist_orthogonal_projection_eq hs s.circumcenter at hr,
  cases hr with r hr,
  have ho : orthogonal_projection (affine_span ℝ (s.points '' ↑fs)) s.circumcenter ∈
    affine_span ℝ (set.range (s.face h).points),
  { rw s.range_face_points h,
    have hn : (affine_span ℝ (s.points '' ↑fs) : set P).nonempty,
    { simp [←finset.card_pos, h] },
    refine orthogonal_projection_mem hn (submodule.complete_of_finite_dimensional _) _ },
  rw set.forall_range_iff at hr,
  exact (s.face h).eq_circumcenter_of_dist_eq ho hr
end

-- The distance from the orthocenter to the reflection of the
-- circumcenter in a side equals the circumradius.  This should go in
-- mathlib in some form.
lemma dist_orthocenter_reflection_circumcenter (t : triangle ℝ P) {i₁ i₂ : fin 3} (h : i₁ ≠ i₂) :
  dist t.orthocenter (reflection (affine_span ℝ (t.points '' {i₁, i₂})) t.circumcenter) =
    t.circumradius :=
sorry

-- The distance from the orthocenter to the reflection of the
-- circumcenter in a side equals the circumradius, variant using a
-- finset.  This should go in mathlib in some form.
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

/-- Distances from two different points determine at most two points
in a two-dimensional subspace containing those points (two circles
intersect in at most two points). -/
lemma eq_of_dist_eq_of_dist_eq_of_mem_of_findim_eq_two {s : affine_subspace ℝ P}
  [finite_dimensional ℝ s.direction] (hd : findim ℝ s.direction = 2) {c₁ c₂ p₁ p₂ p : P}
  (hc₁s : c₁ ∈ s) (hc₂s : c₂ ∈ s) (hp₁s : p₁ ∈ s) (hp₂s : p₂ ∈ s) (hps : p ∈ s) {r₁ r₂ : ℝ}
  (hc : c₁ ≠ c₂) (hp : p₁ ≠ p₂) (hp₁c₁ : dist p₁ c₁ = r₁) (hp₂c₁ : dist p₂ c₁ = r₁)
  (hpc₁ : dist p c₁ = r₁) (hp₁c₂ : dist p₁ c₂ = r₂) (hp₂c₂ : dist p₂ c₂ = r₂)
  (hpc₂ : dist p c₂ = r₂) : p = p₁ ∨ p = p₂ :=
sorry

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
  { rw [affine_subspace.direction_top, findim_top],
    exact hd },
  exact eq_of_dist_eq_of_dist_eq_of_mem_of_findim_eq_two hd'
    (affine_subspace.mem_top ℝ V _) (affine_subspace.mem_top ℝ V _)
    (affine_subspace.mem_top ℝ V _) (affine_subspace.mem_top ℝ V _)
    (affine_subspace.mem_top ℝ V _) hc hp hp₁c₁ hp₂c₁ hpc₁ hp₁c₂ hp₂c₂ hpc₂
end

-- Suppose all distances from `p₁` and `p₂` to the points of a simplex
-- are equal, and that `p₁` and `p₂` lie in the affine span of `p`
-- with the vertices of that simplex.  Then `p₁` and `p₂` are equal or
-- reflections of each other in the affine span of the vertices of the
-- simplex.
lemma eq_or_eq_reflection_of_dist_eq {n : ℕ} {s : simplex ℝ P n} {p p₁ p₂ : P} {r : ℝ}
    (hp₁ : p₁ ∈ affine_span ℝ (insert p (set.range s.points)))
    (hp₂ : p₂ ∈ affine_span ℝ (insert p (set.range s.points)))
    (h₁ : ∀ i, dist p₁ (s.points i) = r) (h₂ : ∀ i, dist p₂ (s.points i) = r) :
  p₁ = p₂ ∨ p₁ = reflection (affine_span ℝ (set.range s.points)) p₂ :=
sorry

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
  have hc : c ∈ affine_span ℝ (set.range s.points) := hs.symm ▸ affine_subspace.mem_top ℝ V c,
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
  have hc : c ∈ affine_span ℝ (set.range s.points) := hs.symm ▸ affine_subspace.mem_top ℝ V c,
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

variables [finite_dimensional ℝ V]

-- The description given as an answer to the problem.
def p2_answer_desc (s : set P) : Prop :=
at_least_four_points s ∧ (cospherical s ∨ orthocentric_system s)

omit V

-- None of these lemmas were needed as of mathlib commit
-- e21675586b974322f8221ee42b384a6932d75440, but as of mathlib commit
-- eaaac992d0a564071242d08fadffeee3043f91d7 the last one was needed
-- for simp to reduce extraction of elements of `fin 3`-indexed
-- families automatically.  As of Lean 3.19.0 and mathlib commit
-- 14e7fe83aec976c37de482d6b443b8ccafb4e2d2, all three lemmas were
-- needed and the last argument needed to be stated using fin.mk
-- rather than using a numeral as before.

@[simp] lemma p2_fin3_0 {α : Type*} (a b c : α) : ![a, b, c] (fin.mk 0 (by norm_num)) = a :=
rfl

@[simp] lemma p2_fin3_1 {α : Type*} (a b c : α) : ![a, b, c] (fin.mk 1 (by norm_num)) = b :=
rfl

@[simp] lemma p2_fin3_3 {α : Type*} (a b c : α) : ![a, b, c] (fin.mk 2 (by norm_num)) = c :=
rfl

-- Likewise, lemmas for fin 2.

@[simp] lemma p2_fin2_0 {α : Type*} (a b : α) : ![a, b] (fin.mk 0 (by norm_num)) = a :=
rfl

@[simp] lemma p2_fin2_1 {α : Type*} (a b : α) : ![a, b] (fin.mk 1 (by norm_num)) = b :=
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
  let t12 : simplex ℝ P 1 := ⟨![t0.points i1, t0.points i2], affine_independent_of_ne_fin ℝ h12⟩,
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
  have hr0 : ∀ i, dist t0.circumcenter (t12.points i) = t0.circumradius,
  { intro i,
    fin_cases i; simp [t12] },
  have hr1 : ∀ i, dist t1.circumcenter (t12.points i) = t0.circumradius,
  { intro i,
    fin_cases i,
    { change dist _ (t1.points 0) = _,
      simp [←ht1cr] },
    { change dist _ (t1.points 1) = _,
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
      exact t2.eq_circumcenter_of_dist_eq (ht2span.symm ▸ affine_subspace.mem_top ℝ V _) h },
    have ht12cc : t1.circumcenter = t2.circumcenter,
    { have h : ∀ (i : fin 3), dist (t2.points i) t1.circumcenter = t1.circumradius,
      { intro i,
        fin_cases i,
        { change dist (t1.points 0) _ = _,
          simp },
        { change dist (t1.points 1) _ = _,
          simp },
        { simp [t2, p2_triangle_of_ne, heq] } },
      exact t2.eq_circumcenter_of_dist_eq (ht2span.symm ▸ affine_subspace.mem_top ℝ V _) h },
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
