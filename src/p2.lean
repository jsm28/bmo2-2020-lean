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
open_locale classical

section add_torsor

variables {G : Type*} {P : Type*} [add_comm_group G] [add_torsor G P]

lemma vsub_vadd_comm (p1 p2 p3 : P) :
  (p1 -ᵥ p2 : G) +ᵥ p3 = p3 -ᵥ p2 +ᵥ p1 :=
begin
  rw [←@vsub_eq_zero_iff_eq G, vadd_vsub_assoc, vsub_vadd_eq_vsub_sub],
  simp
end

end add_torsor

open affine finite_dimensional euclidean_geometry

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

-- A set of points is cospherical.  Should probably go in mathlib in
-- some form, with relations between versions with or without centre
-- constrained to be in a given subspace containing the points, and
-- with versions with bundled spheres in nondegenerate cases.
def cospherical (s : set P) : Prop :=
∃ (centre : P) (radius : ℝ), ∀ p ∈ s, dist p centre = radius

include V

-- All n-simplices among cospherical points in n-space have the same
-- circumradius.  This should go in mathlib in some form.
lemma exists_circumradius_eq_of_cospherical {ps : set P} {n : ℕ} (hd : findim ℝ V = n)
    (hc : cospherical ps) :
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
lemma exists_circumcenter_eq_of_cospherical {ps : set P} {n : ℕ} (hd : findim ℝ V = n)
    (hc : cospherical ps) :
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

-- The linear map corresponding to `orthogonal_projection`.  This
-- should go in mathlib.
@[simp] lemma orthogonal_projection_linear {s : affine_subspace ℝ P} (hn : (s : set P).nonempty)
    (hc : is_complete (s.direction : set V)) :
  (orthogonal_projection hn hc).linear = orthogonal_projection hc :=
rfl

-- Orthogonal projection is idempotent.  This should go in mathlib.
@[simp] lemma orthogonal_projection_orthgonal_projection {s : affine_subspace ℝ P}
    (hn : (s : set P).nonempty) (hc : is_complete (s.direction : set V)) {p : P} :
   orthogonal_projection hn hc (orthogonal_projection hn hc p) = orthogonal_projection hn hc p :=
begin
  rw orthogonal_projection_eq_self_iff hn hc,
  exact orthogonal_projection_mem hn hc p
end

-- Reflection in a nonempty affine subspace, whose direction is
-- complete (generalization of both the common cases of reflection in
-- a point and reflection in a codimension-one subspace).  This should
-- go in mathlib.
def reflection {s : affine_subspace ℝ P} (hn : (s : set P).nonempty)
    (hc : is_complete (s.direction : set V)) : P ≃ᵢ P :=
{ to_fun := λ p, (orthogonal_projection hn hc p -ᵥ p) +ᵥ orthogonal_projection hn hc p,
  inv_fun := λ p, (orthogonal_projection hn hc p -ᵥ p) +ᵥ orthogonal_projection hn hc p,
  left_inv := λ p, by simp [vsub_vadd_eq_vsub_sub, -orthogonal_projection_linear],
  right_inv := λ p, by simp [vsub_vadd_eq_vsub_sub, -orthogonal_projection_linear],
  isometry_to_fun := begin
    dsimp only,
    rw isometry_emetric_iff_metric,
    intros p₁ p₂,
    rw [←mul_self_inj_of_nonneg dist_nonneg dist_nonneg, dist_eq_norm_vsub V
          ((orthogonal_projection hn hc p₁ -ᵥ p₁) +ᵥ orthogonal_projection hn hc p₁),
        dist_eq_norm_vsub V p₁, vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_comm, add_sub_assoc,
        ←vsub_vadd_eq_vsub_sub, vsub_vadd_comm, vsub_vadd_eq_vsub_sub, ←add_sub_assoc,
        ←affine_map.linear_map_vsub, orthogonal_projection_linear, ←inner_self_eq_norm_square,
        ←inner_self_eq_norm_square, inner_sub_sub_self, inner_add_left, inner_add_right,
        inner_add_left, ←two_mul, ←two_mul, ←two_mul, ←mul_sub_left_distrib,
        ←mul_sub_left_distrib, ←inner_sub_right, inner_comm, ←inner_neg_neg, neg_sub,
        inner_neg_right,
        orthogonal_projection_inner_eq_zero hc _ _ (orthogonal_projection_mem hc _)],
    simp
  end }

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

-- The description given as an answer to the problem.
def p2_answer_desc (s : set P) : Prop :=
at_least_four_points s ∧ (cospherical s ∨ orthocentric_system s)

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
-- must be its orthocentre.
theorem p2_eq_orthocentre {s : set P} (hd2 : findim ℝ V = 2) {t0 : triangle ℝ P} {p : P}
    (ht0s : set.range t0.points ⊆ s)
    (hr : ∀ (t : triangle ℝ P), set.range t.points ⊆ s → t.circumradius = t0.circumradius)
    (hp : p ∈ s) (hpn : dist p t0.circumcenter ≠ t0.circumradius) :
  p = t0.orthocenter :=
begin
  sorry
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
  { refine p2_eq_orthocentre hd2 ht1s _ hp hpt1,
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
    have hpo := p2_eq_orthocentre hd2 ht0s hr hps hpr,
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
      { exact hp1no (p2_eq_orthocentre hd2 ht0s hr hp1 hp1r) } } }
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
