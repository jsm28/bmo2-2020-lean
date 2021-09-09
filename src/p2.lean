-- BMO2 2020 problem 2.

-- Choices made for formalization: the original problem refers to
-- "collections", which we take as meaning sets.

import geometry.euclidean

noncomputable theory
open_locale classical

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
theorem p2_dist_reflection_circumcentre {s : set P} (hd2 : finrank ℝ V = 2)
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
  have h12 := t0.independent.injective.ne hi12,
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
    { refine t0.independent.affine_span_eq_top_of_card_eq_finrank_add_one _,
      simp [hd2] },
    rw ←ht0span,
    congr,
    rw [←set.image_univ, ←set.image_univ, hu2, hu3, set.image_insert_eq, set.image_singleton,
        set.image_insert_eq, set.image_insert_eq, set.image_singleton],
    refl },
  -- So the circumcentres of t1 and t2 are in that span.
  have hc0s : t0.circumcenter ∈ affine_span ℝ (insert (t0.points i3) (set.range t12.points)),
  { simp [h123, -matrix.range_cons] },
  have hc1s : t1.circumcenter ∈ affine_span ℝ (insert (t0.points i3) (set.range t12.points)),
  { simp [h123, -matrix.range_cons] },
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
  { have hr : affine_span ℝ (t0.points '' ↑({i1, i2} : finset (fin 3))) =
      affine_span ℝ (set.range t12.points),
    { rw [←set.image_univ, hu2],
      simp [t12, set.image_insert_eq] },
    rw [eq_reflection_of_eq_subspace hr, ←h],
    change dist (t1.points 2) _ = _,
    simp [ht1cr] }
end

-- Given a triangle in a set with the properties of the problem, any
-- point in that set that is not on the circumcircle of the triangle
-- must be its orthocentre.
theorem p2_eq_orthocentre {s : set P} (hd2 : finrank ℝ V = 2) (hn3 : no_three_points_collinear s)
    {t0 : triangle ℝ P} {p : P} (ht0s : set.range t0.points ⊆ s)
    (hr : ∀ (t : triangle ℝ P), set.range t.points ⊆ s → t.circumradius = t0.circumradius)
    (hp : p ∈ s) (hpn : dist p t0.circumcenter ≠ t0.circumradius) :
  p = t0.orthocenter :=
begin
  -- First find a vertex not equal to the orthocentre.
  obtain ⟨i1 : fin 3, hi1o⟩ := t0.independent.injective.exists_ne t0.orthocenter,
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
    have hf12 : affine_span ℝ (t0.points '' ↑({i1, i2} : finset (fin 3))) =
      affine_span ℝ (set.range (t0.face hc12).points), { simp },
    have hf13 : affine_span ℝ (t0.points '' ↑({i1, i3} : finset (fin 3))) =
      affine_span ℝ (set.range (t0.face hc13).points), { simp },
    rw [eq_reflection_of_eq_subspace hf12, eq_reflection_of_eq_subspace hf13,
        reflection_eq_iff_orthogonal_projection_eq, t0.orthogonal_projection_circumcenter hc12,
        t0.orthogonal_projection_circumcenter hc13, (t0.face hc12).circumcenter_eq_centroid,
        (t0.face hc13).circumcenter_eq_centroid, t0.face_centroid_eq_iff] at h,
    exact h1213 h },
  -- Thus p is either vertex i1 or the orthocentre.
  have hpeq :=
    eq_of_dist_eq_of_dist_eq_of_finrank_eq_two hd2 hrne hi1o hi12 ho2 hp12 hi13 ho3 hp13,
  cases hpeq,
  { rw [hpeq, t0.dist_circumcenter_eq_circumradius] at hpn,
    exact false.elim (hpn rfl) },
  { exact hpeq }
end

-- Given p on the circumcircle of t0, not a vertex, not the
-- orthocentre, the orthocentre not on the circumcircle; derive a
-- contradiction.
theorem p2_orthocentre_extra {s : set P} (hd2 : finrank ℝ V = 2)
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
    have hi := t0.independent.injective h,
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
    { refine t0.independent.affine_span_eq_top_of_card_eq_finrank_add_one _,
      simp [hd2] },
    have ht1span : affine_span ℝ (set.range t1.points) = ⊤,
    { refine t1.independent.affine_span_eq_top_of_card_eq_finrank_add_one _,
      simp [hd2] },
    have ht2span : affine_span ℝ (set.range t2.points) = ⊤,
    { refine t2.independent.affine_span_eq_top_of_card_eq_finrank_add_one _,
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
  have hs' := hs'o.eq_insert_orthocenter ht1s',
  rw ←hpt1o at hs',
  have hps' : p ∈ insert t0.orthocenter (set.range t0.points),
  { change p ∈ s',
    rw hs',
    exact set.mem_insert _ _ },
  simpa [hpno, h0np] using hps'
end

-- The main part of the solution: a set with the given property is as
-- described.
theorem p2_result_main {s : set P} (hd2 : finrank ℝ V = 2) (h4 : at_least_four_points s)
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
theorem p2_result (s : set P) (hd2 : finrank ℝ V = 2) :
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
        exact λ p hpi hps, hc.affine_independent hps hpi },
      { exact exists_circumradius_eq_of_cospherical hd2 hc } },
    { split,
      { rw no_three_points_collinear_iff,
        exact λ p hpi hps, ho.affine_independent hps hpi },
      { exact ho.exists_circumradius_eq } } }
end
