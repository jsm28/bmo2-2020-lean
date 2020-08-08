-- Existence and uniqueness of circumcenter (mathlib PR #3693).

import geometry.euclidean

noncomputable theory
open_locale classical
open_locale big_operators

namespace euclidean_geometry

variables (V : Type*) {P : Type*} [inner_product_space V] [metric_space P]
    [euclidean_affine_space V P]

variables {V}

open add_torsor affine_subspace affine_space

/-- `p` is equidistant from two points in `s` if and only if its
`orthogonal_projection` is. -/
lemma dist_eq_iff_dist_orthogonal_projection_eq {s : affine_subspace ℝ V P}
    (hn : (s : set P).nonempty) (hc : is_complete (s.direction : set V)) {p1 p2 : P} (p3 : P)
    (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) :
  dist p1 p3 = dist p2 p3 ↔
    dist p1 (orthogonal_projection hn hc p3) = dist p2 (orthogonal_projection hn hc p3) :=
begin
  rw [←mul_self_inj_of_nonneg dist_nonneg dist_nonneg,
      ←mul_self_inj_of_nonneg dist_nonneg dist_nonneg,
      dist_square_eq_dist_orthogonal_projection_square_add_dist_orthogonal_projection_square
        hn hc p3 hp1,
      dist_square_eq_dist_orthogonal_projection_square_add_dist_orthogonal_projection_square
        hn hc p3 hp2],
  simp
end

/-- `p` is equidistant from a set of points in `s` if and only if its
`orthogonal_projection` is. -/
lemma dist_set_eq_iff_dist_orthogonal_projection_eq {s : affine_subspace ℝ V P}
    (hn : (s : set P).nonempty) (hc : is_complete (s.direction : set V)) {ps : set P}
    (hps : ps ⊆ s) (p : P) :
  (∀ p1 p2 ∈ ps, dist p1 p = dist p2 p) ↔
    ∀ p1 p2 ∈ ps, dist p1 (orthogonal_projection hn hc p) =
      dist p2 (orthogonal_projection hn hc p) :=
⟨λ h p1 p2 hp1 hp2,
  (dist_eq_iff_dist_orthogonal_projection_eq hn hc p (hps hp1) (hps hp2)).1 (h p1 p2 hp1 hp2),
λ h p1 p2 hp1 hp2,
  (dist_eq_iff_dist_orthogonal_projection_eq hn hc p (hps hp1) (hps hp2)).2 (h p1 p2 hp1 hp2)⟩

variables (V)

/-- `p` has pairwise equal distances to a set of points if and only if
there exists an `r` that all those distances equal. -/
lemma dist_set_eq_iff_exists_dist_eq (ps : set P) (p : P) :
  (∀ p1 p2 ∈ ps, dist p1 p = dist p2 p) ↔ ∃ r, ∀ p1 ∈ ps, dist p1 p = r :=
begin
  split,
  { intro h,
    by_cases hn : ps.nonempty,
    { cases hn with q hq,
      exact ⟨dist q p, λ p1 hp1, h p1 q hp1 hq⟩ },
    { rw set.not_nonempty_iff_eq_empty at hn,
      use 0,
      intros p1 hp1,
      rw hn at hp1,
      exact false.elim hp1 } },
  { rintros ⟨r, hr⟩ p1 p2 hp1 hp2,
    rw [hr p1 hp1, hr p2 hp2] }
end

variables {V}

/-- There exists `r` such that `p` has distance `r` from all the
points of a set of points in `s` if and only if there exists (possibly
different) `r` such that its `orthogonal_projection` has that distance
from all the points in that set. -/
lemma exists_dist_eq_iff_exists_dist_orthogonal_projection_eq {s : affine_subspace ℝ V P}
    (hn : (s : set P).nonempty) (hc : is_complete (s.direction : set V)) {ps : set P}
    (hps : ps ⊆ s) (p : P) :
  (∃ r, ∀ p1 ∈ ps, dist p1 p = r) ↔
    ∃ r, ∀ p1 ∈ ps, dist p1 (orthogonal_projection hn hc p) = r :=
begin
  have h := dist_set_eq_iff_dist_orthogonal_projection_eq hn hc hps p,
  simp_rw dist_set_eq_iff_exists_dist_eq at h,
  exact h
end

/-- The induction step for the existence and uniqueness of the
circumcenter.  Given a nonempty set of points in a nonempty affine
subspace whose direction is complete, such that there is a unique
(circumcenter, circumradius) pair for those points in that subspace,
and a point `p` not in that subspace, there is a unique (circumcenter,
circumradius) pair for the set with `p` added, in the span of the
subspace with `p` added. -/
lemma exists_unique_dist_eq_of_insert {s : affine_subspace ℝ V P} (hn : (s : set P).nonempty)
    (hc : is_complete (s.direction : set V)) {ps : set P} (hnps : ps.nonempty) {p : P}
    (hps : ps ⊆ s) (hp : p ∉ s)
    (hu : ∃! cccr : (P × ℝ), cccr.fst ∈ s ∧ ∀ p1 ∈ ps, dist p1 cccr.fst = cccr.snd) :
  ∃! cccr₂ : (P × ℝ), cccr₂.fst ∈ affine_span ℝ V (insert p (s : set P)) ∧
    ∀ p1 ∈ insert p ps, dist p1 cccr₂.fst = cccr₂.snd :=
begin
  rcases hu with ⟨⟨cc, cr⟩, ⟨hcc, hcr⟩, hcccru⟩,
  simp only [prod.fst, prod.snd] at hcc hcr hcccru,
  let x := dist cc (orthogonal_projection hn hc p),
  let y := dist p (orthogonal_projection hn hc p),
  have hy0 : y ≠ 0 := dist_orthogonal_projection_ne_zero_of_not_mem hn hc hp,
  let ycc₂ := (x * x + y * y - cr * cr) / (2 * y),
  let cc₂ := (ycc₂ / y) • (p -ᵥ orthogonal_projection hn hc p : V) +ᵥ cc,
  let cr₂ := real.sqrt (cr * cr + ycc₂ * ycc₂),
  use (cc₂, cr₂),
  simp only [prod.fst, prod.snd],
  have hpo :
    p = (1 : ℝ) • (p -ᵥ orthogonal_projection hn hc p : V) +ᵥ orthogonal_projection hn hc p,
  { simp },
  split,
  { split,
    { refine vadd_mem_of_mem_direction _ (mem_affine_span ℝ V (set.mem_insert_of_mem _ hcc)),
      rw direction_affine_span,
      exact submodule.smul_mem _ _
        (vsub_mem_vector_span ℝ V (set.mem_insert _ _)
                                  (set.mem_insert_of_mem _ (orthogonal_projection_mem hn hc _))) },
    { intros p1 hp1,
      rw [←mul_self_inj_of_nonneg dist_nonneg (real.sqrt_nonneg _),
          real.mul_self_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))],
      cases hp1,
      { rw hp1,
        rw [hpo,
            dist_square_smul_orthogonal_vadd_smul_orthogonal_vadd
              (orthogonal_projection_mem hn hc p) hcc _ _
              (vsub_orthogonal_projection_mem_direction_orthogonal hn hc p),
            ←dist_eq_norm V p, dist_comm _ cc],
        field_simp [hy0],
        ring },
      { rw [dist_square_eq_dist_orthogonal_projection_square_add_dist_orthogonal_projection_square
              hn hc _ (hps hp1),
            orthogonal_projection_vadd_smul_vsub_orthogonal_projection hn hc _ _ hcc, hcr p1 hp1,
            dist_eq_norm V cc₂ cc, vadd_vsub, norm_smul, ←dist_eq_norm V, real.norm_eq_abs,
            abs_div, abs_of_nonneg dist_nonneg, div_mul_cancel _ hy0, abs_mul_abs_self] } } },
  { rintros ⟨cc₃, cr₃⟩ ⟨hcc₃, hcr₃⟩,
    simp only [prod.fst, prod.snd] at hcc₃ hcr₃,
    rw mem_affine_span_insert_iff (orthogonal_projection_mem hn hc p) at hcc₃,
    rcases hcc₃ with ⟨t₃, cc₃', hcc₃', hcc₃⟩,
    have hcr₃' : ∃ r, ∀ p1 ∈ ps, dist p1 cc₃ = r :=
      ⟨cr₃, λ p1 hp1, hcr₃ p1 (set.mem_insert_of_mem _ hp1)⟩,
    rw [exists_dist_eq_iff_exists_dist_orthogonal_projection_eq hn hc hps cc₃, hcc₃,
        orthogonal_projection_vadd_smul_vsub_orthogonal_projection hn hc _ _ hcc₃'] at hcr₃',
    cases hcr₃' with cr₃' hcr₃',
    have hu := hcccru (cc₃', cr₃'),
    simp only [prod.fst, prod.snd] at hu,
    replace hu := hu ⟨hcc₃', hcr₃'⟩,
    rw prod.ext_iff at hu,
    simp only [prod.fst, prod.snd] at hu,
    cases hu with hucc hucr,
    substs hucc hucr,
    have hcr₃val : cr₃ = real.sqrt (cr₃' * cr₃' + (t₃ * y) * (t₃ * y)),
    { cases hnps with p0 hp0,
      rw [←hcr₃ p0 (set.mem_insert_of_mem _ hp0), hcc₃,
          ←mul_self_inj_of_nonneg dist_nonneg (real.sqrt_nonneg _),
          real.mul_self_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)),
          dist_square_eq_dist_orthogonal_projection_square_add_dist_orthogonal_projection_square
            hn hc _ (hps hp0),
          orthogonal_projection_vadd_smul_vsub_orthogonal_projection hn hc _ _ hcc₃', hcr p0 hp0,
          dist_eq_norm V _ cc₃', vadd_vsub, norm_smul, ←dist_eq_norm V p, real.norm_eq_abs,
          ←mul_assoc, mul_comm _ (abs t₃), ←mul_assoc, abs_mul_abs_self],
      ring },
    replace hcr₃ := hcr₃ p (set.mem_insert _ _),
    rw [hpo, hcc₃, hcr₃val, ←mul_self_inj_of_nonneg dist_nonneg (real.sqrt_nonneg _),
        dist_square_smul_orthogonal_vadd_smul_orthogonal_vadd
          (orthogonal_projection_mem hn hc p) hcc₃' _ _
          (vsub_orthogonal_projection_mem_direction_orthogonal hn hc p),
        dist_comm, ←dist_eq_norm V p,
        real.mul_self_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))] at hcr₃,
    change x * x + _ * (y * y) = _ at hcr₃,
    rw [(show x * x + (1 - t₃) * (1 - t₃) * (y * y) =
           x * x + y * y - 2 * y * (t₃ * y) + t₃ * y * (t₃ * y), by ring), add_left_inj] at hcr₃,
    have ht₃ : t₃ = ycc₂ / y,
    { field_simp [←hcr₃, hy0],
      ring },
    subst ht₃,
    change cc₃ = cc₂ at hcc₃,
    congr',
    rw hcr₃val,
    congr' 2,
    field_simp [hy0],
    ring }
end

/-- Given a finite nonempty affinely independent family of points,
there is a unique (circumcenter, circumradius) pair for those points
in the affine subspace they span. -/
lemma exists_unique_dist_eq_of_affine_independent {ι : Type*} [hne : nonempty ι] [fintype ι]
    {p : ι → P} (ha : affine_independent ℝ V p) :
  ∃! cccr : (P × ℝ), cccr.fst ∈ affine_span ℝ V (set.range p) ∧
    ∀ i, dist (p i) cccr.fst = cccr.snd :=
begin
  generalize' hn : fintype.card ι = n,
  unfreezingI { induction n with m hm generalizing ι },
  { exfalso,
    have h := fintype.card_pos_iff.2 hne,
    rw hn at h,
    exact lt_irrefl 0 h },
  { cases m,
    { rw fintype.card_eq_one_iff at hn,
      cases hn with i hi,
      haveI : unique ι := ⟨⟨i⟩, hi⟩,
      use (p i, 0),
      simp only [prod.fst, prod.snd, set.range_unique, affine_subspace.mem_affine_span_singleton],
      split,
      { simp_rw [hi (default ι)],
        use rfl,
        intro i1,
        rw hi i1,
        exact dist_self _ },
      { rintros ⟨cc, cr⟩,
        simp only [prod.fst, prod.snd],
        rintros ⟨rfl, hdist⟩,
        rw hi (default ι),
        congr',
        rw ←hdist (default ι),
        exact dist_self _ } },
    { have i := hne.some,
      let ι2 := {x // x ≠ i},
      have hc : fintype.card ι2 = m + 1,
      { rw fintype.card_of_subtype (finset.univ.filter (λ x, x ≠ i)),
        { rw finset.filter_not,
          simp_rw eq_comm,
          rw [finset.filter_eq, if_pos (finset.mem_univ _),
              finset.card_sdiff (finset.subset_univ _), finset.card_singleton, finset.card_univ,
              hn],
          simp },
        { simp } },
      haveI : nonempty ι2 := fintype.card_pos_iff.1 (hc.symm ▸ nat.zero_lt_succ _),
      have ha2 : affine_independent ℝ V (λ i2 : ι2, p i2) :=
        affine_independent_subtype_of_affine_independent ha _,
      replace hm := hm ha2 hc,
      have hr : set.range p = insert (p i) (set.range (λ i2 : ι2, p i2)),
      { change _ = insert _ (set.range (λ i2 : {x | x ≠ i}, p i2)),
        rw [←set.image_eq_range, ←set.image_univ, ←set.image_insert_eq],
        congr,
        ext,
        simp [classical.em] },
      change ∃! (cccr : P × ℝ), (_ ∧ ∀ i2, (λ q, dist q cccr.fst = cccr.snd) (p i2)),
      conv {
        congr,
        funext,
        conv { congr, skip, rw ←set.forall_range_iff }
      },
      dsimp only,
      rw hr,
      change ∃! (cccr : P × ℝ), (_ ∧ ∀ (i2 : ι2), (λ q, dist q cccr.fst = cccr.snd) (p i2)) at hm,
      conv at hm {
        congr,
        funext,
        conv { congr, skip, rw ←set.forall_range_iff }
      },
      have hs : affine_span ℝ V (insert (p i) (set.range (λ (i2 : ι2), p i2))) =
        affine_span ℝ V (insert (p i) (affine_span ℝ V (set.range (λ (i2 : ι2), p i2)) : set P)),
      { rw [set.insert_eq, set.insert_eq, span_union, span_union, affine_span_coe] },
      rw hs,
      refine exists_unique_dist_eq_of_insert
        ((affine_span_nonempty ℝ V _).2 (set.range_nonempty _))
        (submodule.complete_of_finite_dimensional _)
        (set.range_nonempty _)
        (subset_span_points ℝ V _)
        _
        hm,
      convert not_mem_affine_span_diff_of_affine_independent ha i set.univ,
      change set.range (λ i2 : {x | x ≠ i}, p i2) = _,
      rw ←set.image_eq_range,
      congr,
      ext,
      simp,
      refl } }
end

end euclidean_geometry

namespace affine_space

namespace simplex

open euclidean_geometry

variables {V : Type*} {P : Type*} [inner_product_space V] [metric_space P]
    [euclidean_affine_space V P]

/-- The pair (circumcenter, circumradius) of a simplex. -/
def circumcenter_circumradius {n : ℕ} (s : simplex ℝ V P n) : (P × ℝ) :=
(exists_unique_dist_eq_of_affine_independent s.independent).some

/-- The property satisfied by the (circumcenter, circumradius) pair. -/
lemma circumcenter_circumradius_unique_dist_eq {n : ℕ} (s : simplex ℝ V P n) :
  (s.circumcenter_circumradius.fst ∈ affine_span ℝ V (set.range s.points) ∧
    ∀ i, dist (s.points i) s.circumcenter_circumradius.fst = s.circumcenter_circumradius.snd) ∧
  (∀ cccr : (P × ℝ), (cccr.fst ∈ affine_span ℝ V (set.range s.points) ∧
    ∀ i, dist (s.points i) cccr.fst = cccr.snd) → cccr = s.circumcenter_circumradius) :=
(exists_unique_dist_eq_of_affine_independent s.independent).some_spec

/-- The circumcenter of a simplex. -/
def circumcenter {n : ℕ} (s : simplex ℝ V P n) : P :=
s.circumcenter_circumradius.fst

/-- The circumradius of a simplex. -/
def circumradius {n : ℕ} (s : simplex ℝ V P n) : ℝ :=
s.circumcenter_circumradius.snd

/-- The circumcenter lies in the affine span. -/
lemma circumcenter_mem_affine_span {n : ℕ} (s : simplex ℝ V P n) :
  s.circumcenter ∈ affine_span ℝ V (set.range s.points) :=
s.circumcenter_circumradius_unique_dist_eq.1.1

/-- All points have distance from the circumcenter equal to the
circumradius. -/
lemma dist_circumcenter_eq_circumradius {n : ℕ} (s : simplex ℝ V P n) :
  ∀ i, dist (s.points i) s.circumcenter = s.circumradius :=
s.circumcenter_circumradius_unique_dist_eq.1.2

/-- Given a point in the affine span from which all the points are
equidistant, that point is the circumcenter. -/
lemma eq_circumcenter_of_dist_eq {n : ℕ} (s : simplex ℝ V P n) {p : P}
    (hp : p ∈ affine_span ℝ V (set.range s.points)) {r : ℝ} (hr : ∀ i, dist (s.points i) p = r) :
  p = s.circumcenter :=
begin
  have h := s.circumcenter_circumradius_unique_dist_eq.2 (p, r),
  simp only [hp, hr, forall_const, eq_self_iff_true, and_self, prod.ext_iff] at h,
  exact h.1
end

/-- Given a point in the affine span from which all the points are
equidistant, that distance is the circumradius. -/
lemma eq_circumradius_of_dist_eq {n : ℕ} (s : simplex ℝ V P n) {p : P}
    (hp : p ∈ affine_span ℝ V (set.range s.points)) {r : ℝ} (hr : ∀ i, dist (s.points i) p = r) :
  r = s.circumradius :=
begin
  have h := s.circumcenter_circumradius_unique_dist_eq.2 (p, r),
  simp only [hp, hr, forall_const, eq_self_iff_true, and_self, prod.ext_iff] at h,
  exact h.2
end

end simplex

end affine_space
