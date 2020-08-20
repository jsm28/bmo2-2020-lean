-- Existence and uniqueness of Monge point / orthocenter (in
-- preparation for adding to mathlib).

import geometry.euclidean
import tactic.derive_fintype

noncomputable theory
open_locale big_operators
open_locale classical

namespace affine

namespace simplex

open affine_subspace euclidean_geometry

variables {V : Type*} {P : Type*} [inner_product_space V] [metric_space P]
    [normed_add_torsor V P]

/-- An index type for the vertices of a simplex plus its circumcenter.
This is for use in calculations where it is convenient to work with
affine combinations of vertices together with the circumcenter.  (An
equivalent form sometimes used in the literature is placing the
circumcenter at the origin and working with vectors for the vertices.) -/
@[derive fintype]
inductive points_with_circumcenter_index (n : ℕ)
| point_index : fin (n + 1) → points_with_circumcenter_index
| circumcenter_index : points_with_circumcenter_index

open points_with_circumcenter_index

instance points_with_circumcenter_index_inhabited (n : ℕ) :
  inhabited (points_with_circumcenter_index n) :=
⟨circumcenter_index⟩

/-- `point_index` as an embedding. -/
def point_index_embedding (n : ℕ) : fin (n + 1) ↪ points_with_circumcenter_index n :=
⟨λ i, point_index i, λ _ _ h, by injection h⟩

/-- The sum of a function over `points_with_circumcenter_index`. -/
lemma sum_points_with_circumcenter {α : Type*} [add_comm_monoid α] {n : ℕ}
  (f : points_with_circumcenter_index n → α) :
  ∑ i, f i = (∑ (i : fin (n + 1)), f (point_index i)) + f circumcenter_index :=
begin
  have h : finset.univ = insert circumcenter_index (finset.univ.map (point_index_embedding n)),
  { ext x,
    refine ⟨λ h, _, λ _, finset.mem_univ _⟩,
    cases x with i,
    { exact finset.mem_insert_of_mem (finset.mem_map_of_mem _ (finset.mem_univ i)) },
    { exact finset.mem_insert_self _ _ } },
  change _ = ∑ i, f (point_index_embedding n i) + _,
  rw [add_comm, h, ←finset.sum_map, finset.sum_insert],
  simp_rw [finset.mem_map, not_exists],
  intros x hx h,
  injection h
end

include V

/-- The vertices of a simplex plus its circumcenter. -/
def points_with_circumcenter {n : ℕ} (s : simplex ℝ P n) : points_with_circumcenter_index n → P
| (point_index i) := s.points i
| circumcenter_index := s.circumcenter

/-- `points_with_circumcenter`, applied to a `point_index` value,
equals `points` applied to that value. -/
@[simp] lemma points_with_circumcenter_point {n : ℕ} (s : simplex ℝ P n) (i : fin (n + 1)) :
  s.points_with_circumcenter (point_index i) = s.points i :=
rfl

/-- `points_with_circumcenter`, applied to `circumcenter_index`, equals the
circumcenter. -/
@[simp] lemma points_with_circumcenter_eq_circumcenter {n : ℕ} (s : simplex ℝ P n) :
  s.points_with_circumcenter circumcenter_index = s.circumcenter :=
rfl

omit V

/-- The weights for a single vertex of a simplex, in terms of
`points_with_circumcenter`. -/
def point_weights_with_circumcenter {n : ℕ} (i : fin (n + 1)) :
  points_with_circumcenter_index n → ℝ
| (point_index j) := if j = i then 1 else 0
| circumcenter_index := 0

/-- `point_weights_with_circumcenter` sums to 1. -/
@[simp] lemma sum_point_weights_with_circumcenter {n : ℕ} (i : fin (n + 1)) :
  ∑ j, point_weights_with_circumcenter i j = 1 :=
begin
  convert finset.sum_ite_eq' finset.univ (point_index i) (function.const _ (1 : ℝ)),
  { ext j,
    cases j;
      simp [point_weights_with_circumcenter] },
  { simp }
end

include V

/-- A single vertex, in terms of `points_with_circumcenter`. -/
lemma point_eq_affine_combination_of_points_with_circumcenter {n : ℕ} (s : simplex ℝ P n)
    (i : fin (n + 1)) :
  s.points i = 
    (finset.univ : finset (points_with_circumcenter_index n)).affine_combination
      s.points_with_circumcenter (point_weights_with_circumcenter i) :=
begin
  rw ←points_with_circumcenter_point,
  symmetry,
  refine finset.affine_combination_of_eq_one_of_eq_zero _ _ _
    (finset.mem_univ _)
    (by simp [point_weights_with_circumcenter])
    _,
  intros i hi hn,
  cases i,
  { have h : i_1 ≠ i := λ h, hn (h ▸ rfl),
    simp [point_weights_with_circumcenter, h] },
  { refl }
end

omit V

/-- The weights for the centroid of some vertices of a simplex, in
terms of `points_with_circumcenter`. -/
def centroid_weights_with_circumcenter {n : ℕ} (fs : finset (fin (n + 1)))
  : points_with_circumcenter_index n → ℝ
| (point_index i) := if i ∈ fs then ((finset.card fs : ℝ) ⁻¹) else 0
| circumcenter_index := 0

/-- `centroid_weights_with_circumcenter` sums to 1, if the `finset` is
nonempty. -/
@[simp] lemma sum_centroid_weights_with_circumcenter {n : ℕ} {fs : finset (fin (n + 1))} (h : fs.nonempty) :
  ∑ i, centroid_weights_with_circumcenter fs i = 1 :=
begin
  simp_rw [sum_points_with_circumcenter, centroid_weights_with_circumcenter, add_zero,
           ←fs.sum_centroid_weights_eq_one_of_nonempty ℝ h,
           set.sum_indicator_subset _ fs.subset_univ],
  congr,
  ext i,
  congr
end

include V

/-- The centroid of some vertices of a simplex, in terms of
`points_with_circumcenter`. -/
lemma centroid_eq_affine_combination_of_points_with_circumcenter {n : ℕ} (s : simplex ℝ P n)
    (fs : finset (fin (n + 1))) :
  fs.centroid ℝ s.points =
    (finset.univ : finset (points_with_circumcenter_index n)).affine_combination
      s.points_with_circumcenter (centroid_weights_with_circumcenter fs) :=
begin
  simp_rw [finset.centroid_def, finset.affine_combination_apply,
           finset.weighted_vsub_of_point_apply, sum_points_with_circumcenter,
           centroid_weights_with_circumcenter, points_with_circumcenter_point, zero_smul,
           add_zero, finset.centroid_weights,
           set.sum_indicator_subset_of_eq_zero
             (function.const (fin (n + 1)) ((finset.card fs : ℝ)⁻¹))
             (λ i wi, wi • (s.points i -ᵥ classical.choice add_torsor.nonempty))
             fs.subset_univ
             (λ i, zero_smul ℝ _),
           set.indicator_apply],
  congr,
  ext i,
  congr
end

omit V

/-- The weights for the circumcenter of a simplex, in terms of
`points_with_circumcenter`. -/
def circumcenter_weights_with_circumcenter (n : ℕ) : points_with_circumcenter_index n → ℝ
| (point_index i) := 0
| circumcenter_index := 1

/-- `circumcenter_weights_with_circumcenter` sums to 1. -/
@[simp] lemma sum_circumcenter_weights_with_circumcenter (n : ℕ) :
  ∑ i, circumcenter_weights_with_circumcenter n i = 1 :=
begin
  convert finset.sum_ite_eq' finset.univ circumcenter_index (function.const _ (1 : ℝ)),
  { ext j,
    cases j;
      simp [circumcenter_weights_with_circumcenter] },
  { simp },
  { exact classical.dec_eq _ }
end

include V

/-- The circumcenter of a simplex, in terms of
`points_with_circumcenter`. -/
lemma circumcenter_eq_affine_combination_of_points_with_circumcenter {n : ℕ}
    (s : simplex ℝ P n) :
  s.circumcenter = (finset.univ : finset (points_with_circumcenter_index n)).affine_combination
    s.points_with_circumcenter (circumcenter_weights_with_circumcenter n) :=
begin
  rw ←points_with_circumcenter_eq_circumcenter,
  symmetry,
  refine finset.affine_combination_of_eq_one_of_eq_zero _ _ _ (finset.mem_univ _) rfl _,
  intros i hi hn,
  cases i,
  { refl },
  { exact false.elim (hn rfl) }
end

/-- The Monge point of a simplex (in 2 or more dimensions) is a
generalization of the orthocenter of a triangle.  It is defined to be
the intersection of the Monge planes, where a Monge plane is the
(n-1)-dimensional affine subspace of the subspace spanned by the
simplex that passes through the centroid of an (n-2)-dimensional face
and is orthogonal to the opposite edge (in 2 dimensions, this is the
same as an altitude).  The circumcenter O, centroid G and Monge point
M are collinear in that order on the Euler line, with OG : GM = (n-1)
: 2.  Here, we use that ratio to define the Monge point (so resulting
in a point that equals the centroid in 0 or 1 dimensions), and then
show in subsequent lemmas that the point so defined lies in the Monge
planes and is their unique point of intersection. -/
def monge_point {n : ℕ} (s : simplex ℝ P n) : P :=
(((n + 1 : ℕ) : ℝ) / (((n - 1) : ℕ) : ℝ)) •
  ((finset.univ : finset (fin (n + 1))).centroid ℝ s.points -ᵥ s.circumcenter : V) +ᵥ
  s.circumcenter

/-- The position of the Monge point in relation to the circumcenter
and centroid. -/
lemma monge_point_eq_smul_vsub_vadd_circumcenter {n : ℕ} (s : simplex ℝ P n) :
  s.monge_point = (((n + 1 : ℕ) : ℝ) / (((n - 1) : ℕ) : ℝ)) •
    ((finset.univ : finset (fin (n + 1))).centroid ℝ s.points -ᵥ s.circumcenter : V) +ᵥ
    s.circumcenter :=
rfl

/-- The Monge point lies in the affine span. -/
lemma monge_point_mem_affine_span {n : ℕ} (s : simplex ℝ P n) :
  s.monge_point ∈ affine_span ℝ (set.range s.points) :=
affine_subspace.smul_vsub_vadd_mem _ _ _ _ _
  (centroid_mem_affine_span_of_card_eq_add_one ℝ _ (finset.card_fin (n + 1)))
  s.circumcenter_mem_affine_span
  s.circumcenter_mem_affine_span

omit V

/-- The weights for the Monge point of an (n+2)-simplex, in terms of
`points_with_circumcenter`. -/
def monge_point_weights_with_circumcenter (n : ℕ) : points_with_circumcenter_index (n + 2) → ℝ
| (point_index i) := (((n + 1) : ℕ) : ℝ)⁻¹
| circumcenter_index := (-2 / (((n + 1) : ℕ) : ℝ))

/-- `monge_point_weights_with_circumcenter` sums to 1. -/
@[simp] lemma sum_monge_point_weights_with_circumcenter (n : ℕ) :
  ∑ i, monge_point_weights_with_circumcenter n i = 1 :=
begin
  simp_rw [sum_points_with_circumcenter, monge_point_weights_with_circumcenter, finset.sum_const,
           finset.card_fin, nsmul_eq_mul],
  have hn1 : (n + 1 : ℝ) ≠ 0,
  { norm_cast,
    exact nat.succ_ne_zero _ },
  field_simp [hn1],
  ring
end

include V

/-- The Monge point of an (n+2)-simplex, in terms of
`points_with_circumcenter`. -/
lemma monge_point_eq_affine_combination_of_points_with_circumcenter {n : ℕ}
    (s : simplex ℝ P (n + 2)) :
  s.monge_point = (finset.univ : finset (points_with_circumcenter_index (n + 2))).affine_combination
    s.points_with_circumcenter (monge_point_weights_with_circumcenter n) :=
begin
  rw [monge_point_eq_smul_vsub_vadd_circumcenter,
      centroid_eq_affine_combination_of_points_with_circumcenter,
      circumcenter_eq_affine_combination_of_points_with_circumcenter,
      finset.affine_combination_vsub, ←linear_map.map_smul,
      finset.weighted_vsub_vadd_affine_combination],
  congr,
  ext i,
  rw [pi.add_apply, pi.smul_apply, smul_eq_mul, pi.sub_apply],
  have hn1 : (n + 1 : ℝ) ≠ 0,
  { norm_cast,
    exact nat.succ_ne_zero _ },
  cases i;
    simp_rw [centroid_weights_with_circumcenter, circumcenter_weights_with_circumcenter,
             monge_point_weights_with_circumcenter];
    rw [nat.add_sub_assoc (dec_trivial : 1 ≤ 2), (dec_trivial : 2 - 1 = 1)],
  { rw [if_pos (finset.mem_univ _), sub_zero, add_zero, finset.card_fin],
    have hn3 : (n + 2 + 1 : ℝ) ≠ 0,
    { norm_cast,
      exact nat.succ_ne_zero _ },
    field_simp [hn1, hn3],
    ring },
  { field_simp [hn1],
    ring }
end

omit V

/-- The weights for the Monge point of an (n+2)-simplex, minus the
centroid of an n-dimensional face, in terms of
`points_with_circumcenter`.  This definition is only valid when `i₁ ≠
i₂`. -/
def monge_point_vsub_face_centroid_weights_with_circumcenter {n : ℕ} (i₁ i₂ : fin (n + 3)) :
  points_with_circumcenter_index (n + 2) → ℝ
| (point_index i) := if i = i₁ ∨ i = i₂ then (((n + 1) : ℕ) : ℝ)⁻¹ else 0
| circumcenter_index := (-2 / (((n + 1) : ℕ) : ℝ))

/-- `monge_point_vsub_face_centroid_weights_with_circumcenter` is the
result of subtracting `centroid_weights_with_circumcenter` from
`monge_point_weights_with_circumcenter`. -/
lemma monge_point_vsub_face_centroid_weights_with_circumcenter_eq_sub {n : ℕ}
    {i₁ i₂ : fin (n + 3)} (h : i₁ ≠ i₂) :
  monge_point_vsub_face_centroid_weights_with_circumcenter i₁ i₂ =
    monge_point_weights_with_circumcenter n -
      centroid_weights_with_circumcenter (finset.univ \ {i₁, i₂}) :=
begin
  ext i,
  cases i,
  { rw [pi.sub_apply, monge_point_weights_with_circumcenter, centroid_weights_with_circumcenter,
        monge_point_vsub_face_centroid_weights_with_circumcenter],
    have hu : finset.card (finset.univ \ {i₁, i₂} : finset (fin (n + 3))) = n + 1,
    { rw [finset.card_univ_diff, fintype.card_fin],
      simp [h] },
    rw hu,
    by_cases hi : i = i₁ ∨ i = i₂;
      simp [hi] },
  { simp [monge_point_weights_with_circumcenter, centroid_weights_with_circumcenter,
          monge_point_vsub_face_centroid_weights_with_circumcenter] }
end

/-- `monge_point_vsub_face_centroid_weights_with_circumcenter` sums to 0. -/
@[simp] lemma sum_monge_point_vsub_face_centroid_weights_with_circumcenter {n : ℕ}
    {i₁ i₂ : fin (n + 3)} (h : i₁ ≠ i₂) :
  ∑ i, monge_point_vsub_face_centroid_weights_with_circumcenter i₁ i₂ i = 0 :=
begin
  rw monge_point_vsub_face_centroid_weights_with_circumcenter_eq_sub h,
  simp_rw [pi.sub_apply, finset.sum_sub_distrib, sum_monge_point_weights_with_circumcenter],
  rw [sum_centroid_weights_with_circumcenter, sub_self],
  rw [←finset.card_pos, finset.card_univ_diff],
  simp [h]
end

include V

/-- The Monge point of an (n+2)-simplex, minus the centroid of an
n-dimensional face, in terms of `points_with_circumcenter`. -/
lemma monge_point_vsub_face_centroid_eq_weighted_vsub_of_points_with_circumcenter {n : ℕ}
    (s : simplex ℝ P (n + 2)) {i₁ i₂ : fin (n + 3)} (h : i₁ ≠ i₂) :
  s.monge_point -ᵥ (finset.univ \ {i₁, i₂}).centroid ℝ s.points =
    (finset.univ : finset (points_with_circumcenter_index (n + 2))).weighted_vsub
      s.points_with_circumcenter (monge_point_vsub_face_centroid_weights_with_circumcenter i₁ i₂) :=
by simp_rw [monge_point_eq_affine_combination_of_points_with_circumcenter,
            centroid_eq_affine_combination_of_points_with_circumcenter,
            finset.affine_combination_vsub,
            monge_point_vsub_face_centroid_weights_with_circumcenter_eq_sub h]

/-- The Monge point of an (n+2)-simplex, minus the centroid of an
n-dimensional face, is orthogonal to the difference of the two
vertices not in that face. -/
lemma inner_monge_point_vsub_face_centroid_vsub {n : ℕ} (s : simplex ℝ P (n + 2))
    {i₁ i₂ : fin (n + 3)} (h : i₁ ≠ i₂) :
  inner (s.monge_point -ᵥ (finset.univ \ {i₁, i₂}).centroid ℝ s.points)
        (s.points i₁ -ᵥ s.points i₂) = 0 :=
begin
  simp_rw [monge_point_vsub_face_centroid_eq_weighted_vsub_of_points_with_circumcenter s h,
           point_eq_affine_combination_of_points_with_circumcenter,
           finset.affine_combination_vsub],
  have hs : ∑ i, (point_weights_with_circumcenter i₁ - point_weights_with_circumcenter i₂) i = 0,
  { simp },
  rw [inner_weighted_vsub _ (sum_monge_point_vsub_face_centroid_weights_with_circumcenter h) _ hs,
      sum_points_with_circumcenter, points_with_circumcenter_eq_circumcenter],
  simp only [monge_point_vsub_face_centroid_weights_with_circumcenter,
             points_with_circumcenter_point],
  let fs : finset (fin (n + 3)) := {i₁, i₂},
  have hfs : ∀ i : fin (n + 3),
    i ∉ fs → (i ≠ i₁ ∧ i ≠ i₂),
  { intros i hi,
    repeat { split },
    all_goals { intro hj, simpa [←hj] using hi } },
  rw ←finset.sum_subset fs.subset_univ _,
  { simp_rw [sum_points_with_circumcenter, points_with_circumcenter_eq_circumcenter,
             points_with_circumcenter_point, pi.sub_apply, point_weights_with_circumcenter],
    rw [←finset.sum_subset fs.subset_univ _],
    { simp_rw [finset.sum_insert (finset.not_mem_singleton.2 h), finset.sum_singleton],
      repeat { rw ←finset.sum_subset fs.subset_univ _ },
      { simp_rw [finset.sum_insert (finset.not_mem_singleton.2 h), finset.sum_singleton],
        simp [h, h.symm, dist_comm (s.points i₁)] },
      all_goals { intros i hu hi, simp [hfs i hi] } },
    { intros i hu hi,
      simp [hfs i hi, point_weights_with_circumcenter] } },
  { intros i hu hi,
    simp [hfs i hi] }
end

/-- A Monge plane of an (n+2)-simplex is the (n+1)-dimensional affine
subspace of the subspace spanned by the simplex that passes through
the centroid of an n-dimensional face and is orthogonal to the
opposite edge (in 2 dimensions, this is the same as an altitude).
This definition is only intended to be used when `i₁ ≠ i₂`. -/
def monge_plane {n : ℕ} (s : simplex ℝ P (n + 2)) (i₁ i₂ : fin (n + 3)) :
  affine_subspace ℝ P :=
mk' ((finset.univ \ {i₁, i₂}).centroid ℝ s.points) (submodule.span ℝ {s.points i₁ -ᵥ s.points i₂}).orthogonal ⊓
  affine_span ℝ (set.range s.points)

/-- The definition of a Monge plane. -/
lemma monge_plane_def {n : ℕ} (s : simplex ℝ P (n + 2)) (i₁ i₂ : fin (n + 3)) :
  s.monge_plane i₁ i₂ = mk' ((finset.univ \ {i₁, i₂}).centroid ℝ s.points)
                            (submodule.span ℝ {s.points i₁ -ᵥ s.points i₂}).orthogonal ⊓
                          affine_span ℝ (set.range s.points) :=
rfl

/-- The Monge plane associated with vertices `i₁` and `i₂` equals that
associated with `i₂` and `i₁`. -/
lemma monge_plane_comm {n : ℕ} (s : simplex ℝ P (n + 2)) (i₁ i₂ : fin (n + 3)) :
  s.monge_plane i₁ i₂ = s.monge_plane i₂ i₁ :=
begin
  simp_rw monge_plane_def,
  congr' 3,
  { congr' 1,
    ext,
    simp,
    tauto },
  { ext,
    simp_rw submodule.mem_span_singleton,
    split,
    all_goals { rintros ⟨r, rfl⟩, use -r, rw [neg_smul, ←smul_neg, neg_vsub_eq_vsub_rev] } }
end

/-- The Monge point lies in the Monge planes. -/
lemma monge_point_mem_monge_plane {n : ℕ} (s : simplex ℝ P (n + 2)) {i₁ i₂ : fin (n + 3)}
    (h : i₁ ≠ i₂) : s.monge_point ∈ s.monge_plane i₁ i₂ :=
begin
  rw [monge_plane_def, mem_inf_iff, ←vsub_right_mem_direction_iff_mem (self_mem_mk' _ _),
      direction_mk', submodule.mem_orthogonal'],
  refine ⟨_, s.monge_point_mem_affine_span⟩,
  intros v hv,
  rw submodule.mem_span_singleton at hv,
  rcases hv with ⟨r, rfl⟩,
  rw [inner_smul_right, s.inner_monge_point_vsub_face_centroid_vsub h, mul_zero]
end

-- This doesn't actually need the `i₁ ≠ i₂` hypothesis, but it's
-- convenient for the proof and `monge_plane` isn't intended to be
-- useful without that hypothesis.
/-- The direction of a Monge plane. -/
lemma direction_monge_plane {n : ℕ} (s : simplex ℝ P (n + 2)) {i₁ i₂ : fin (n + 3)} (h : i₁ ≠ i₂) :
  (s.monge_plane i₁ i₂).direction = (submodule.span ℝ {s.points i₁ -ᵥ s.points i₂}).orthogonal ⊓
    vector_span ℝ (set.range s.points) :=
by rw [monge_plane_def, direction_inf_of_mem_inf (s.monge_point_mem_monge_plane h), direction_mk',
       direction_affine_span]

/-- The Monge point is the only point in all the Monge planes from any
one vertex. -/
lemma eq_monge_point_of_forall_mem_monge_plane {n : ℕ} {s : simplex ℝ P (n + 2)}
    {i₁ : fin (n + 3)} {p : P} (h : ∀ i₂, i₁ ≠ i₂ → p ∈ s.monge_plane i₁ i₂) :
  p = s.monge_point :=
begin
  rw ←@vsub_eq_zero_iff_eq V,
  have h' : ∀ i₂, i₁ ≠ i₂ → p -ᵥ s.monge_point ∈
    (submodule.span ℝ {s.points i₁ -ᵥ s.points i₂}).orthogonal ⊓ vector_span ℝ (set.range s.points),
  { intros i₂ hne,
    rw [←s.direction_monge_plane hne,
        vsub_right_mem_direction_iff_mem (s.monge_point_mem_monge_plane hne)],
    exact h i₂ hne },
  have hi : p -ᵥ s.monge_point ∈ ⨅ (i₂ : {i // i₁ ≠ i}),
    (submodule.span ℝ ({s.points i₁ -ᵥ s.points i₂}: set V)).orthogonal,
  { rw submodule.mem_infi,
    exact λ i, (submodule.mem_inf.1 (h' i i.property)).1 },
  rw [submodule.infi_orthogonal, ←submodule.span_Union] at hi,
  have hu : (⋃ (i : {i // i₁ ≠ i}), ({s.points i₁ -ᵥ s.points i} : set V)) =
    (-ᵥ) (s.points i₁) '' (s.points '' (set.univ \ {i₁})),
  { rw [set.image_image],
    ext x,
    simp_rw [set.mem_Union, set.mem_image, set.mem_singleton_iff, set.mem_diff_singleton],
    split,
    { rintros ⟨i, rfl⟩,
      use [i, ⟨set.mem_univ _, i.property.symm⟩] },
    { rintros ⟨i, ⟨hiu, hi⟩, rfl⟩,
      use [⟨i, hi.symm⟩, rfl] } },
  rw [hu, ←vector_span_image_eq_span_vsub_set_left_ne ℝ _ (set.mem_univ _),
      set.image_univ] at hi,
  have hv : p -ᵥ s.monge_point ∈ vector_span ℝ (set.range s.points),
  { let s₁ : finset (fin (n + 3)) := finset.univ.erase i₁,
    obtain ⟨i₂, h₂⟩ :=
      finset.card_pos.1 (show 0 < finset.card s₁, by simp [finset.card_erase_of_mem]),
    have h₁₂ : i₁ ≠ i₂ := (finset.ne_of_mem_erase h₂).symm,
    exact (submodule.mem_inf.1 (h' i₂ h₁₂)).2 },
  exact submodule.disjoint_def.1 ((vector_span ℝ (set.range s.points)).orthogonal_disjoint)
    _ hv hi,
end

/-- An altitude of a simplex is the line that passes through a vertex
and is orthogonal to the opposite face. -/
def altitude {n : ℕ} (s : simplex ℝ P (n + 1)) (i : fin (n + 2)) :
  affine_subspace ℝ P :=
mk' (s.points i) (affine_span ℝ (s.points '' ↑(finset.univ.erase i))).direction.orthogonal ⊓
  affine_span ℝ (set.range s.points)

/-- The definition of an altitude. -/
lemma altitude_def {n : ℕ} (s : simplex ℝ P (n + 1)) (i : fin (n + 2)) :
  s.altitude i = mk' (s.points i)
                     (affine_span ℝ (s.points '' ↑(finset.univ.erase i))).direction.orthogonal ⊓
    affine_span ℝ (set.range s.points) :=
rfl

end simplex

namespace triangle

open simplex

variables {V : Type*} {P : Type*} [inner_product_space V] [metric_space P]
    [normed_add_torsor V P]

include V

/-- The orthocenter of a triangle is the intersection of its
altitudes.  It is defined here as the 2-dimensional case of the
Monge point. -/
def orthocenter (t : triangle ℝ P) : P := t.monge_point

/-- The orthocenter equals the Monge point. -/
lemma orthocenter_eq_monge_point (t : triangle ℝ P) :
  t.orthocenter = t.monge_point :=
rfl

/-- The position of the orthocenter in relation to the circumcenter
and centroid. -/
lemma orthocenter_eq_smul_vsub_vadd_circumcenter (t : triangle ℝ P) :
  t.orthocenter = (3 : ℝ) •
    ((finset.univ : finset (fin 3)).centroid ℝ t.points -ᵥ t.circumcenter : V) +ᵥ t.circumcenter :=
begin
  rw [orthocenter_eq_monge_point, monge_point_eq_smul_vsub_vadd_circumcenter],
  norm_num
end

/-- The orthocenter lies in the affine span. -/
lemma orthocenter_mem_affine_span (t : triangle ℝ P) :
  t.orthocenter ∈ affine_span ℝ (set.range t.points) :=
t.monge_point_mem_affine_span

/-- In the case of a triangle, altitudes are the same thing as Monge
planes. -/
lemma altitude_eq_monge_plane (t : triangle ℝ P) {i₁ i₂ i₃ : fin 3} (h₁₂ : i₁ ≠ i₂)
    (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
  t.altitude i₁ = t.monge_plane i₂ i₃ :=
begin
  have hu : (finset.univ : finset (fin 3)) = {i₁, i₂, i₃},
  { refine (finset.eq_of_subset_of_card_le (finset.subset_univ _) _).symm,
    simp [h₁₂, h₁₃, h₂₃] },
  have hs : (finset.univ \ {i₂, i₃} : finset (fin 3)) = {i₁},
  { rw [hu, finset.insert_sdiff_of_not_mem {i₂, i₃}],
    { simp },
    { simp [h₁₂, h₁₃] } },
  have he : finset.univ.erase i₁ = {i₂, i₃},
  { rw [hu, finset.erase_insert],
    simp [h₁₂, h₁₃] },
  rw [monge_plane_def, altitude_def, direction_affine_span, hs, he, finset.centroid_singleton,
      finset.coe_insert, finset.coe_singleton,
      vector_span_image_eq_span_vsub_set_left_ne ℝ _ (set.mem_insert i₂ _)],
  simp [h₂₃, submodule.span_insert_eq_span]
end

/-- The orthocenter lies in the altitudes. -/
lemma orthocenter_mem_altitude (t : triangle ℝ P) {i₁ : fin 3} :
  t.orthocenter ∈ t.altitude i₁ :=
begin
  let s₂₃ : finset (fin 3) := finset.univ.erase i₁,
  obtain ⟨i₂, h₂⟩ :=
    finset.card_pos.1 (show 0 < finset.card s₂₃, by simp [finset.card_erase_of_mem]),
  have h₁₂ : i₁ ≠ i₂ := (finset.ne_of_mem_erase h₂).symm,
  let s₃ : finset (fin 3) := s₂₃.erase i₂,
  obtain ⟨i₃, h₃⟩ :=
    finset.card_pos.1 (show 0 < finset.card s₃, by simp [finset.card_erase_of_mem, h₂]),
  have h₂₃ : i₂ ≠ i₃ := (finset.ne_of_mem_erase h₃).symm,
  have h₁₃ : i₁ ≠ i₃ := (finset.ne_of_mem_erase (finset.mem_of_mem_erase h₃)).symm,
  rw [orthocenter_eq_monge_point, t.altitude_eq_monge_plane h₁₂ h₁₃ h₂₃],
  exact t.monge_point_mem_monge_plane h₂₃
end

/-- The orthocenter is the only point lying in any two of the
altitudes. -/
lemma eq_orthocenter_of_forall_mem_altitude {t : triangle ℝ P} {i₁ i₂ : fin 3} {p : P}
    (h₁₂ : i₁ ≠ i₂) (h₁ : p ∈ t.altitude i₁) (h₂ : p ∈ t.altitude i₂) :
  p = t.orthocenter :=
begin
  let s₃ : finset (fin 3) := (finset.univ.erase i₁).erase i₂,
  have hc₃ : finset.card s₃ = 1,
  { simp [finset.card_erase_of_mem, finset.mem_erase_of_ne_of_mem, h₁₂.symm] },
  obtain ⟨i₃, h₃⟩ := finset.card_pos.1 (show 0 < finset.card s₃, by simp [hc₃]),
  have h₂₃ : i₂ ≠ i₃ := (finset.ne_of_mem_erase h₃).symm,
  have h₁₃ : i₁ ≠ i₃ := (finset.ne_of_mem_erase (finset.mem_of_mem_erase h₃)).symm,
  rw t.altitude_eq_monge_plane h₁₃ h₁₂ h₂₃.symm at h₁,
  rw t.altitude_eq_monge_plane h₂₃ h₁₂.symm h₁₃.symm at h₂,
  rw orthocenter_eq_monge_point,
  have ha : ∀ i, i₃ ≠ i → p ∈ t.monge_plane i₃ i,
  { intros i hi,
    by_cases hi₂ : i = i₂,
    { exact hi₂.symm ▸ h₁ },
    { let s₁ : finset (fin 3) := (finset.univ.erase i₂).erase i₃,
      have hc₁ : finset.card s₁ = 1,
      { simp [finset.card_erase_of_mem, finset.mem_erase_of_ne_of_mem, h₂₃.symm] },
      rw finset.card_eq_one at hc₁,
      rcases hc₁ with ⟨i', hi'⟩,
      have hi₁s₁ : i₁ ∈ s₁, { simp [finset.mem_erase_of_ne_of_mem, h₁₂, h₁₃] },
      have his₁ : i ∈ s₁, { simp [finset.mem_erase_of_ne_of_mem, hi₂, hi.symm] },
      rw [hi', finset.mem_singleton] at hi₁s₁ his₁,
      rw [his₁, hi₁s₁.symm],
      exact h₂ } },
  exact eq_monge_point_of_forall_mem_monge_plane ha
end

end triangle

end affine
