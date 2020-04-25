-- BMO2 2020 problem 4: lemmas of possibly more general use.  Are any
-- of these already in mathlib, possibly under a different name or in
-- a more general form, or should any of them be?

import data.real.cardinality
import topology.instances.real

open real

-- This is meaningful for general topological (semi)fields, not just ℝ
-- (so for complex and nnreal, for example), but mathlib does not have
-- topological fields or semifields.

/-- Continuity at a point of the result of dividing two functions
continuous at that point, where the denominator is nonzero. -/
lemma continuous_at.div {α : Type} [topological_space α] {f : α → ℝ} {g : α → ℝ} {x : α}
    (hf : continuous_at f x) (hg : continuous_at g x) (hnz : g x ≠ 0) :
  continuous_at (λ x, f x / g x) x :=
continuous_at.mul hf (continuous_at.comp (tendsto_inv hnz) hg)

-- The following proofs that intervals of reals are uncountable are
-- probably much more complicated than necessary.

-- The interval [0, 1) is uncountable (auxiliary lemma).
lemma not_countable_real_Ico_0_1 : ¬ set.countable (set.Ico (0 : ℝ) 1) :=
begin
  intro h,
  have hm : ∀ m : ℝ, set.countable (set.Ico m (m + 1)),
  { intro m,
    convert set.countable_image (λ x : ℝ, m + x) h,
    ext,
    split,
    { intro h,
      cases h with h1 h2,
      use x - m,
      split,
      { erw set.mem_set_of_eq,
        split,
        { linarith },
        { linarith } },
      { simp } },
    { intro h,
      cases h with a ha,
      cases ha with ha1 ha2,
      erw set.mem_set_of_eq at ha1,
      unfold at ha2,
      cases ha1 with ha1a ha1b,
      split,
      { linarith },
      { linarith } } },
  have hu : (set.univ : set ℝ) = ⋃ m : ℤ, (set.Ico (m : ℝ) ((m : ℝ) + 1)),
  { symmetry,
    apply set.eq_univ_of_forall,
    intro y,
    rw set.mem_Union,
    use floor y,
    erw set.mem_set_of_eq,
    split,
    { exact floor_le y },
    { exact lt_floor_add_one y } },
  apply cardinal.not_countable_real,
  rw hu,
  apply set.countable_Union,
  intro m,
  exact hm (m : ℝ)
end

-- The interval (0, 1) is uncountable (auxiliary lemma).
lemma not_countable_real_Ioo_0_1 : ¬ set.countable (set.Ioo (0 : ℝ) 1) :=
begin
  intro h,
  have hu : set.Ico (0 : ℝ) 1 = set.Ioo (0 : ℝ) 1 ∪ {0},
  { ext,
    erw [set.union_singleton, set.mem_insert_iff, set.mem_set_of_eq, set.mem_set_of_eq],
    split,
    { intro h,
      cases h with h1 h2,
      by_cases h0 : x = 0,
      { left,
        exact h0 },
      { right,
        split,
        { have hz : 0 ≠ x,
          { intro heq,
            exact h0 heq.symm },
          exact lt_of_le_of_ne h1 hz },
        { exact h2 } } },
    { intro h,
      cases h with h1 h2,
      { rw h1,
        norm_num },
      { cases h2 with h2a h2b,
        split,
        { linarith },
        { linarith } } } },
  apply not_countable_real_Ico_0_1,
  rw hu,
  apply set.countable_union h,
  exact set.countable_singleton 0,
end

/-- Any open interval of reals is uncountable. -/
lemma not_countable_real_Ioo {k1 k2 : ℝ} (h : k1 < k2) :
  ¬ set.countable (set.Ioo k1 k2) :=
begin
  intro h,
  apply not_countable_real_Ioo_0_1,
  convert set.countable_image (λ x, (x - k1) / (k2 - k1)) h,
  ext,
  split,
  { intro hx,
    cases hx with hx0 hx1,
    use (k2 - k1) * x + k1,
    split,
    { erw set.mem_set_of_eq,
      split,
      { linarith [mul_pos (show 0 < k2 - k1, by linarith) hx0] },
      { have h2 : (k2 - k1) * x < (k2 - k1) * 1 :=
          mul_lt_mul_of_pos_left hx1 (show 0 < (k2 - k1), by linarith),
        linarith } },
    { unfold,
      field_simp [(show k2 - k1 ≠ 0, by linarith)],
      ring } },
  { intro hy,
    cases hy with y hy,
    cases hy with hy1 hy2,
    erw set.mem_set_of_eq at hy1,
    unfold at hy2,
    cases hy1 with hy1a hy1b,
    rw ← hy2,
    erw [set.mem_set_of_eq, lt_div_iff (show 0 < (k2 - k1), by linarith), zero_mul,
         div_lt_iff (show 0 < (k2 - k1), by linarith)],
    split,
    { linarith },
    { linarith } }
end
