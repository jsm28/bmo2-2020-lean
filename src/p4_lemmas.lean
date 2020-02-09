-- BMO2 2020 problem 4: lemmas of possibly more general use.  Are any
-- of these already in mathlib, possibly under a different name or in
-- a more general form, or should any of them be?

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
