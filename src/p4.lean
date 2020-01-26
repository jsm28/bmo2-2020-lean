-- BMO2 2020 problem 4.

import data.real.basic
import tactic.basic
import tactic.linarith
import topology.instances.real

noncomputable theory

-- Next term in sequence.
def p4_seq_next (x y : ℝ) : ℝ := (y * y - 1) / x

-- Condition that sequence satisfies recurrence.
def p4_recurrence (b : ℕ → ℝ) : Prop :=
∀ n : ℕ, b (n + 2) = p4_seq_next (b n) (b (n + 1))

-- Condition that terms are nonzero.
def p4_nonzero (b : ℕ → ℝ) : Prop := ∀ n : ℕ, b n ≠ 0

-- Function we will show is an invariant (the same for all pairs of
-- consecutive terms).
def p4_invar (x y : ℝ) : ℝ := ((y - x) * (y - x) - 1) / (x * y)

-- Induction step to show this is an invariant.
theorem invar_step (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : p4_seq_next x y ≠ 0) :
  p4_invar y (p4_seq_next x y) = p4_invar x y :=
begin
  unfold p4_invar p4_seq_next,
  unfold p4_seq_next at hz,
  have hzz: (y * y - 1) / x * x ≠ 0 := mul_ne_zero hz hx,
  rw [div_mul_cancel _ hx, sub_eq_add_neg] at hzz,
  field_simp [hx, hy, hzz],
  ring,
end

-- This is an invariant.
theorem p4_is_invar (b : ℕ → ℝ) (hrec : p4_recurrence b) (hnz : p4_nonzero b) :
  ∀ n : ℕ, p4_invar (b n) (b (n + 1)) = p4_invar (b 0) (b 1) :=
begin
  intro n,
  induction n with k hk,
  { refl },
  { rw [← hk, nat.succ_eq_add_one, add_assoc, (show 1 + 1 = 2, by norm_num),
        hrec k],
    have hz : p4_seq_next (b k) (b (k + 1)) ≠ 0,
    { rw ← hrec k, exact hnz (k + 2) },
    exact invar_step (b k) (b (k + 1)) (hnz k) (hnz (k + 1)) hz, },
end

-- The invariant is negative.
theorem invar_lt_zero (k : ℝ) (h1 : 1 < k) (h2 : k < 2) : p4_invar 1 k < 0 :=
begin
  unfold p4_invar,
  rw [one_mul, (show (k - 1) * (k - 1) - 1 = (k - 2) * k, by ring),
      mul_div_cancel _ (show k ≠ 0, by linarith)],
  linarith,
end

-- The invariant is greater than -1.  (Actually -4 is all that's needed.)
theorem invar_gt_m1 (k : ℝ) (h1 : 1 < k) (h2 : k < 2) : -1 < p4_invar 1 k :=
begin
  unfold p4_invar,
  rw [one_mul, (show (k - 1) * (k - 1) - 1 = (k - 2) * k, by ring),
      mul_div_cancel _ (show k ≠ 0, by linarith)],
  linarith,
end

-- TODO 2: expression with sum of squares.

-- TODO 3: bounds on |x-y| and |x+y|.

-- TODO 4: bounds on x.

-- TODO 5: thus, first part of problem.

-- TODO 6: continuity and deduce second part of problem.
