-- BMO2 2020 problem 4.

import data.real.basic
import tactic.basic
import tactic.linarith
import topology.instances.real

noncomputable theory

open real

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

-- Rearranged expression using invariant, in form more suited to
-- inequalities.
theorem invar_rearranged (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
  (1 + (p4_invar x y) / 4) * ((x - y) * (x - y)) + (-((p4_invar x y) / 4)) * ((x + y) * (x + y)) = 1 :=
begin
  unfold p4_invar,
  field_simp [hx, hy, mul_ne_zero hx hy, (show (4 : ℝ) ≠ 0, by norm_num)],
  ring,
end

-- Bounds on two variables, given such a sum of squares.
theorem square_bounds_1 (a b x y : ℝ) (ha : 0 < a) (hb : 0 < b)
  (hs : a * (x * x) + b * (y * y) = 1) : abs x ≤ sqrt (1 / a) :=
begin
  apply le_sqrt_of_sqr_le,
  rw [(show abs x ^ 2 = abs x * abs x, by ring), abs_mul_abs_self],
  have hb2: 0 ≤ b * (y * y) := mul_nonneg (le_of_lt hb) (mul_self_nonneg y),
  have hs2: a * (x * x) ≤ 1, {linarith},
  rw mul_comm at hs2,
  rw le_div_iff ha,
  exact hs2,
end

theorem square_bounds_2 (a b x y : ℝ) (ha : 0 < a) (hb : 0 < b)
  (hs : a * (x * x) + b * (y * y) = 1) : abs y ≤ sqrt (1 / b) :=
begin
  rw add_comm at hs,
  exact square_bounds_1 b a y x hb ha hs,
end

-- Bounds on x, given the invariant.
theorem bounds_using_invar_1 (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0)
  (ha : 0 < (1 + (p4_invar x y) / 4)) (hb : 0 < (-((p4_invar x y) / 4))):
  abs x ≤ (sqrt (1 / (1 + (p4_invar x y) / 4)) + sqrt (1 / (-((p4_invar x y) / 4)))) / 2 :=
begin
  have hi : (1 + (p4_invar x y) / 4) * ((x - y) * (x - y)) + (-((p4_invar x y) / 4)) * ((x + y) * (x + y)) = 1 := invar_rearranged x y hx hy,
  have haxmy : abs (x - y) ≤ sqrt (1 / (1 + (p4_invar x y) / 4)) := square_bounds_1 _ _ _ _ ha hb hi,
  have haxpy : abs (x + y) ≤ sqrt (1 / (-((p4_invar x y) / 4))) := square_bounds_2 _ _ _ _ ha hb hi,
  have hxmy : (x - y) ≤ sqrt (1 / (1 + (p4_invar x y) / 4)) := le_trans (le_abs_self _) haxmy,
  have hxpy : (x + y) ≤ sqrt (1 / (-((p4_invar x y) / 4))) := le_trans (le_abs_self _) haxpy,
  apply abs_le_of_le_of_neg_le,
  { linarith },
  rw ← abs_neg at haxmy,
  have hmxmy : -(x - y) ≤ sqrt (1 / (1 + (p4_invar x y) / 4)) := le_trans (le_abs_self _) haxmy,
  rw ← abs_neg at haxpy,
  have hmxpy : -(x + y) ≤ sqrt (1 / (-((p4_invar x y) / 4))) := le_trans (le_abs_self _) haxpy,
  linarith,
end

-- The first part of the problem.
theorem p4_part_1 (b : ℕ → ℝ) (hrec : p4_recurrence b) (hnz : p4_nonzero b)
  (k : ℝ) (h1 : 1 < k) (h2 : k < 2) (hb0 : b 0 = 1) (hb1 : b 1 = k) :
  ∃ B : ℝ, ∀ n : ℕ, -B ≤ b n ∧ b n ≤ B :=
begin
  have habs: ∃ B : ℝ, ∀ n : ℕ, abs (b n) ≤ B,
    { use (sqrt (1 / (1 + (p4_invar 1 k) / 4)) + sqrt (1 / (-((p4_invar 1 k) / 4)))) / 2,
      intro n,
      have hinvar: p4_invar (b n) (b (n + 1)) = p4_invar (b 0) (b 1) := p4_is_invar b hrec hnz n,
      rw [hb0, hb1] at hinvar,
      rw ←hinvar,
      have ha: 0 < (1 + (p4_invar (b n) (b (n + 1))) / 4),
      { rw hinvar,
        have hgt: -1 < p4_invar 1 k := invar_gt_m1 k h1 h2,
        linarith, },
      have hb: 0 < (-((p4_invar (b n) (b (n + 1)) / 4))),
      { rw hinvar,
        have hlt: p4_invar 1 k < 0 := invar_lt_zero k h1 h2,
        linarith, },
      exact bounds_using_invar_1 (b n) (b (n + 1)) (hnz n) (hnz (n + 1)) ha hb, },
  cases habs with B hB,
  use B,
  intro n,
  have hBb : abs (b n) ≤ B := hB n,
  split,
  { rw ← abs_neg at hBb,
    have hBb2 : -b n ≤ B := le_trans (le_abs_self _) hBb,
    linarith, },
  { exact le_trans (le_abs_self _) hBb },
end

-- Terms of the sequence, as functions of k.
noncomputable def p4_term : ℕ → ℝ → ℝ
| 0 := λ k, 1
| 1 := λ k, k
| (nat.succ (nat.succ n)) := λ k, p4_seq_next (p4_term n k) (p4_term (nat.succ n) k)

-- These functions do give the terms.
theorem p4_terms (b : ℕ → ℝ) (hrec : p4_recurrence b) (k : ℝ)
  (hb0 : b 0 = 1) (hb1 : b 1 = k) : ∀ n : ℕ, b n = p4_term n k :=
begin
  intro n,
  induction n using nat.case_strong_induction_on with m hm,
  { exact hb0 },
  { cases m,
    { exact hb1 },
    { unfold p4_term,
      rw [nat.succ_eq_add_one, nat.succ_eq_add_one, add_assoc,
          (show 1 + 1 = 2, by norm_num), hrec m, hm m (nat.le_succ _),
          hm (m + 1) (show m + 1 ≤ nat.succ m, by rw nat.succ_eq_add_one)] } }
end

-- These functions have the expected value for k = 2.
theorem p4_terms_at_2 : ∀ n : ℕ, p4_term n 2 = n + 1 :=
begin
  intro n,
  induction n using nat.case_strong_induction_on with m hm,
  { unfold p4_term,
    norm_num },
  { cases m,
    { unfold p4_term,
      norm_num },
    { unfold p4_term,
      rw [nat.succ_eq_add_one, nat.succ_eq_add_one, hm m (nat.le_succ _),
          hm (m + 1) (show m + 1 ≤ nat.succ m, by rw nat.succ_eq_add_one),
          p4_seq_next],
      push_cast,
      have hm1: 1 + (↑m : ℝ) ≠ 0,
      { norm_cast,
        rw add_comm,
        exact dec_trivial },
      field_simp [hm1],
      ring } }
end

-- These functions are continuous at k = 2.
theorem p4_terms_continuous : ∀ n : ℕ, continuous_at (p4_term n) 2 :=
begin
  intro n,
  induction n using nat.case_strong_induction_on with m hm,
  { unfold p4_term,
    exact continuous_at_const },
  { cases m,
    { unfold p4_term,
      exact continuous_at_id },
    { unfold p4_term,
      unfold p4_seq_next,
      conv
      begin
        congr,
        funext,
        rw div_eq_mul_one_div,
        rw one_div_eq_inv
      end,
      apply continuous_at.mul,
      { apply continuous_at.add,
        { apply continuous_at.mul,
          { exact hm (nat.succ m) (by refl), },
          { exact hm (nat.succ m) (by refl), } },
        { exact continuous_at_const } },
      { sorry, } } }
end

-- TODO 6: continuity and deduce second part of problem.
