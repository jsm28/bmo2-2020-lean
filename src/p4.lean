-- BMO2 2020 problem 4.

import data.rat.basic
import data.real.basic
import tactic.basic
import tactic.linarith
import tactic.ring_exp
import topology.instances.real

noncomputable theory

open real

-- Some of the following are defined for a general field, although the
-- problem is stated for real numbers, because it's convenient to use
-- a sequence of rationals in proving terms are nonzero.

-- Next term in sequence.
def p4_seq_next {α : Type} [field α] (x y : α) : α := (y * y - 1) / x

-- Condition that sequence satisfies recurrence.
def p4_recurrence {α : Type} [field α] (b : ℕ → α) : Prop :=
∀ n : ℕ, b (n + 2) = p4_seq_next (b n) (b (n + 1))

-- Condition that terms are nonzero.
def p4_nonzero {α : Type} [field α] (b : ℕ → α) : Prop := ∀ n : ℕ, b n ≠ 0

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
noncomputable def p4_term {α : Type} [field α] : ℕ → α → α
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
theorem p4_terms_at_2 : ∀ n : ℕ, p4_term n (2 : ℝ) = n + 1 :=
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
theorem p4_terms_continuous : ∀ n : ℕ, continuous_at (p4_term n) (2 : ℝ) :=
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
      apply continuous_at.mul,
      { apply continuous_at.add,
        { apply continuous_at.mul,
          { exact hm (nat.succ m) (by refl), },
          { exact hm (nat.succ m) (by refl), } },
        { exact continuous_at_const } },
      { apply continuous_at.comp,
        { apply tendsto_inv,
          { rw p4_terms_at_2 m,
            norm_cast,
            exact dec_trivial, } },
        { exact hm m (nat.le_succ m) } } } }
end

-- These functions have values close to n + 1 near k = 2.
theorem p4_terms_close : ∀ n : ℕ, ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, abs (x - 2) < δ → abs (p4_term n x - p4_term n 2) < ε :=
begin
  intro n,
  have h : continuous_at (p4_term n) (2 : ℝ) := p4_terms_continuous n,
  unfold continuous_at at h,
  rw metric.tendsto_nhds_nhds at h,
  exact h,
end


-- The second part of the problem, in terms of p4_term rather than the
-- original recurrence, finding an interval of values and with an
-- explicit term number.

theorem p4_part_2_terms_interval : ∃ (kb : ℝ) (h1 : 1 ≤ kb) (h2 : kb < 2), ∀ k : ℝ, kb < k → k < 2 → 2020 < (p4_term 2020) k :=
begin
  have h : ∃ δ > 0, ∀ x : ℝ, abs (x - 2) < δ → abs (p4_term 2020 x - p4_term 2020 2) < 1 := p4_terms_close 2020 1 (by norm_num),
  cases h with d hd,
  cases hd with hd hh,
  have he: ∃ (e : ℝ) (heg0 : e > 0) (hel1 : e ≤ 1), ∀ x : ℝ, abs (x - 2) < e → abs (p4_term 2020 x - p4_term 2020 2) < 1,
  { by_cases hdlt : d ≤ 1,
    { use d,
      use hd,
      use hdlt,
      exact hh },
    { use 1,
      use (show (1 : ℝ) > 0, by norm_num),
      use (show (1 : ℝ) ≤ 1, by norm_num),
      intro x,
      intro h12,
      apply hh x,
      linarith } },
  cases he with e he,
  cases he with heg0 he,
  cases he with hel1 he,
  use 2 - e,
  use (by linarith),
  use (by linarith),
  intros k hklb hkub,
  have hkx: abs (p4_term 2020 k - p4_term 2020 2) < 1,
  { apply he k,
    rw [← abs_neg _, neg_sub, abs_of_pos (show 2 - k > 0, by linarith)],
    linarith },
  rw p4_terms_at_2 2020 at hkx,
  norm_cast at hkx,
  rw (show 2020 + 1 = 2021, by norm_num) at hkx,
  rw ←abs_neg at hkx,
  have hc: -(p4_term 2020 k - ↑2021) ≤ abs (-(p4_term 2020 k - ↑2021)) := le_abs_self _,
  have hcc : -(p4_term 2020 k - ↑2021) < 1, {linarith},
  rw neg_sub at hcc,
  norm_cast at hcc,
  linarith,
end

-- Having found an interval, we now need to show it contains a real
-- such that all the terms are nonzero.  A natural informal proof is:
-- each b_n is a rational function of k, except for at finitely many
-- points where a previous term was zero, and none of those functions
-- is the constant 0 (because of the values at 2), so each b_n has
-- only finitely many k for which it is zero, so there are only
-- countably many such k in total, but there are uncountably many k in
-- the interval.  This seems hard for a beginner to formalise, so
-- instead we show that any noninteger rational results in all terms
-- nonzero.

-- Define the concept of a power of a natural number (intended to be
-- prime) exactly dividing the denominator of a rational (and that
-- number not dividing the numerator).  (Ideally this would be based
-- on extending the notion of multiplicity with which a prime divides
-- a natural number to the case of rationals with negative
-- multiplicity allowed.)

def pow_exactly_divides_denom (p : ℕ) (k : ℕ) (q : ℚ) :=
  ∃ (a : ℤ) (b : ℤ), a.nat_abs.coprime p ∧ b.nat_abs.coprime p ∧ q = (a : ℚ) / ((b * p ^ k) : ℚ)

-- How this behaves for products.
theorem divides_denom_mul (p : ℕ) (hp : p.prime) (kq : ℕ) (q : ℚ)
  (hkq : pow_exactly_divides_denom p kq q)
  (kr : ℕ) (r : ℚ) (hkr : pow_exactly_divides_denom p kr r) :
  pow_exactly_divides_denom p (kq + kr) (q * r) :=
begin
  cases hkq with qa hkq,
  cases hkq with qb hkq,
  cases hkq with hqa hkq,
  cases hkq with hqb hkq,
  cases hkr with ra hkr,
  cases hkr with rb hkr,
  cases hkr with hra hkr,
  cases hkr with hrb hkr,
  use qa * ra,
  use qb * rb,
  split,
  { rw int.nat_abs_mul,
    exact nat.coprime.mul hqa hra },
  { split,
    { rw int.nat_abs_mul,
      exact nat.coprime.mul hqb hrb },
    { rw [hkq, hkr],
      push_cast,
      field_simp,
      congr' 1,
      ring_exp } }
end

-- How this behaves for division.
theorem divides_denom_div (p : ℕ) (hp : p.prime) (kqr : ℕ) (kr : ℕ) (q : ℚ)
  (hkq : pow_exactly_divides_denom p (kqr + kr) q)
  (kr : ℕ) (r : ℚ) (hkr : pow_exactly_divides_denom p kr r) :
  pow_exactly_divides_denom p kqr (q / r) :=
begin
  cases hkq with qa hkq,
  cases hkq with qb hkq,
  cases hkq with hqa hkq,
  cases hkq with hqb hkq,
  cases hkr with ra hkr,
  cases hkr with rb hkr,
  cases hkr with hra hkr,
  cases hkr with hrb hkr,
  use qa * rb,
  use qb * ra,
  split,
  { rw int.nat_abs_mul,
    exact nat.coprime.mul hqa hrb },
  { split,
    { rw int.nat_abs_mul,
      exact nat.coprime.mul hqb hra },
    { rw [hkq, hkr],
      push_cast,
      rw pow_add,
      field_simp,
      sorry } }
end

-- Any rational with denominator not 1 is suitable.

theorem p4_rational_terms_nonzero (k : ℚ) (hk : k.denom ≠ 1): ∀ n : ℕ, p4_term n k ≠ 0 :=
begin
  sorry
end

theorem p4_rational_real_terms_eq (k : ℚ) : ∀ n : ℕ, ↑(p4_term n k) = p4_term n (↑k : ℝ) :=
begin
  intro n,
  induction n using nat.case_strong_induction_on with m hm,
  { unfold p4_term,
    norm_cast },
  { cases m,
    { unfold p4_term },
    { unfold p4_term,
      rw [← hm m (nat.le_succ _), ← hm (nat.succ m) (by refl)],
      unfold p4_seq_next,
      norm_cast } }
end

theorem p4_rational_real_terms_nonzero (k : ℚ) (hk : k.denom ≠ 1): ∀ n : ℕ, p4_term n (↑k : ℝ) ≠ 0 :=
begin
  intro n,
  rw ← p4_rational_real_terms_eq,
  norm_cast,
  exact p4_rational_terms_nonzero k hk n
end

-- The actual result that a suitable value is in the interval.

theorem p4_interval_terms_nonzero (kb : ℝ) (h1 : 1 ≤ kb) (h2 : kb < 2) :
  ∃ (k : ℝ) (h1 : kb < k) (h2 : k < 2), ∀ n : ℕ, p4_term n k ≠ 0 :=
begin
  have hq: ∃ q : ℚ, kb < q ∧ (q : ℝ) < 2 := exists_rat_btwn h2,
  cases hq with q hq,
  use (↑q : ℝ),
  cases hq with hql hqr,
  use hql,
  use hqr,
  have hq1 : (1 : ℝ) < q, {linarith},
  norm_cast at hq1,
  norm_cast at hqr,
  have hqd : q.denom ≠ 1,
  { intro hqd,
    have hqnum : (↑q.num) = q := rat.coe_int_num_of_denom_eq_one hqd,
    rw ← hqnum at hq1,
    rw ← hqnum at hqr,
    norm_cast at hq1,
    norm_cast at hqr,
    linarith },
  exact p4_rational_real_terms_nonzero q hqd
end

-- The second part of the problem, in terms of p4_term rather than the
-- original recurrence and with an explicit term number.
theorem p4_part_2_terms : ∃ (k : ℝ) (h1 : 1 < k) (h2 : k < 2),
  2020 < (p4_term 2020) k ∧ ∀ n : ℕ, p4_term n k ≠ 0 :=
begin
  cases p4_part_2_terms_interval with kb hkb,
  cases hkb with h1 hkb,
  cases hkb with h2 hkb,
  cases p4_interval_terms_nonzero kb h1 h2 with k hk,
  cases hk with hk1 hk,
  cases hk with hk2 hk,
  use k,
  use (by linarith),
  use hk2,
  split,
  { exact hkb k hk1 hk2 },
  { exact hk },
end

-- The second part of the original problem.
theorem p4_part_2 : ∃ (k : ℝ) (h1 : 1 < k) (h2 : k < 2),
  ∀ b : ℕ → ℝ, b 0 = 1 → b 1 = k → (p4_recurrence b) →
    ((∃ n : ℕ, 2020 < b n) ∧ (∀ n : ℕ, b n ≠ 0)) :=
begin
  have hterms: ∃ (k : ℝ) (h1 : 1 < k) (h2 : k < 2), 2020 < (p4_term 2020) k ∧ ∀ n : ℕ, p4_term n k ≠ 0 := p4_part_2_terms,
  cases hterms with k hterms,
  cases hterms with h1 hterms,
  cases hterms with h2 hterms,
  use k,
  use h1,
  use h2,
  intro b,
  intro hb0,
  intro hb1,
  intro hrec,
  split,
  { use 2020,
    rw p4_terms b hrec k hb0 hb1 2020,
     exact hterms.1 },
  { intro n,
    rw p4_terms b hrec k hb0 hb1 n,
    exact hterms.2 n }
end
