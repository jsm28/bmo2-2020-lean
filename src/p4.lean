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
  have hzz : (y * y - 1) / x * x ≠ 0 := mul_ne_zero hz hx,
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
  (1 + (p4_invar x y) / 4) * ((x - y) * (x - y)) +
   (-((p4_invar x y) / 4)) * ((x + y) * (x + y)) = 1 :=
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
  have hb2 : 0 ≤ b * (y * y) := mul_nonneg (le_of_lt hb) (mul_self_nonneg y),
  have hs2 : a * (x * x) ≤ 1, {linarith},
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
  (ha : 0 < (1 + (p4_invar x y) / 4)) (hb : 0 < (-((p4_invar x y) / 4))) :
  abs x ≤ (sqrt (1 / (1 + (p4_invar x y) / 4)) + sqrt (1 / (-((p4_invar x y) / 4)))) / 2 :=
begin
  have hi : (1 + (p4_invar x y) / 4) * ((x - y) * (x - y)) +
             (-((p4_invar x y) / 4)) * ((x + y) * (x + y)) = 1 := invar_rearranged x y hx hy,
  have haxmy : abs (x - y) ≤ sqrt (1 / (1 + (p4_invar x y) / 4)) :=
    square_bounds_1 _ _ _ _ ha hb hi,
  have haxpy : abs (x + y) ≤ sqrt (1 / (-((p4_invar x y) / 4))) :=
    square_bounds_2 _ _ _ _ ha hb hi,
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
  have habs : ∃ B : ℝ, ∀ n : ℕ, abs (b n) ≤ B,
    { use (sqrt (1 / (1 + (p4_invar 1 k) / 4)) + sqrt (1 / (-((p4_invar 1 k) / 4)))) / 2,
      intro n,
      have hinvar : p4_invar (b n) (b (n + 1)) = p4_invar (b 0) (b 1) := p4_is_invar b hrec hnz n,
      rw [hb0, hb1] at hinvar,
      rw ←hinvar,
      have ha : 0 < (1 + (p4_invar (b n) (b (n + 1))) / 4),
      { rw hinvar,
        have hgt : -1 < p4_invar 1 k := invar_gt_m1 k h1 h2,
        linarith, },
      have hb : 0 < (-((p4_invar (b n) (b (n + 1)) / 4))),
      { rw hinvar,
        have hlt : p4_invar 1 k < 0 := invar_lt_zero k h1 h2,
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
      have hm1 : 1 + (↑m : ℝ) ≠ 0,
      { norm_cast,
        rw add_comm,
        exact dec_trivial },
      field_simp [hm1],
      ring } }
end

-- Continuity at a point of the result of dividing two functions
-- continuous at that point, where the denominator is nonzero.  Is
-- this in mathlib?  Should it be (for general topological
-- semifields, not just ℝ?)?
theorem continuous_at.div {α : Type} [topological_space α] {f : α → ℝ} {g : α → ℝ} {x : α}
    (hf : continuous_at f x) (hg : continuous_at g x) (hnz : g x ≠ 0) :
  continuous_at (λ x, f x / g x) x :=
continuous_at.mul hf (continuous_at.comp (tendsto_inv hnz) hg)

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
      apply continuous_at.div,
      { apply continuous_at.add,
        { apply continuous_at.mul,
          { exact hm (nat.succ m) (by refl), },
          { exact hm (nat.succ m) (by refl), } },
        { exact continuous_at_const } },
      { exact hm m (nat.le_succ m) },
      { rw p4_terms_at_2 m,
        norm_cast,
        exact dec_trivial } } }
end

-- These functions have values close to n + 1 near k = 2.
theorem p4_terms_close :
  ∀ n : ℕ, ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, abs (x - 2) < δ → abs (p4_term n x - p4_term n 2) < ε :=
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

theorem p4_part_2_terms_interval :
  ∃ (kb : ℝ) (h1 : 1 ≤ kb) (h2 : kb < 2), ∀ k : ℝ, kb < k → k < 2 → 2020 < (p4_term 2020) k :=
begin
  have h : ∃ δ > 0, ∀ x : ℝ, abs (x - 2) < δ → abs (p4_term 2020 x - p4_term 2020 2) < 1 :=
    p4_terms_close 2020 1 (by norm_num),
  cases h with d hd,
  cases hd with hd hh,
  have he : ∃ (e : ℝ) (heg0 : e > 0) (hel1 : e ≤ 1), ∀ x : ℝ,
    abs (x - 2) < e → abs (p4_term 2020 x - p4_term 2020 2) < 1,
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
  have hkx : abs (p4_term 2020 k - p4_term 2020 2) < 1,
  { apply he k,
    rw [← abs_neg _, neg_sub, abs_of_pos (show 2 - k > 0, by linarith)],
    linarith },
  rw p4_terms_at_2 2020 at hkx,
  norm_cast at hkx,
  rw (show 2020 + 1 = 2021, by norm_num) at hkx,
  rw ←abs_neg at hkx,
  have hc : -(p4_term 2020 k - ↑2021) ≤ abs (-(p4_term 2020 k - ↑2021)) := le_abs_self _,
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
    (r : ℚ) (hkr : pow_exactly_divides_denom p kr r) :
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
  have hranz : (ra : ℚ) ≠ 0,
  { norm_cast,
    intro hraz,
    rw hraz at hra,
    norm_num at hra,
    rw hra at hp,
    norm_num at hp },
  have hqbnz : (qb : ℚ) ≠ 0,
  { norm_cast,
    intro hqbz,
    rw hqbz at hqb,
    norm_num at hqb,
    rw hqb at hp,
    norm_num at hp },
  have hpnz : (p : ℚ) ≠ 0,
  { norm_cast,
    intro hpz,
    rw hpz at hp,
    norm_num at hp },
  split,
  { rw int.nat_abs_mul,
    exact nat.coprime.mul hqa hrb },
  { split,
    { rw int.nat_abs_mul,
      exact nat.coprime.mul hqb hra },
    { rw [hkq, hkr],
      push_cast,
      field_simp [hranz, hqbnz, pow_ne_zero kqr hpnz, pow_ne_zero kr hpnz,
                  pow_ne_zero (kqr + kr) hpnz],
      ring_exp } }
end

-- How this behaves for subtracting 1.
theorem divides_denom_sub_one (p : ℕ) (hp : p.prime) (kq : ℕ) (q : ℚ)
    (hkq : pow_exactly_divides_denom p kq q) (hkqpos : 0 < kq) :
  pow_exactly_divides_denom p kq (q - 1) :=
begin
  cases hkq with qa hkq,
  cases hkq with qb hkq,
  cases hkq with hqa hkq,
  cases hkq with hqb hkq,
  use qa - qb * p ^ kq,
  use qb,
  split,
  { apply nat.coprime.symm,
    rw nat.prime.coprime_iff_not_dvd hp,
    intro hdvd,
    rw ← int.coe_nat_dvd at hdvd,
    rw int.dvd_nat_abs at hdvd,
    have hkq1 : ∃ kq1 : ℕ, kq = kq1 + 1,
    { cases kq,
      { norm_num at hkqpos },
      { use kq } },
    cases hkq1 with kq1 hkq1,
    rw [hkq1, pow_add, pow_one,
        (show qa - qb * (↑p ^ kq1 * ↑p) = qa + ↑p * (-qb * ↑p ^ kq1), by ring),
        ←dvd_add_iff_left (dvd.intro (-qb * ↑p ^ kq1) rfl),
        int.coe_nat_dvd_left] at hdvd,
        have hqas := nat.coprime.symm hqa,
        rw nat.prime.coprime_iff_not_dvd hp at hqas,
        exact hqas hdvd },
  { split,
    { exact hqb },
    { rw hkq,
      have hqbnz : (qb : ℚ) ≠ 0,
      { norm_cast,
        intro hqbz,
        rw hqbz at hqb,
        norm_num at hqb,
        rw hqb at hp,
        norm_num at hp },
      have hpnz : (p : ℚ) ≠ 0,
      { norm_cast,
        intro hpz,
        rw hpz at hp,
        norm_num at hp },
      field_simp [hqbnz, pow_ne_zero kq hpnz] } }
end

-- How this behaves for iterating the recurrence.
theorem divides_denom_recurrence (p : ℕ) (hp : p.prime) (t : ℕ) (kq : ℕ) (q : ℚ)
    (hkq : pow_exactly_divides_denom p kq q) (r : ℚ)
    (hkr : pow_exactly_divides_denom p (kq + t) r) (htpos : 0 < t) :
  pow_exactly_divides_denom p (kq + 2 * t) (p4_seq_next q r) :=
begin
  unfold p4_seq_next,
  have hnum : pow_exactly_divides_denom p (kq + 2 * t + kq) (r * r - 1),
  { apply divides_denom_sub_one p hp (kq + 2 * t + kq) (r * r),
    { rw (show kq + 2 * t + kq = (kq + t) + (kq + t), by ring),
      apply divides_denom_mul p hp (kq + t) r hkr (kq + t) r hkr },
    { linarith } },
  apply divides_denom_div p hp (kq + 2 * t) kq (r * r - 1) hnum q hkq
end

-- What this implies for the terms.
theorem p4_terms_divides_denom (p : ℕ) (hp : p.prime) (t : ℕ) (htpos : 0 < t)
    (k : ℚ) (hkt : pow_exactly_divides_denom p t k) :
  ∀ n : ℕ, pow_exactly_divides_denom p (n * t) (p4_term n k) :=
begin
  intro n,
  induction n using nat.case_strong_induction_on with m hm,
  { unfold p4_term,
    rw zero_mul,
    use 1,
    use 1,
    norm_num },
  { cases m,
    { unfold p4_term,
      rw one_mul,
      exact hkt },
    { unfold p4_term,
      have hmd : pow_exactly_divides_denom p (m * t) (p4_term m k) := hm m (nat.le_succ m),
      have hm1d : pow_exactly_divides_denom p ((nat.succ m) * t) (p4_term (nat.succ m) k) :=
        hm (nat.succ m) (by refl),
      rw [(show (m + 1) * t = m * t + t, by ring)] at hm1d,
      have hm2d : pow_exactly_divides_denom p (m * t + 2 * t)
          (p4_seq_next (p4_term m k) (p4_term (nat.succ m) k))
        := divides_denom_recurrence p hp t (m * t) (p4_term m k) hmd (p4_term (nat.succ m) k)
                                    hm1d htpos,
      rw [nat.succ_eq_add_one, nat.succ_eq_add_one,
          (show (m + 1 + 1) * t = (m * t + 2 * t), by ring)],
          exact hm2d } }
end

-- A prime power exists that exactly divides any non-0 natural number.
theorem nat_pow_exactly_divides_exists (k : ℕ) (hkn0 : k ≠ 0) (p : ℕ) (hp : p.prime) :
  ∃ (pe : ℕ), p^pe ∣ k ∧ ¬ p^(pe + 1) ∣ k :=
begin
  induction k using nat.case_strong_induction_on with m hm,
  { exfalso,
    exact hkn0 rfl },
  { by_cases p ∣ nat.succ m,
    { have hlt : (nat.succ m) / p < (nat.succ m),
     { apply nat.div_lt_self,
       { exact dec_trivial, },
       { apply nat.prime.two_le,
         exact hp } },
     have hnez : (nat.succ m) / p ≠ 0,
     { intro hez,
       exact nat.succ_ne_zero m (nat.eq_zero_of_dvd_of_div_eq_zero h hez) },
     have hexists : ∃ (pe : ℕ), p ^ pe ∣ (nat.succ m / p) ∧ ¬p ^ (pe + 1) ∣ (nat.succ m / p),
     { apply hm (nat.succ m / p) (nat.le_of_lt_succ hlt) hnez },
     cases hexists with pem1 hpem1,
     cases hpem1 with hpem1a hpem1b,
     use pem1 + 1,
     rw ← nat.div_mul_cancel h,
     have hppos : 0 < p, {linarith [hp.left]},
     split,
     { rw [←nat.succ_eq_add_one, nat.pow_succ, nat.mul_dvd_mul_iff_right hppos],
       exact hpem1a },
     { rw [←nat.succ_eq_add_one, nat.pow_succ, nat.mul_dvd_mul_iff_right hppos],
       exact hpem1b } },
    { use 0,
      norm_num,
      exact h } }
end

-- Any rational with denominator not 1 is suitable.
theorem p4_rational_terms_nonzero (k : ℚ) (hk : k.denom ≠ 1) : ∀ n : ℕ, p4_term n k ≠ 0 :=
begin
  have hf : ∃ (p : ℕ), p.prime ∧ p ∣ k.denom,
  { use nat.min_fac k.denom,
    split,
    { exact nat.min_fac_prime hk },
    { exact nat.min_fac_dvd k.denom } },
  cases hf with p hf,
  cases hf with hp hdvd,
  have hexp : ∃ (exp : ℕ), 0 < exp ∧ pow_exactly_divides_denom p exp k,
  { have hdennz : k.denom ≠ 0,
    { linarith [k.pos] },
    have hpe : ∃ (pe : ℕ), p^pe ∣ k.denom ∧ ¬ p^(pe + 1) ∣ k.denom :=
      nat_pow_exactly_divides_exists k.denom hdennz p hp,
    cases hpe with exp hexp,
    cases hexp with hexp1 hexp2,
    use exp,
    split,
    { cases exp,
      { exfalso,
        norm_num at hexp2,
        exact hexp2 hdvd, },
      { norm_num } },
    { use k.num,
      use k.denom / p^exp,
      norm_cast,
      split,
      { apply nat.coprime.symm,
        rw nat.prime.coprime_iff_not_dvd hp,
        intro hndvd,
        have hnc : ¬ nat.coprime (int.nat_abs k.num) k.denom :=
          nat.not_coprime_of_dvd_of_dvd (nat.prime.one_lt hp) hndvd hdvd,
        exact hnc k.cop },
      { split,
        { apply nat.coprime.symm,
          rw nat.prime.coprime_iff_not_dvd hp,
          intro hexp3,
          have hexp4 : p * p^exp ∣ k.denom / p^exp * p^exp := mul_dvd_mul_right hexp3 _,
          rw [nat.div_mul_cancel hexp1,
              (show p * p^exp = p^(exp + 1), by ring_exp)] at hexp4,
          exact hexp2 hexp4 },
        { rw nat.div_mul_cancel hexp1, simp } } } },
  cases hexp with t ht,
  cases ht with htpos htdiv,
  intro n,
  have hdiv : pow_exactly_divides_denom p (n * t) (p4_term n k) :=
    p4_terms_divides_denom p hp t htpos k htdiv n,
  intro h0,
  rw h0 at hdiv,
  unfold pow_exactly_divides_denom at hdiv,
  cases hdiv with a hdiv,
  cases hdiv with b hdiv,
  cases hdiv with hac hdiv,
  cases hdiv with hbc hdiv,
  have hanz : (a : ℚ) ≠ 0,
  { norm_cast,
    intro haz,
    rw haz at hac,
    norm_num at hac,
    rw hac at hp,
    norm_num at hp },
  have hbnz : (b : ℚ) ≠ 0,
  { norm_cast,
    intro hbz,
    rw hbz at hbc,
    norm_num at hbc,
    rw hbc at hp,
    norm_num at hp },
  have hpnz : (p : ℚ) ≠ 0,
  { norm_cast,
    intro hpz,
    rw hpz at hp,
    norm_num at hp },
  field_simp [hbnz, pow_ne_zero (n * t) hpnz] at hdiv,
  exact hanz hdiv.symm,
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

theorem p4_rational_real_terms_nonzero (k : ℚ) (hk : k.denom ≠ 1) :
  ∀ n : ℕ, p4_term n (↑k : ℝ) ≠ 0 :=
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
  have hq : ∃ q : ℚ, kb < q ∧ (q : ℝ) < 2 := exists_rat_btwn h2,
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
  have hterms : ∃ (k : ℝ) (h1 : 1 < k) (h2 : k < 2),
    2020 < (p4_term 2020) k ∧ ∀ n : ℕ, p4_term n k ≠ 0 := p4_part_2_terms,
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
