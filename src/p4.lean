-- BMO2 2020 problem 4.

-- Choices made for formalization: we index the sequence starting at 0
-- rather than at 1 as in the original problem.

import data.polynomial
import data.real.basic
import tactic.basic
import tactic.linarith
import tactic.ring_exp
import topology.instances.real

import p4_lemmas

noncomputable theory
open_locale classical

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
  have hzz : (y * y - 1) / x * x ≠ 0 := mul_ne_zero hz hx,
  rw [div_mul_cancel _ hx] at hzz,
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
  have hs2 : a * (x * x) ≤ 1, { linarith },
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
      have hm1 : (↑m : ℝ) + 1 ≠ 0,
      { norm_cast,
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
  have hcc : -(p4_term 2020 k - ↑2021) < 1, { linarith },
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
-- the interval.  As mathlib does not have the concept of rational
-- function, we define a pair of numerator and denominator
-- polynomials.  (In fact the terms are polynomials in k, but that is
-- not needed for this proof.)

-- Terms of the sequence, as numerators and denominators of polynomials in k.
noncomputable def p4_term_poly : ℕ → ((polynomial ℝ) × (polynomial ℝ))
| 0 := ⟨polynomial.C 1, polynomial.C 1⟩
| 1 := ⟨polynomial.X, polynomial.C 1⟩
| (nat.succ (nat.succ n)) :=
  ⟨((p4_term_poly (nat.succ n)).fst * (p4_term_poly (nat.succ n)).fst -
    (p4_term_poly (nat.succ n)).snd * (p4_term_poly (nat.succ n)).snd) *
   (p4_term_poly n).snd,
   (p4_term_poly (nat.succ n)).snd * (p4_term_poly (nat.succ n)).snd * (p4_term_poly n).fst⟩

theorem p4_term_poly_num (n : ℕ) : (p4_term_poly (nat.succ (nat.succ n))).fst =
    ((p4_term_poly (nat.succ n)).fst * (p4_term_poly (nat.succ n)).fst -
      (p4_term_poly (nat.succ n)).snd * (p4_term_poly (nat.succ n)).snd) *
        (p4_term_poly n).snd :=
begin
  unfold p4_term_poly
end

theorem p4_term_poly_den (n : ℕ) : (p4_term_poly (nat.succ (nat.succ n))).snd =
  (p4_term_poly (nat.succ n)).snd * (p4_term_poly (nat.succ n)).snd * (p4_term_poly n).fst :=
begin
  unfold p4_term_poly
end

-- Terms are given by those rational functions, if no prior term was
-- zero.
theorem p4_terms_poly (k : ℝ) : ∀ n : ℕ, (∀ m : ℕ, m < n → p4_term m k ≠ 0) →
    p4_term n k = polynomial.eval k (p4_term_poly n).fst /
        polynomial.eval k (p4_term_poly n).snd :=
begin
  intro n,
  induction n using nat.case_strong_induction_on with t ht,
  { intro hm,
    unfold p4_term p4_term_poly,
    simp },
  { intro hm,
    cases t,
    { unfold p4_term p4_term_poly,
      simp },
    { unfold p4_term,
      rw [p4_term_poly_num, p4_term_poly_den],
      have hmm : ∀ (m : ℕ), m < nat.succ t → p4_term m k ≠ 0,
      { intros m hmlt,
        exact hm m (lt_trans hmlt (nat.lt_succ_self _)) },
      have hmmm : ∀ (m : ℕ), m < t → p4_term m k ≠ 0,
      { intros m hmlt,
        exact hmm m (lt_trans hmlt (nat.lt_succ_self _)) },
      have ht1 := ht t (nat.le_succ t) hmmm,
      have ht2 := ht (nat.succ t) (by refl) hmm,
      rw [ht1, ht2],
      unfold p4_seq_next,
      have ht1a : polynomial.eval k (p4_term_poly t).fst ≠ 0,
      { intro hz,
        rw [hz, zero_div] at ht1,
        exact hmm t (nat.lt_succ_self _) ht1 },
      have ht1b : polynomial.eval k (p4_term_poly t).snd ≠ 0,
      { intro hz,
        rw [hz, div_zero] at ht1,
        exact hmm t (nat.lt_succ_self _) ht1 },
      have ht2a : polynomial.eval k (p4_term_poly (nat.succ t)).fst ≠ 0,
      { intro hz,
        rw [hz, zero_div] at ht2,
        exact hm (nat.succ t) (nat.lt_succ_self _) ht2 },
      have ht2b : polynomial.eval k (p4_term_poly (nat.succ t)).snd ≠ 0,
      { intro hz,
        rw [hz, div_zero] at ht2,
        exact hm (nat.succ t) (nat.lt_succ_self _) ht2 },
      field_simp [ht1a, ht1b, ht2a, ht2b] } }
end

-- The numerator and denominator polynomials are not identically zero.
theorem p4_poly_ne_zero : ∀ n : ℕ, ((p4_term_poly n).fst) ≠ 0 ∧ ((p4_term_poly n).snd) ≠ 0 :=
begin
  have h2 : ∀ m : ℕ, p4_term m (2 : ℝ) = polynomial.eval 2 (p4_term_poly m).fst /
        polynomial.eval 2 (p4_term_poly m).snd,
  { intro m,
    apply p4_terms_poly,
    intro m1,
    intro hm1,
    rw p4_terms_at_2,
    norm_cast,
    simp },
  intro n,
  split,
  { intro h,
    have h2n := h2 n,
    rw [h, p4_terms_at_2, polynomial.eval_zero, zero_div] at h2n,
    norm_cast at h2n },
  { intro h,
    have h2n := h2 n,
    rw [h, p4_terms_at_2, polynomial.eval_zero, div_zero] at h2n,
    norm_cast at h2n }
end

-- There exists a finite set of k for which some term up to n is zero.
theorem p4_finset_zero  (n : ℕ) :
  ∃ s : finset ℝ, (∀ k : ℝ, (∃ m : ℕ, m ≤ n ∧ p4_term m k = 0) → k ∈ s) :=
begin
  induction n with t ht,
  { use ∅,
    intro k,
    intro h,
    exfalso,
    cases h with m hm,
    cases hm with hm0 hmt,
    have hm00 : m = 0, { linarith },
    rw hm00 at hmt,
    unfold p4_term at hmt,
    norm_num at hmt },
  { cases ht with st hst,
    use st ∪ polynomial.roots ((p4_term_poly (nat.succ t)).fst) ∪
             polynomial.roots ((p4_term_poly (nat.succ t)).snd),
    intro k,
    intro hm,
    cases hm with m hm,
    cases hm with hmlt hm0,
    by_cases hx : ∃ (q : ℕ), (q ≤ t ∧ p4_term q k = 0),
    { apply finset.mem_union_left,
      apply finset.mem_union_left,
      exact hst k hx },
    { by_cases hmlet : m ≤ t,
      { exfalso,
        apply hx,
        use m,
        split,
        { exact hmlet },
        { exact hm0 } },
      { have hmt : m = nat.succ t,
        { rw [←lt_iff_not_ge', ←nat.succ_le_iff] at hmlet,
          linarith },
        have hterm : p4_term m k = polynomial.eval k (p4_term_poly m).fst /
          polynomial.eval k (p4_term_poly m).snd,
        { apply p4_terms_poly,
          intros m1 hm1 hm10,
          apply hx,
          use m1,
          split,
          { rw hmt at hm1,
            rw ←nat.lt_succ_iff,
            exact hm1 },
          { exact hm10 } },
        { have hn0 : (p4_term_poly (nat.succ t)).fst ≠ 0 := (p4_poly_ne_zero (nat.succ t)).left,
          have hd0 : (p4_term_poly (nat.succ t)).snd ≠ 0 := (p4_poly_ne_zero (nat.succ t)).right,
          by_cases hden : polynomial.eval k (p4_term_poly m).snd = 0,
          { apply finset.mem_union_right,
            rw polynomial.mem_roots hd0,
            unfold polynomial.is_root,
            rw ← hmt,
            exact hden },
          { rw [hterm, div_eq_zero_iff hden] at hm0,
            apply finset.mem_union_left,
            apply finset.mem_union_right,
            rw polynomial.mem_roots hn0,
            unfold polynomial.is_root,
            rw ← hmt,
            exact hm0 } } } } }
end

-- There exists a countable set of k for which some term up to n is zero.
theorem p4_countableset_zero (n : ℕ) :
  ∃ s : set ℝ, s.countable ∧ (∀ k : ℝ, (∃ m : ℕ, m ≤ n ∧ p4_term m k = 0) → k ∈ s) :=
begin
  cases p4_finset_zero n with fs hfs,
  use (↑fs),
  split,
  { apply set.countable_finite,
    exact finset.finite_to_set fs },
  { intro k,
    intro h,
    rw finset.mem_coe,
    revert h,
    revert k,
    exact hfs }
end

-- That countable set.
def p4_countableset_zero_set (n : ℕ) := classical.some (p4_countableset_zero n)

-- Its defining property.
theorem p4_countableset_zero_set_prop (n : ℕ) :
  (p4_countableset_zero_set n).countable ∧
    (∀ k : ℝ, (∃ m : ℕ, m ≤ n ∧ p4_term m k = 0) → k ∈ (p4_countableset_zero_set n)) :=
classical.some_spec (p4_countableset_zero n)

-- There exists a countable set of k for which some term is zero.
theorem p4_countable_zero : ∃ s : set ℝ,
    s.countable ∧ (∀ k : ℝ, (∃ m : ℕ, p4_term m k = 0) → k ∈ s) :=
begin
  use ⋃ n : ℕ, p4_countableset_zero_set n,
  split,
  { apply set.countable_Union,
    intro n,
    exact (p4_countableset_zero_set_prop n).left },
  { intros k h,
    rw set.mem_Union,
    cases h with m hm,
    use m,
    apply (p4_countableset_zero_set_prop m).right k,
    use m,
    split,
    { refl },
    { exact hm } },
end

-- That countable set.
def p4_countable_zero_set := classical.some p4_countable_zero

-- Its defining property.
theorem p4_countable_zero_set_prop:
  set.countable p4_countable_zero_set ∧
    (∀ k : ℝ, (∃ m : ℕ, p4_term m k = 0) → k ∈ p4_countable_zero_set) :=
classical.some_spec p4_countable_zero

-- Any open interval of reals contains one not in that set.
theorem interval_open_not_in_set (k1 k2 : ℝ) (h : k1 < k2) :
  ∃ k : ℝ, k ∈ {x : ℝ | k1 < x ∧ x < k2} ∧ ¬ k ∈ p4_countable_zero_set :=
begin
  have hns : ¬ {x : ℝ | k1 < x ∧ x < k2} ⊆ p4_countable_zero_set,
  { intro hsub,
    exact not_countable_real_interval_open h
      (set.countable_subset hsub p4_countable_zero_set_prop.left) },
  rw set.not_subset at hns,
  cases hns with k hk,
  cases hk with hk1 hk2,
  use k,
  exact and.intro hk1 hk2
end

-- The actual result that a suitable value is in the interval.

theorem p4_interval_terms_nonzero (kb : ℝ) (h1 : 1 ≤ kb) (h2 : kb < 2) :
  ∃ (k : ℝ) (h1 : kb < k) (h2 : k < 2), ∀ n : ℕ, p4_term n k ≠ 0 :=
begin
  cases interval_open_not_in_set kb 2 h2 with k hk,
  cases hk with hk1 hk2,
  rw set.mem_set_of_eq at hk1,
  cases hk1 with hk1a hk1b,
  use k,
  use hk1a,
  use hk1b,
  intro n,
  intro hz,
  have hex : ∃ m : ℕ, p4_term m k = 0,
  { use n,
    exact hz },
  exact hk2 (p4_countable_zero_set_prop.right k hex)
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
