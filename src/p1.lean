-- BMO2 2020 problem 1.

-- Choices made for formalization: the original problem does not
-- specify a type for the terms of the sequence; we choose ℤ.  We also
-- index the sequence starting at 0 rather than at 1 as in the
-- original problem.

import data.int.parity
import tactic.basic
import tactic.linarith
import tactic.norm_num
import tactic.ring
import tactic.ring_exp

open int

-- Next term in sequence.
def p1_seq_next (a : ℤ) : ℤ := a * (a - 1) / 2

-- Condition that sequence satisfies recurrence.
def p1_recurrence (a : ℕ → ℤ) : Prop := ∀ n : ℕ, a (n + 1) = p1_seq_next (a n)

-- Odd numbers.
def all_odd (a : ℕ → ℤ) : Prop := ∀ n : ℕ, odd (a n)

/-- If an integer is `a` mod `b`, there are corresponding cases for its
value mod `c * b`. -/
lemma mod_mul_eq_cases {n a b c : ℤ} (hbpos : 0 < b) (hcpos : 0 < c) (hmod : n % b = a) :
  ∃ d : ℤ, 0 ≤ d ∧ d < c ∧ n % (c * b) = a + d * b :=
begin
  use ((n % (c * b)) / b),
  split,
  { exact int.div_nonneg (mod_nonneg _ (mul_ne_zero (ne_of_gt hcpos) (ne_of_gt hbpos)))
                         (int.le_of_lt hbpos) },
  split,
  { rw int.div_lt_iff_lt_mul hbpos,
    exact mod_lt_of_pos n (mul_pos hcpos hbpos) },
  { rw [←hmod, ←mod_mod_of_dvd n (dvd_mul_left b c), mod_def (n % (c * b)) b,
        mul_comm b (n % (c * b) / b)],
    simp }
end

-- If an integer is a mod b, it is a or a + b mod 2b.
theorem mod_mul_2 (n : ℤ) (a : ℤ) (b : ℤ) (hbpos : 0 < b) (hmod : n % b = a) :
  n % (2 * b) = a ∨ n % (2 * b) = a + b :=
begin
  rcases mod_mul_eq_cases hbpos (dec_trivial : (0 : ℤ) < 2) hmod with ⟨d, ⟨hd0, ⟨hd2, hdmod⟩⟩⟩,
  have hd01 : d = 0 ∨ d = 1,
  { by_cases h : 1 ≤ d,
    { right,
      linarith },
    { left,
      linarith } },
  cases hd01,
  { left,
    rw [hd01, zero_mul, add_zero] at hdmod,
    exact hdmod },
  { right,
    rw [hd01, one_mul] at hdmod,
    exact hdmod }
end

-- Powers of 2 are positive.
theorem power_of_2_pos (k : ℕ) : 0 < (2^k : ℤ) :=
pow_pos dec_trivial k

-- The main part of the induction step in the proof.  If two
-- consecutive terms are 3 mod 2^m, the first must be 3 mod 2^(m+1).
-- Note: with (3 % 2^m) the result could be stated in a more
-- complicated way meaningful for m = 1 as well.
theorem induction_main (m : ℕ) (a : ℤ) (hm : 2 ≤ m) (ha : a % 2^m = 3)
    (hb : (p1_seq_next a) % 2^m = 3) : a % 2^(m+1) = 3 :=
begin
  have h2m1 : (2^(m+1) : ℤ) = (2 * 2^m : ℤ) := rfl,
  rw h2m1,
  have hcases : a % (2 * 2^m) = 3 ∨ a % (2 * 2^m) = 3 + 2^m,
  { exact mod_mul_2 _ _ _ (power_of_2_pos m) ha },
  cases hcases with hc1 hc2,
  { exact hc1 },
  { exfalso,
    unfold p1_seq_next at hb,
    rw mod_def at hc2,
    set d := a / (2 * 2^m) with hd,
    have hc2m : a = 3 + 2^m + 2 * 2^m * d,
    { rw ← hc2,
      simp, },
    have hc2mm : a = 3 + 2 ^ m * (1 + 2 * d),
    { rw hc2m,
      ring },
    have hm1 : ∃ m1 : ℕ, m = 1 + m1,
    { have hm2 : ∃ m2 : ℕ, m = 2 + m2 := nat.exists_eq_add_of_le hm,
      cases hm2 with m2 hm2_h,
      use 1 + m2,
      rw hm2_h,
      ring },
    cases hm1 with m1 hmm1,
    rw [hc2mm, hmm1,
        (show (3 + 2 ^ (1 + m1) * (1 + 2 * d)) * (3 + 2 ^ (1 + m1) * (1 + 2 * d) - 1) =
               2 * (3 + 2^m1 + 2^(1 + m1) * (2 + 5 * d + 2^m1 * (1 + 2 * d) * (1 + 2 * d))),
         by ring_exp),
        int.mul_div_cancel_left _ (show (2 : ℤ) ≠ 0, by norm_num), ← hmm1,
        ← add_mod_mod, mul_assoc, mul_mod_right, add_zero] at hb,
    have hbbx : (3 + (2 : ℤ)^m1) % 2^m = 3 % 2^m, { rw [← mod_mod, hb] },
    rw [mod_eq_mod_iff_mod_sub_eq_zero, add_comm, add_sub_assoc, sub_self, add_zero,
        hmm1, add_comm, pow_succ] at hbbx,
    have hdvd : (2^m1 : ℤ) ∣ 2^m,
    { use 2,
      rw [mul_comm, hmm1, add_comm, ← pow_succ], },
    have hrdvd : (2^m : ℤ) ∣ 2^m1,
    { rw [hmm1, add_comm, pow_succ],
      exact dvd_of_mod_eq_zero hbbx, },
    have heq : (2^m1 : ℤ) = 2^m,
    { exact dvd_antisymm (int.le_of_lt (power_of_2_pos m1))
                         (int.le_of_lt (power_of_2_pos m)) hdvd hrdvd, },
    rw [hmm1, add_comm, pow_succ] at heq,
    have heqx : (2^m1 : ℤ) - 2^m1 = 2*2^m1 - 2^m1,
    { conv_lhs { congr, rw heq } },
    rw sub_self at heqx,
    have heqxx : 2 * (2^m1 : ℤ) - 2^m1 = 2^m1, { ring },
    rw heqxx at heqx,
    have heqz : 0 < (2^m1 : ℤ) := power_of_2_pos m1,
    rw ← heqx at heqz,
    exact lt_irrefl (0 : ℤ) heqz, },
end

-- Base case: if two consecutive terms are odd, the first is 3 mod 4.
theorem induction_base (a : ℤ) (ha : odd a) (hb : odd (p1_seq_next a)) : a % 2^2 = 3 :=
begin
  rw [odd_def, not_even_iff] at ha hb,
  rw (show (2^2 : ℤ) = 2 * 2, by norm_num),
  have hcases : a % (2 * 2) = 1 ∨ a % (2 * 2) = 1 + 2,
  { exact mod_mul_2 _ _ _ dec_trivial ha },
  cases hcases with hc1 hc2,
  { exfalso,
    unfold p1_seq_next at hb,
    rw mod_def at hc1,
    set d := a / (2 * 2) with hd,
    have hc1m : a = 1 + 2 * 2 * d,
    { conv_rhs { congr, rw ←hc1 },
      simp },
    rw hc1m at hb,
    conv_lhs at hb { congr, congr, congr, skip, rw [add_comm, add_sub_assoc, sub_self, add_zero] },
    rw [mul_comm, mul_assoc, mul_assoc] at hb,
    have hbm : 2 * (2 * (d * (1 + 2 * 2 * d))) / 2 = 2 * (d * (1 + 2 * 2 * d)) :=
      int.mul_div_cancel_left _ dec_trivial,
    rw [hbm, mul_mod_right] at hb,
    norm_num at hb },
  { rw hc2, norm_num, },
end

-- Base case for whole sequence.
theorem induction_base_all (a : ℕ → ℤ) (hodd : all_odd a) (hrec : p1_recurrence a) :
  ∀ n : ℕ, (a n) % 2^2 = 3 :=
begin
  intro n,
  let an : ℤ := a n,
  set an1 : ℤ := a (n + 1) with han1,
  have hrecn : a (n + 1) = p1_seq_next an, { rw hrec n },
  rw ← han1 at hrecn,
  have hanodd : odd an := hodd n,
  have han1odd : odd an1 := hodd (n + 1),
  rw hrecn at han1odd,
  exact induction_base an hanodd han1odd,
end

-- Induction step for whole sequence.
theorem induction_main_all (m : ℕ) (a : ℕ → ℤ) (hm : 2 ≤ m)
    (hmod : ∀ k : ℕ, (a k) % 2^m = 3) (hrec : p1_recurrence a) :
  ∀ n : ℕ, (a n) % 2^(m+1) = 3 :=
begin
  intro n,
  let an : ℤ := a n,
  set an1 : ℤ := a (n + 1) with han1,
  have hrecn : a (n + 1) = p1_seq_next an, { rw hrec n },
  rw ← han1 at hrecn,
  have hanmod : an % 2^m = 3 := hmod n,
  have han1mod : an1 % 2^m = 3 := hmod (n + 1),
  rw hrecn at han1mod,
  exact induction_main m an hm hanmod han1mod,
end

-- All terms are 3 mod all powers of 2.
theorem three_mod_all_powers (a : ℕ → ℤ) (hodd : all_odd a) (hrec : p1_recurrence a) :
  ∀ m : ℕ, 2 ≤ m → ∀ n : ℕ, (a n) % 2^m = 3 :=
begin
  intro m,
  induction m with k hk,
  { intro hx,
    exfalso,
    norm_num at hx, },
  { by_cases h2k : 2 ≤ k,
    { intro hsk,
      exact induction_main_all k a h2k (hk h2k) hrec },
    { by_cases hk1 : k = 1,
      { intro h22,
        rw hk1,
        exact induction_base_all a hodd hrec, },
      { intro h2sk,
        exfalso,
        rw [(show 2 = nat.succ 1, by norm_num), nat.succ_le_iff, nat.lt_add_one_iff] at h2sk,
        rw not_le at h2k,
        exact hk1 (le_antisymm (nat.le_of_lt_succ h2k) h2sk) }}},
end

-- The first term of the sequence is 3.
theorem first_term_three (a : ℕ → ℤ) (hodd : all_odd a)
    (hrec : p1_recurrence a) : a 0 = 3 :=
begin
  set k : ℕ := 2 ^ (2 + nat_abs (a 0 - 3)) with hk,
  have hltk : 2 + nat_abs (a 0 - 3) < k := nat.lt_two_pow _,
  have hmod : a 0 % k = 3,
  { rw hk,
    push_cast,
    norm_num,
    exact three_mod_all_powers a hodd hrec (2 + nat_abs (a 0 + -3)) (by linarith) 0 },
  rw ←nat_abs_of_nat k at hltk,
  exact eq_of_mod_eq_of_nat_abs_sub_lt_nat_abs hmod (by linarith)
end

-- The actual result of the problem.
theorem p1_result  (a : ℕ → ℤ) (hrec : p1_recurrence a) (ha3 : 2 < a 0) :
    all_odd a ↔ a 0 = 3 :=
begin
  split,
  { intro hodd, exact first_term_three a hodd hrec, },
  { intro h03,
    have halln : ∀ n : ℕ, a n = 3,
    { intro n,
      induction n with k hk,
      { exact h03, },
      { rw hrec k,
        unfold p1_seq_next,
        rw hk,
        norm_num, } },
    intro n,
    rw halln n,
    norm_num },
end
