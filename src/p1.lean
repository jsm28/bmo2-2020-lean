-- BMO2 2020 problem 1.

-- Choices made for formalization: the original problem does not
-- specify a type for the terms of the sequence; we choose ℤ.  We also
-- index the sequence starting at 0 rather than at 1 as in the
-- original problem.

import data.int.basic
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
def odd (a : ℤ) : Prop := a % 2 = 1
def all_odd (a : ℕ → ℤ) : Prop := ∀ n : ℕ, odd (a n)

-- If an integer from 0 to 2b is a mod b, it is a or a + b.
theorem mod_mul_2_aux (n : ℤ) (a : ℤ) (b : ℤ) (hbpos : 0 < b) (hmod : n % b = a)
    (hnlower : 0 ≤ n) (hnupper : n < 2 * b) :
  n = a ∨ n = a + b :=
begin
  have ha : a = n - b * (n / b),
  { rw ← hmod, exact mod_def _ _, },
  by_cases hn : n < b,
  { left,
    rw [div_eq_zero_of_lt hnlower hn, mul_zero, sub_zero] at ha,
    exact ha.symm, },
  { right,
    have hnx : b ≤ n,
    { apply le_of_not_gt, rw gt, exact hn, },
    have h1nd : 1 ≤ n / b,
    { rw ← one_mul b at hnx, exact int.le_div_of_mul_le hbpos hnx, },
    have hnd2 : n / b < 2 := int.div_lt_of_lt_mul hbpos hnupper,
    have hnd1 : n / b ≤ 1,
    { rw lt_iff_add_one_le at hnd2, exact le_of_add_le_add_right hnd2, },
    rw [ha, le_antisymm hnd1 h1nd],
    simp, },
end

-- If an integer is a mod b, it is a or a + b mod 2b.
theorem mod_mul_2 (n : ℤ) (a : ℤ) (b : ℤ) (hbpos : 0 < b) (hmod : n % b = a) :
  n % (2 * b) = a ∨ n % (2 * b) = a + b :=
begin
  have hdvd : b ∣ 2 * b := dvd_mul_left _ _,
  have hmodm : n % (2 * b) % b = a,
  { rw mod_mod_of_dvd n hdvd, exact hmod, },
  have h2bpos : 0 < 2 * b,
  { rw ← gt,
    rw ← gt at hbpos,
    exact mul_pos dec_trivial hbpos, },
  have hn2blower : 0 ≤ n % (2 * b),
  { apply mod_nonneg,
    intro h2b0,
    rw h2b0 at h2bpos,
    exact lt_irrefl 0 h2bpos, },
  have hn2bupper : n % (2 * b) < 2 * b := mod_lt_of_pos _ h2bpos,
  exact mod_mul_2_aux (n % (2 * b)) a b hbpos hmodm hn2blower hn2bupper,
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
    let d := a / (2 * 2^m),
    have hd : d = a / (2 * 2^m) := rfl,
    rw ← hd at hc2,
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
      simp },
    cases hm1 with m1 hmm1,
    rw [hc2mm, hmm1,
        (show (3 + 2 ^ (1 + m1) * (1 + 2 * d)) * (3 + 2 ^ (1 + m1) * (1 + 2 * d) - 1) =
               2 * (3 + 2^m1 + 2^(1 + m1) * (2 + 5 * d + 2^m1 * (1 + 2 * d) * (1 + 2 * d))),
         by ring_exp),
        int.mul_div_cancel_left _ (show (2 : ℤ) ≠ 0, by norm_num), ← hmm1,
        ← add_mod_mod, mul_assoc, mul_mod_right, add_zero] at hb,
    have hbbx : (3 + (2 : ℤ)^m1) % 2^m = 3 % 2^m, {rw [← mod_mod, hb]},
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
    { conv
      begin
        to_lhs,
        congr,
        rw heq,
      end, },
    rw sub_self at heqx,
    have heqxx : 2 * (2^m1 : ℤ) - 2^m1 = 2^m1, {ring},
    rw heqxx at heqx,
    have heqz : 0 < (2^m1 : ℤ) := power_of_2_pos m1,
    rw ← heqx at heqz,
    exact lt_irrefl (0 : ℤ) heqz, },
end

-- Base case: if two consecutive terms are odd, the first is 3 mod 4.
theorem induction_base (a : ℤ) (ha : odd a) (hb : odd (p1_seq_next a)) : a % 2^2 = 3 :=
begin
  unfold odd at ha hb,
  rw (show (2^2 : ℤ) = 2 * 2, by norm_num),
  have hcases : a % (2 * 2) = 1 ∨ a % (2 * 2) = 1 + 2,
  { exact mod_mul_2 _ _ _ dec_trivial ha },
  cases hcases with hc1 hc2,
  { exfalso,
    unfold p1_seq_next at hb,
    rw mod_def at hc1,
    let d := a / (2 * 2),
    have hd : d = a / (2 * 2) := rfl,
    rw ← hd at hc1,
    have hc1m : a = 1 + 2 * 2 * d,
    { conv
      begin
        to_rhs,
        congr,
        rw ← hc1,
      end,
      simp, },
    rw hc1m at hb,
    conv at hb
    begin
      to_lhs,
      congr,
      congr,
      congr,
      skip,
      rw [add_comm, add_sub_assoc, sub_self, add_zero],
    end,
    rw [mul_comm, mul_assoc, mul_assoc] at hb,
    have hbm : 2 * (2 * (d * (1 + 2 * 2 * d))) / 2 = 2 * (d * (1 + 2 * 2 * d)),
      by exact int.mul_div_cancel_left _ dec_trivial,
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
  let an1 : ℤ := a (n + 1),
  have han1 : an1 = a (n + 1) := rfl,
  have hrecn : a (n + 1) = p1_seq_next an, {rw hrec n},
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
  let an1 : ℤ := a (n + 1),
  have han1 : an1 = a (n + 1) := rfl,
  have hrecn : a (n + 1) = p1_seq_next an, {rw hrec n},
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
        rw [hk1, (show nat.succ 1 = 2, by norm_num)],
        exact induction_base_all a hodd hrec, },
      { intro h2sk,
        exfalso,
        rw [(show 2 = nat.succ 1, by norm_num), nat.succ_le_iff, nat.lt_add_one_iff,
            le_iff_lt_or_eq] at h2sk,
        finish, }}},
end

-- If a % b = c then b divides a - c.
theorem dvd_sub_of_mod_eq (a b c : ℤ) (h : a % b = c) : b ∣ a - c :=
begin
  have hx : a % b % b = c % b, {rw h},
  rw [mod_mod, ←mod_sub_cancel_right c, sub_self, zero_mod] at hx,
  exact dvd_of_mod_eq_zero hx
end

-- If a larger number divides a natural number, it is zero.
theorem eq_zero_of_dvd_of_gt {a b : ℕ} (w : a ∣ b) (h : b < a) : b = 0 :=
nat.eq_zero_of_dvd_of_div_eq_zero w
  ((nat.div_eq_zero_iff (lt_of_le_of_lt (zero_le b) h)).elim_right h)

-- If a number with larger absolute value divides an integer, it is zero.
theorem eq_zero_of_dvd_of_nat_abs_gt_nat_abs {a b : ℤ} (w : a ∣ b) (h : nat_abs b < nat_abs a)
  : b = 0 :=
begin
  rw [←nat_abs_dvd, ←dvd_nat_abs, coe_nat_dvd] at w,
  rw ←nat_abs_eq_zero,
  exact eq_zero_of_dvd_of_gt w h
end

-- If two integers are congruent to a sufficiently large modulus, they
-- are equal.
theorem eq_of_mod_eq_of_nat_abs_gt_nat_abs_sub {a b c : ℤ} (h1 : a % b = c)
    (h2 : nat_abs (a - c) < nat_abs b) :
  a = c :=
eq_of_sub_eq_zero (eq_zero_of_dvd_of_nat_abs_gt_nat_abs (dvd_sub_of_mod_eq a b c h1) h2)

-- The first term of the sequence is 3.
theorem first_term_three (a : ℕ → ℤ) (hodd : all_odd a)
    (hrec : p1_recurrence a) : a 0 = 3 :=
begin
  set k : ℕ := 2 ^ (2 + nat_abs (a 0 - 3)) with hk,
  have hltk : 2 + nat_abs (a 0 - 3) < k,
  { rw hk,
    exact nat.lt_pow_self dec_trivial _ },
  have hmod : a 0 % k = 3,
  { rw hk,
    push_cast,
    norm_num,
    exact three_mod_all_powers a hodd hrec (2 + nat_abs (a 0 + -3)) (by linarith) 0 },
  rw ←nat_abs_of_nat k at hltk,
  exact eq_of_mod_eq_of_nat_abs_gt_nat_abs_sub hmod (by linarith)
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
    unfold odd,
    norm_num, },
end
