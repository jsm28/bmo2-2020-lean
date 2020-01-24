-- BMO2 2020 problem 1.

import data.int.basic
import tactic.basic
import tactic.linarith
import tactic.norm_num
import tactic.ring

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
    have hnd2: n / b < 2 := int.div_lt_of_lt_mul hbpos hnupper,
    have hnd1: n / b ≤ 1,
    { rw lt_iff_add_one_le at hnd2, exact le_of_add_le_add_right hnd2, },
    rw [ha, le_antisymm hnd1 h1nd],
    simp, },
end

-- If an integer is a mod b, it is a or a + b mod 2b.
theorem mod_mul_2 (n : ℤ) (a : ℤ) (b : ℤ) (hbpos : 0 < b) (hmod : n % b = a) :
    n % (2 * b) = a ∨ n % (2 * b) = a + b :=
begin
  have hdvd: b ∣ 2 * b := dvd_mul_left _ _,
  have hmodm: n % (2 * b) % b = a,
  { rw mod_mod_of_dvd n hdvd, exact hmod, },
  have h2bpos: 0 < 2 * b,
  { rw ← gt,
    rw ← gt at hbpos,
    exact mul_pos dec_trivial hbpos, },
  have hn2blower: 0 ≤ n % (2 * b),
  { apply mod_nonneg,
    intro h2b0,
    rw h2b0 at h2bpos,
    exact lt_irrefl 0 h2bpos, },
  have hn2bupper: n % (2 * b) < 2 * b := mod_lt_of_pos _ h2bpos,
  exact mod_mul_2_aux (n % (2 * b)) a b hbpos hmodm hn2blower hn2bupper,
end

-- Powers of 2 are positive.
theorem power_of_2_pos (k : ℕ): 0 < (2^k : ℤ) :=
pow_pos dec_trivial k

-- The main part of the induction step in the proof.  If two
-- consecutive terms are 3 mod 2^m, the first must be 3 mod 2^(m+1).
-- Note: with (3 % 2^m) the result could be stated in a more
-- complicated way meaningful for m = 1 as well.
theorem induction_main (m : ℕ) (a : ℤ) (hm: 2 ≤ m) (ha : a % 2^m = 3)
    (hb: (p1_seq_next a) % 2^m = 3) : a % 2^(m+1) = 3 :=
begin
  have h2m1: (2^(m+1) : ℤ) = (2 * 2^m : ℤ) := rfl,
  rw h2m1,
  have hcases: a % (2 * 2^m) = 3 ∨ a % (2 * 2^m) = 3 + 2^m,
  { exact mod_mul_2 _ _ _ (power_of_2_pos m) ha },
  cases hcases with hc1 hc2,
  { exact hc1 },
  { exfalso,
    unfold p1_seq_next at hb,
    rw mod_def at hc2,
    let d := a / (2 * 2^m),
    have hd: d = a / (2 * 2^m) := rfl,
    rw ← hd at hc2,
    have hc2m: a = 3 + 2^m + 2 * 2^m * d,
    { rw ← hc2,
      simp, },
    conv at hc2m
    begin
      to_rhs,
      congr,
      congr,
      skip,
      rw ← mul_one (2^m : ℤ),
      skip,
      rw [mul_comm 2 (2^m : ℤ), mul_assoc],
    end,
    rw [add_assoc, ← left_distrib] at hc2m,
    rw hc2m at hb,
    conv at hb
    begin
      to_lhs,
      congr,
      congr,
      congr,
      skip,
      rw [add_comm, add_sub_assoc],
      norm_num,
    end,
    have hm1: ∃ m1 : ℕ, m = 1 + m1,
    { have hm2: ∃ m2 : ℕ, m = 2 + m2 := nat.exists_eq_add_of_le hm,
      cases hm2 with m2 hm2_h,
      use 1 + m2,
      rw hm2_h,
      simp },
    cases hm1 with m1 hmm1,
    conv at hb
    begin
      to_lhs,
      congr,
      congr,
      congr,
      skip,
      rw [hmm1, add_comm 1 m1, pow_succ (2 : ℤ) m1],
    end,
    have hbb: (2 + 2 * 2 ^ m1 * (1 + 2 * d)) = 2 * (1 + 2^m1 * (1 + 2 * d)), {ring},
    rw [hbb, ← mul_assoc] at hb,
    conv at hb
    begin
      to_lhs,
      congr,
      congr,
      congr,
      rw mul_comm,
    end,
    rw [mul_assoc, int.mul_div_cancel_left _ (show (2 : ℤ) ≠ 0, by norm_num),
        right_distrib, ←add_mod_mod, mul_assoc, mul_mod_right, add_zero] at hb,
    conv at hb
    begin
      to_lhs,
      congr,
      congr,
      skip,
     rw [left_distrib, mul_one, ← mul_assoc],
     congr,
     skip,
     congr,
     skip,
     congr,
     rw [mul_comm, ← pow_succ, add_comm, ← hmm1],
    end,
    rw [left_distrib, left_distrib, ← add_assoc, ← mul_assoc, mul_comm 3 (2^m : ℤ),
        ← add_mod_mod, mul_assoc, mul_mod_right, add_zero] at hb,
    conv at hb
    begin
      to_lhs,
      congr,
      congr,
      skip,
      rw [(show (3 : ℤ) = 1 + 2, by norm_num), right_distrib, one_mul, ← pow_succ,
          add_comm m1 1, ← hmm1],
    end,
    rw [← add_assoc, mul_one, ← add_mod_mod, mod_self, add_zero] at hb,
    have hbbx: (3 + (2 : ℤ)^m1) % 2^m = 3 % 2^m, {rw [← mod_mod, hb]},
    rw [mod_eq_mod_iff_mod_sub_eq_zero, add_comm, add_sub_assoc, sub_self, add_zero,
        hmm1, add_comm, pow_succ] at hbbx,
    have hdvd: (2^m1 : ℤ) ∣ 2^m,
    { use 2,
      rw [mul_comm, hmm1, add_comm, ← pow_succ], },
    have hrdvd: (2^m : ℤ) ∣ 2^m1,
    { rw [hmm1, add_comm, pow_succ],
      exact dvd_of_mod_eq_zero hbbx, },
    have heq: (2^m1 : ℤ) = 2^m,
    { exact dvd_antisymm (int.le_of_lt (power_of_2_pos m1)) (int.le_of_lt (power_of_2_pos m)) hdvd hrdvd, },
    rw [hmm1, add_comm, pow_succ] at heq,
    have heqx: (2^m1 : ℤ) - 2^m1 = 2*2^m1 - 2^m1,
    { conv
      begin
        to_lhs,
        congr,
        rw heq,
      end, },
    rw sub_self at heqx,
    have heqxx: 2 * (2^m1 : ℤ) - 2^m1 = 2^m1, {ring},
    rw heqxx at heqx,
    have heqz: 0 < (2^m1 : ℤ) := power_of_2_pos m1,
    rw ← heqx at heqz,
    exact lt_irrefl (0 : ℤ) heqz, },
end

-- Base case: if two consecutive terms are odd, the first is 3 mod 4.
theorem induction_base (a : ℤ) (ha : odd a) (hb: odd (p1_seq_next a)) : a % 2^2 = 3 :=
begin
  unfold odd at ha hb,
  rw (show (2^2 : ℤ) = 2 * 2, by norm_num),
  have hcases: a % (2 * 2) = 1 ∨ a % (2 * 2) = 1 + 2,
  { exact mod_mul_2 _ _ _ dec_trivial ha },
  cases hcases with hc1 hc2,
  { exfalso,
    unfold p1_seq_next at hb,
    rw mod_def at hc1,
    let d := a / (2 * 2),
    have hd: d = a / (2 * 2) := rfl,
    rw ← hd at hc1,
    have hc1m: a = 1 + 2 * 2 * d,
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

-- All powers of 2 divide all terms minus 3.
theorem all_powers_divides_terms_minus_three (a : ℕ → ℤ) (hodd : all_odd a) (hrec : p1_recurrence a) :
  ∀ m : ℕ, ∀ n : ℕ, 2^m ∣ (a n) - 3 :=
begin
  intros m n,
  by_cases h2m : 2 ≤ m,
  { have hmod : (a n) % 2^m = 3 := three_mod_all_powers a hodd hrec m h2m n,
    rw mod_def at hmod,
    have hmodx : a n - 2^m * (a n / 2^m) + 2^m * (a n / 2^m) = 3 + 2^m * (a n / 2 ^ m), {rw hmod},
    rw [add_comm, ← add_sub_assoc, add_comm, add_sub_assoc, sub_self,
        add_zero] at hmodx,
    rw [hmodx, add_comm, add_sub_assoc, sub_self, add_zero],
    simp, },
  { have hmle1: m ≤ 1,
    { apply le_of_not_gt,
      rw gt,
      exact h2m, },
    have haodd: a n % 2 = 1 := hodd n,
    rw mod_def at haodd,
    have ha3m2: a n - 2 * (a n / 2) + 2 * (a n / 2) - 3 = 2 * (a n / 2) - 2,
    { rw [haodd, add_comm, add_sub_assoc],
      ring, },
    rw [add_comm, ← add_sub_assoc, add_comm, add_sub_assoc, sub_self,
        add_zero] at ha3m2,
    conv at ha3m2
    begin
      to_rhs,
      congr,
      skip,
      rw (show (2 : ℤ) = 2 * 1, by norm_num),
    end,
    rw ← mul_sub_left_distrib at ha3m2,
    have ha3d2 : 2 ∣ a n - 3 := dvd_of_mul_right_eq _ ha3m2.symm,
    rw (show (2 : ℤ) = 2^1, by norm_num) at ha3d2,
    have hm1div: (2 : ℤ)^m ∣ 2^1,
    { have hm1: ∃ m1 : ℕ, 1 = m + m1 := nat.exists_eq_add_of_le hmle1,
      cases hm1 with m1 hm1_h,
      conv
      begin
        congr,
        skip,
        congr,
        skip,
        rw hm1_h,
      end,
      rw pow_add,
      exact dvd_of_mul_right_eq (2^m1) rfl },
    exact dvd_trans hm1div ha3d2, },
end

-- If all powers of 2 divide a natural number, it is zero.
theorem zero_if_all_powers_divide_nat (a : ℕ) (h: ∀ m : ℕ, 2^m ∣ a) : a = 0 :=
begin
  by_cases haeq0: a = 0,
  { assumption },
  { have ha : 2^a ∣ a := h a,
    have h2pself : ∀ n : ℕ, n < 2^n,
    { intro n,
      exact nat.lt_pow_self dec_trivial n, },
    exfalso,
    have h2aself: a < 2^a := h2pself a,
    have hapos : a > 0 := nat.pos_of_ne_zero haeq0,
    have hself2a : 2^a ≤ a := (nat.le_of_dvd hapos) ha,
    have haa: a < a := lt_of_lt_of_le h2aself hself2a,
    exact lt_irrefl a haa },
end

-- If all powers of 2 divide a nonnegative integer, it is zero.
theorem zero_if_all_powers_divide_int (a : ℤ) (ha : 0 ≤ a) (h: ∀ m : ℕ, 2^m ∣ a) : a = 0 :=
begin
  have hb: ∃ b : ℕ, a = (b : ℤ),
  { use nat_abs a,
    exact eq_nat_abs_of_zero_le ha, },
  cases hb with b hb_h,
  have hbd : ∀ m : ℕ, 2^m ∣ b,
  { intro m,
    have hma: 2^m ∣ a := h m,
    rw hb_h at hma,
    norm_cast at hma,
    exact hma, },
  have hb0 : b = 0,
  { exact zero_if_all_powers_divide_nat b hbd, },
  rw [hb_h, hb0],
  refl,
end

-- If the first term of the sequence is at least 3, it is 3.
theorem first_term_three_if_at_least_three (a : ℕ → ℤ) (hodd : all_odd a)
    (hrec : p1_recurrence a) (ha3 : 3 ≤ a 0) : a 0 = 3 :=
begin
  have hallpowers: ∀ m : ℕ, 2^m ∣ a 0 - 3,
  { intro m,
    exact all_powers_divides_terms_minus_three a hodd hrec m 0, },
  have ha0: 0 ≤ a 0 - 3,
  { linarith, },
  have ha30: a 0 - 3 = 0 := zero_if_all_powers_divide_int (a 0 - 3) ha0 hallpowers,
  rw [← add_zero (3 : ℤ), ← ha30],
  ring,
end

-- The actual result of the problem.
theorem p1_result  (a : ℕ → ℤ) (hrec : p1_recurrence a) (ha3 : 2 < a 0) :
    all_odd a ↔ a 0 = 3 :=
begin
  rw [(show (2 : ℤ) = 3 - 1, by norm_num), sub_one_lt_iff] at ha3,
  split,
  { intro hodd, exact first_term_three_if_at_least_three a hodd hrec ha3, },
  { intro h03,
    have halln: ∀ n : ℕ, a n = 3,
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
