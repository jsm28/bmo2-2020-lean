-- BMO2 2020 problem 1: lemmas of possibly more general use.  Are any
-- of these already in mathlib, possibly under a different name or in
-- a more general form, or should any of them be?

import data.int.basic

open int

/-- If an integer is `a` mod `b`, there are corresponding cases for its
    value mod `c * b`. -/
lemma mod_mul_eq_cases (n : ℤ) (a : ℤ) (b : ℤ) (c : ℤ) (hbpos : 0 < b) (hcpos : 0 < c)
  (hmod : n % b = a) :
  ∃ d : ℤ, 0 ≤ d ∧ d < c ∧ n % (c * b) = a + d * b :=
begin
  existsi ((n % (c * b)) / b),
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

/-- If `a % b = c` then `b` divides `a - c`. -/
lemma dvd_sub_of_mod_eq (a b c : ℤ) (h : a % b = c) : b ∣ a - c :=
begin
  have hx : a % b % b = c % b, {rw h},
  rw [mod_mod, ←mod_sub_cancel_right c, sub_self, zero_mod] at hx,
  exact dvd_of_mod_eq_zero hx
end

/-- If a larger number divides a natural number, it is zero. -/
lemma eq_zero_of_dvd_of_gt {a b : ℕ} (w : a ∣ b) (h : b < a) : b = 0 :=
nat.eq_zero_of_dvd_of_div_eq_zero w
  ((nat.div_eq_zero_iff (lt_of_le_of_lt (zero_le b) h)).elim_right h)

/-- If a number with larger absolute value divides an integer, it is
    zero. -/
lemma eq_zero_of_dvd_of_nat_abs_gt_nat_abs {a b : ℤ} (w : a ∣ b) (h : nat_abs b < nat_abs a) :
  b = 0 :=
begin
  rw [←nat_abs_dvd, ←dvd_nat_abs, coe_nat_dvd] at w,
  rw ←nat_abs_eq_zero,
  exact eq_zero_of_dvd_of_gt w h
end

/-- If two integers are congruent to a sufficiently large modulus,
    they are equal. -/
lemma eq_of_mod_eq_of_nat_abs_gt_nat_abs_sub {a b c : ℤ} (h1 : a % b = c)
    (h2 : nat_abs (a - c) < nat_abs b) :
  a = c :=
eq_of_sub_eq_zero (eq_zero_of_dvd_of_nat_abs_gt_nat_abs (dvd_sub_of_mod_eq a b c h1) h2)
