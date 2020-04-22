-- BMO2 2020 problem 1: lemmas of possibly more general use.  Are any
-- of these already in mathlib, possibly under a different name or in
-- a more general form, or should any of them be?

import data.int.basic

open int

/-- If an integer is `a` mod `b`, there are corresponding cases for its
value mod `c * b`. -/
lemma mod_mul_eq_cases {n a b c : ℤ} (hbpos : 0 < b) (hcpos : 0 < c) (hmod : n % b = a) :
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
