-- BMO2 2020 problem 3: lemmas of possibly more general use.  Are any
-- of these already in mathlib, possibly under a different name or in
-- a more general form, or should any of them be?

import data.fin
import tactic.norm_cast

open fin

/-- `a < b` as natural numbers if and only if `a < b` in `fin n`. -/
@[elim_cast]
lemma coe_fin_lt {n : ℕ} {a b : fin n} : (a : ℕ) < (b : ℕ) ↔ a < b :=
iff.rfl

/-- `a ≤ b` as natural numbers if and only if `a ≤ b` in `fin n`. -/
@[elim_cast]
lemma coe_fin_le {n : ℕ} {a b : fin n} : (a : ℕ) ≤ (b : ℕ) ↔ a ≤ b :=
iff.rfl

/--  If `a` and `b` are equal mod `c`, `a - b` is zero mod `c`. -/
theorem sub_mod_eq_zero_of_mod_eq (a b c : ℕ) (h : a % c = b % c) : (a - b) % c = 0 :=
begin
  rw [←nat.mod_add_div a c, ←nat.mod_add_div b c, ←h, ←nat.sub_sub, nat.add_sub_cancel_left,
      ←nat.mul_sub_left_distrib, nat.mul_mod_right]
end
