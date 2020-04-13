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

/-- Converting an in-range number to `fin n` with `fin.of_nat`
    produces a result whose value is the original number.  -/
theorem of_nat_val {n : ℕ} (a : ℕ) (h : a < nat.succ n) :
  ((fin.of_nat a) : fin (nat.succ n)).val = a :=
nat.mod_eq_of_lt h

/-- Converting the value of a `fin n` to `fin n` with `fin.of_nat`
    produces a result whose value is the original number.  -/
theorem of_nat_val_self {n : ℕ} (a : fin (nat.succ n)) :
  ((fin.of_nat a.val) : fin (nat.succ n)).val = a.val :=
of_nat_val a.val a.is_lt

/-- Converting the value of a `fin n` to `fin n` with `fin.of_nat`
    results in the same value.  -/
theorem of_nat_val_eq_self {n : ℕ} (a : fin (nat.succ n)) : fin.of_nat a.val = a :=
begin
  rw fin.eq_iff_veq,
  exact of_nat_val_self a
end

/-- Converting a `fin n` to `ℕ` and back with `fin.of_nat` results in
    the same value. -/
theorem of_nat_coe_eq_self {n : ℕ} (a : fin (nat.succ n)) : fin.of_nat (a : ℕ) = a :=
of_nat_val_eq_self a

/-- `fin.of_nat` of an in-range number, converted back to `ℕ`, is that
    number. -/
theorem of_nat_coe {n : ℕ} (a : ℕ) (h : a < nat.succ n) :
  (((fin.of_nat a) : fin (nat.succ n)) : ℕ) = a :=
nat.mod_eq_of_lt h

/-- `fin.of_nat 0`, converted to `ℕ`, is 0. -/
theorem of_nat_coe_zero {n : ℕ} : (((fin.of_nat 0) : fin (nat.succ n)) : ℕ) = 0 :=
rfl

/--  If `a` and `b` are equal mod `c`, `a - b` is zero mod `c`. -/
theorem sub_mod_eq_zero_of_mod_eq (a b c : ℕ) (h : a % c = b % c) : (a - b) % c = 0 :=
begin
  rw [←nat.mod_add_div a c, ←nat.mod_add_div b c, ←h, ←nat.sub_sub, nat.add_sub_cancel_left,
      ←nat.mul_sub_left_distrib, nat.mul_mod_right]
end
