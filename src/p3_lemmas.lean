-- BMO2 2020 problem 3: lemmas of possibly more general use.  Are any
-- of these already in mathlib, possibly under a different name or in
-- a more general form, or should any of them be?

import data.fin
import tactic.norm_cast

open fin

/-- `a < b` as natural numbers if and only if `a < b` in `fin n`. -/
@[norm_cast] lemma coe_fin_lt {n : ℕ} {a b : fin n} : (a : ℕ) < (b : ℕ) ↔ a < b :=
iff.rfl

/-- `a ≤ b` as natural numbers if and only if `a ≤ b` in `fin n`. -/
@[norm_cast] lemma coe_fin_le {n : ℕ} {a b : fin n} : (a : ℕ) ≤ (b : ℕ) ↔ a ≤ b :=
iff.rfl

/-- Converting an in-range number to `fin (n + 1)` with `fin.of_nat`
produces a result whose value is the original number.  -/
lemma of_nat_val_of_lt {n : ℕ} {a : ℕ} (h : a < n + 1) :
  ((fin.of_nat a) : fin (n + 1)).val = a :=
nat.mod_eq_of_lt h

/-- Converting the value of a `fin (n + 1)` to `fin (n + 1)` with `fin.of_nat`
results in the same value.  -/
lemma of_nat_val_eq_self {n : ℕ} (a : fin (n + 1)) : fin.of_nat a.val = a :=
begin
  rw fin.eq_iff_veq,
  exact of_nat_val_of_lt a.is_lt
end

/-- `fin.of_nat` of an in-range number, converted back to `ℕ`, is that
number. -/
lemma of_nat_coe_of_lt {n : ℕ} {a : ℕ} (h : a < n + 1) :
  (((fin.of_nat a) : fin (n + 1)) : ℕ) = a :=
nat.mod_eq_of_lt h

/-- Converting a `fin (n + 1)` to `ℕ` and back with `fin.of_nat` results in
the same value. -/
lemma of_nat_coe_eq_self {n : ℕ} (a : fin (n + 1)) : fin.of_nat (a : ℕ) = a :=
of_nat_val_eq_self a
