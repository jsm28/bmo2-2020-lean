-- BMO2 2020 problem 3: lemmas of possibly more general use.  Are any
-- of these already in mathlib, possibly under a different name or in
-- a more general form, or should any of them be?

import data.fin
import data.zmod.basic
import tactic.norm_cast

open fin

/-- `a < b` as natural numbers if and only if `a < b` in `fin n`. -/
@[norm_cast] lemma coe_fin_lt {n : ℕ} {a b : fin n} : (a : ℕ) < (b : ℕ) ↔ a < b :=
iff.rfl

/-- `a ≤ b` as natural numbers if and only if `a ≤ b` in `fin n`. -/
@[norm_cast] lemma coe_fin_le {n : ℕ} {a b : fin n} : (a : ℕ) ≤ (b : ℕ) ↔ a ≤ b :=
iff.rfl

/-- Converting an in-range number to `fin (n + 1)` produces a result
whose value is the original number.  -/
lemma coe_val_of_lt {n : ℕ} {a : ℕ} (h : a < n + 1) :
  (a : fin (n + 1)).val = a :=
begin
  rw ←fin.of_nat_eq_coe,
  exact nat.mod_eq_of_lt h
end

/-- Converting the value of a `fin (n + 1)` to `fin (n + 1)` results
in the same value.  -/
@[simp] lemma coe_val_eq_self {n : ℕ} (a : fin (n + 1)) : (a.val : fin (n + 1)) = a :=
begin
  rw fin.eq_iff_veq,
  exact coe_val_of_lt a.is_lt
end

/-- Coercing an in-range number to `fin (n + 1)`, and converting back
to `ℕ`, results in that number. -/
lemma coe_coe_of_lt {n : ℕ} {a : ℕ} (h : a < n + 1) :
  ((a : fin (n + 1)) : ℕ) = a :=
coe_val_of_lt h

/-- Converting a `fin (n + 1)` to `ℕ` and back results in the same
value. -/
@[simp] lemma coe_coe_eq_self {n : ℕ} (a : fin (n + 1)) : ((a : ℕ) : fin (n + 1)) = a :=
coe_val_eq_self a
