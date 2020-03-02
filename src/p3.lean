-- BMO2 2020 problem 3.

import data.finset
import data.fintype
import data.nat.parity
import logic.function
import tactic.linarith

import p3_lemmas

noncomputable theory
open_locale classical

open finset

-- The grid.
abbreviation grid := fin 2019 × fin 2019

-- A colouring of the grid (the set of black cells).
abbreviation colouring := finset grid

-- A square subgrid of the coloured grid.  (This definition allows the
-- square to go off the edges, so separate hypotheses are needed where
-- that is undesirable.)
def subcolouring (c : colouring) (a b : fin 2019) (k : ℕ) : finset grid :=
finset.filter (λ p : grid, a ≤ p.1 ∧ b ≤ p.2 ∧
                               (p.1 : ℕ) < (a : ℕ) + k ∧ (p.2 : ℕ) < (b : ℕ) + k) c

-- The complement of a colouring.
def complement (c : colouring) : colouring := finset.univ \ c

-- The number of black cells in a subgrid.
def sub_black (c : colouring) (a b : fin 2019) (k : ℕ) : ℕ :=
finset.card (subcolouring c a b k)

-- The number of white cells in a subgrid.
def sub_white (c : colouring) (a b : fin 2019) (k : ℕ) : ℕ :=
finset.card (subcolouring (complement c) a b k)

-- The imbalance of a subgrid.
def sub_imbalance (c : colouring) (a b : fin 2019) (k : ℕ) : ℕ :=
int.nat_abs (((sub_black c a b k) : ℤ) - ((sub_white c a b k) : ℤ))

-- Whether a subgrid is balanced.
def sub_balanced (c : colouring) (a b : fin 2019) (k : ℕ) : Prop :=
sub_imbalance c a b k ≤ 1

-- Whether a colouring is balanced for subgrids of side k.
def balanced_k (c : colouring) (k : ℕ) : Prop :=
∀ (a b : fin 2019), (a : ℕ) + k ≤ 2019 → (b : ℕ) + k ≤ 2019 → sub_balanced c a b k

-- Whether a colouring is balanced.
def balanced (c : colouring) : Prop :=
∀ (k : ℕ), 1 ≤ k → k ≤ 2019 → balanced_k c k

-- The set of balanced colourings.
def balanced_colourings : finset colouring :=
finset.univ.filter balanced

-- Adding the numbers of black and white cells in a subgrid.
theorem sub_black_add_sub_white (c : colouring) (a b : fin 2019) (k : ℕ)
    (ha : (a : ℕ) + k ≤ 2019) (hb : (b : ℕ) + k ≤ 2019) :
  sub_black c a b k + sub_white c a b k = k * k :=
begin
  unfold sub_black sub_white subcolouring complement,
  rw [←card_union_add_card_inter, ←filter_union, filter_inter, inter_filter,
      union_sdiff_of_subset (subset_univ _), inter_sdiff_self, filter_empty, filter_empty,
      card_empty, add_zero],
  have h2019 : nat.succ 2018 = 2019,
  { rw nat.succ_eq_add_one,
    norm_num },
  refine card_eq_of_bijective (λ i h, ⟨fin.of_nat (a + i / k : ℕ), fin.of_nat (b + i % k : ℕ)⟩)
    _ _ _,
  { intro p,
    intro hp,
    rw mem_filter at hp,
    cases hp with hpu hp1,
    cases hp1 with ha1 hp1,
    cases hp1 with hb1 hp1,
    cases hp1 with ha2 hb2,
    use ((p.fst : ℕ) - (a : ℕ)) * k + ((p.snd : ℕ) - (b : ℕ)),
    rw fin.le_iff_val_le_val at ha1,
    rw fin.le_iff_val_le_val at hb1,
    repeat {rw fin.coe_eq_val at *},
    rw ←nat.sub_lt_left_iff_lt_add ha1 at ha2,
    rw ←nat.sub_lt_left_iff_lt_add hb1 at hb2,
    split,
    { have h1 : (p.fst.val - a.val) * k ≤ (k - 1) * k :=
        mul_le_mul_of_nonneg_right (nat.le_pred_of_lt ha2) (nat.zero_le _),
      have h2 : k * k = (k - 1) * k + k,
      { cases k with kk,
        { norm_num },
        { repeat { rw nat.succ_eq_add_one },
          rw nat.add_sub_cancel,
          ring } },
      linarith },
    { ext,
      { unfold prod.fst fin.of_nat,
        apply fin.eq_of_veq,
        unfold fin.val,
        cases k with kk,
        { exfalso,
          exact nat.not_lt_zero _ ha2 },
        { rw [add_comm ((p.fst.val - a.val) * nat.succ kk) (p.snd.val - b.val),
              nat.add_mul_div_right _ _ (nat.zero_lt_succ _), nat.div_eq_of_lt hb2, zero_add,
              ←nat.add_sub_assoc ha1, nat.add_sub_cancel_left],
          apply nat.mod_eq_of_lt,
          exact p.fst.is_lt } },
      { unfold prod.snd fin.of_nat,
        apply fin.eq_of_veq,
        unfold fin.val,
        cases k with kk,
        { exfalso,
          exact nat.not_lt_zero _ ha2 },
        { rw [add_comm ((p.fst.val - a.val) * nat.succ kk) (p.snd.val - b.val),
              nat.add_mul_mod_self_right, nat.mod_eq_of_lt hb2, ←nat.add_sub_assoc hb1,
              nat.add_sub_cancel_left],
          apply nat.mod_eq_of_lt,
          exact p.snd.is_lt } } } },
  { intros i hi,
    rw mem_filter,
    split,
    { exact mem_univ _ },
    { repeat { rw fin.le_def },
      repeat { rw fin.coe_eq_val at * },
      unfold fin.of_nat prod.fst prod.snd fin.val,
      repeat { rw h2019 },
      have hkpos : 0 < k,
      { by_contradiction,
        have hk0 : k = 0, {linarith},
        rw [hk0, mul_zero] at hi,
        exact nat.not_lt_zero _ hi },
      have hidiv : i / k < k,
      { rw nat.div_lt_iff_lt_mul _ _ hkpos,
        exact hi },
      have himod : i % k < k := nat.mod_lt _ hkpos,
      repeat { split },
      { have hax : (a.val + i / k) < 2019, {linarith},
        rw nat.mod_eq_of_lt hax,
        exact nat.le_add_right _ _ },
      { have hbx : (b.val + i % k) < 2019, {linarith},
        rw nat.mod_eq_of_lt hbx,
        exact nat.le_add_right _ _ },
      { have hax : (a.val + i / k) < 2019, {linarith},
        rw nat.mod_eq_of_lt hax,
        linarith },
      { have hbx : (b.val + i % k) < 2019, {linarith},
        rw nat.mod_eq_of_lt hbx,
        linarith } } },
  { intros i j hi hj heq,
    rw prod.mk.inj_iff at heq,
    cases heq with heq1 heq2,
    unfold fin.of_nat at heq1 heq2,
    injection heq1 with heq1a,
    injection heq2 with heq2a,
    rw [h2019] at heq1a,
    rw [h2019] at heq2a,
    repeat { rw fin.coe_eq_val at * },
    have hkpos : 0 < k,
    { by_contradiction,
      have hk0 : k = 0, {linarith},
      rw [hk0, mul_zero] at hi,
      exact nat.not_lt_zero _ hi },
    have hidiv : i / k < k,
    { rw nat.div_lt_iff_lt_mul _ _ hkpos,
      exact hi },
    have himod : i % k < k := nat.mod_lt _ hkpos,
    have hjdiv : j / k < k,
    { rw nat.div_lt_iff_lt_mul _ _ hkpos,
      exact hj },
    have hjmod : j % k < k := nat.mod_lt _ hkpos,
    have hai : a.val + i / k < 2019, {linarith},
    have haj : a.val + j / k < 2019, {linarith},
    have hbi : b.val + i % k < 2019, {linarith},
    have hbj : b.val + j % k < 2019, {linarith},
    rw [nat.mod_eq_of_lt hai, nat.mod_eq_of_lt haj, add_left_cancel_iff] at heq1a,
    rw [nat.mod_eq_of_lt hbi, nat.mod_eq_of_lt hbj, add_left_cancel_iff] at heq2a,
    rw [←nat.mod_add_div i k, ←nat.mod_add_div j k, heq1a, heq2a] }
end

-- Number of black cells in a subgrid, inequality.
theorem sub_black_le (c : colouring) (a b : fin 2019) (k : ℕ)
    (ha : (a : ℕ) + k ≤ 2019) (hb : (b : ℕ) + k ≤ 2019) : sub_black c a b k ≤ k * k :=
begin
  rw ← sub_black_add_sub_white c a b k ha hb,
  exact nat.le_add_right _ _,
end

-- Number of white cells in a subgrid, more convenient form.
theorem sub_white_eq (c : colouring) (a b : fin 2019) (k : ℕ)
    (ha : (a : ℕ) + k ≤ 2019) (hb : (b : ℕ) + k ≤ 2019) :
  sub_white c a b k = k * k - sub_black c a b k :=
begin
  symmetry,
  rw [nat.sub_eq_iff_eq_add (sub_black_le c a b k ha hb), add_comm],
  symmetry,
  exact sub_black_add_sub_white c a b k ha hb
end

-- Imbalance in terms only of number of black cells.
theorem imbalance_eq (c : colouring) (a b : fin 2019) (k : ℕ)
    (ha : (a : ℕ) + k ≤ 2019) (hb : (b : ℕ) + k ≤ 2019) :
  sub_imbalance c a b k = int.nat_abs (2 * ((sub_black c a b k) : ℤ) - ((k * k) : ℤ)) :=
begin
  unfold sub_imbalance,
  rw sub_white_eq c a b k ha hb,
  congr' 1,
  rw int.coe_nat_sub (sub_black_le c a b k ha hb),
  norm_cast,
  rw ←sub_add,
  push_cast,
  ring
end

-- We wish to count colourings by whether rows, columns or both
-- reverse the colours of the previous row or column, and having done
-- that count for the case of rows we wish to deduce it for the case
-- of columns.  So prove results about transposing a colouring.

-- A cell, transposed.
def transpose_cell (p : grid) : grid := ⟨p.snd, p.fst⟩

-- Transposing twice produces the original cell.
theorem transpose_cell_involutive : function.involutive transpose_cell :=
begin
  intro p,
  unfold transpose_cell,
  ext,
  { unfold prod.fst },
  { unfold prod.snd },
end

-- And transposing is thus bijective.
theorem transpose_cell_bijective : function.bijective transpose_cell :=
function.involutive.bijective transpose_cell_involutive

-- And the composition is the identity.
theorem transpose_cell_twice_id : transpose_cell ∘ transpose_cell = id :=
begin
  rw ←function.involutive_iff_iter_2_eq_id.elim_left transpose_cell_involutive,
  refl
end

-- And the composition is the identity, variant form.
theorem transpose_cell_twice_id' (p : grid) :
  transpose_cell (transpose_cell p) = p :=
begin
  change (transpose_cell ∘ transpose_cell) p = p,
  rw transpose_cell_twice_id,
  refl
end

-- A colouring, transposed.
def transpose_colouring (c : colouring) : colouring := c.image transpose_cell

-- Transposing twice produces the original colouring.
theorem transpose_colouring_involutive : function.involutive transpose_colouring :=
begin
  intro p,
  unfold transpose_colouring,
  rw image_image,
  rw transpose_cell_twice_id,
  exact image_id
end

-- And transposing is thus bijective.
theorem transpose_colouring_bijective : function.bijective transpose_colouring :=
function.involutive.bijective transpose_colouring_involutive

-- And the composition is the identity.
theorem transpose_colouring_twice_id : transpose_colouring ∘ transpose_colouring = id :=
begin
  rw ←function.involutive_iff_iter_2_eq_id.elim_left transpose_colouring_involutive,
  refl
end

-- And the composition is the identity, variant form.
theorem transpose_colouring_twice_id' (c : colouring) :
  transpose_colouring (transpose_colouring c) = c :=
begin
  change (transpose_colouring ∘ transpose_colouring) c = c,
  rw transpose_colouring_twice_id,
  refl
end

-- Condition for a cell to be in the transpose.
theorem cell_in_transpose_iff (c : colouring) (a b : fin 2019) :
  (a, b) ∈ c ↔ (b, a) ∈ transpose_colouring c :=
begin
  unfold transpose_colouring,
  rw mem_image,
  split,
  { intro h,
    use (a, b),
    use h,
    refl },
  { intro h,
    cases h with x hx,
    cases hx with hx1 hx2,
    have hx3 : (a, b) = transpose_cell (transpose_cell x),
    { rw hx2,
      unfold transpose_cell },
    rw transpose_cell_twice_id' at hx3,
    convert hx1 }
end

-- Condition for a cell not to be in the transpose.
theorem cell_not_in_transpose_iff (c : colouring) (a b : fin 2019) :
  (a, b) ∉ c ↔ (b, a) ∉ transpose_colouring c :=
begin
  rw not_iff_not,
  exact cell_in_transpose_iff c a b
end

-- Transposing a subcolouring produces the same results as taking the
-- corresponding subcolouring of the transpose.
theorem transpose_subcolouring (c : colouring) (a b : fin 2019) (k : ℕ) :
  transpose_colouring (subcolouring c a b k) = subcolouring (transpose_colouring c) b a k :=
begin
  unfold transpose_colouring subcolouring,
  ext,
  rw [mem_image, mem_filter, mem_image],
  split,
  { intro h,
    cases h with p hp,
    cases hp with hp2 hpt,
    rw mem_filter at hp2,
    split,
    { use p,
      exact and.intro hp2.1 hpt },
    { unfold transpose_cell at hpt,
      rw ←hpt,
      unfold prod.fst prod.snd,
      rcases hp2 with ⟨hp2a, hp2b, hp2c, hp2d, hp2e⟩,
      exact and.intro hp2c (and.intro hp2b (and.intro hp2e hp2d)) } },
  { intro h,
    cases h with h1 h2,
    cases h1 with p hp,
    cases hp with hp1 hpt,
    unfold transpose_cell at hpt,
    rw ←hpt at h2,
    unfold prod.fst prod.snd at h2,
    rcases h2 with ⟨h2a, h2b, h2c, h2d⟩,
    use p,
    rw mem_filter,
    exact and.intro (and.intro hp1 (and.intro h2b (and.intro h2a (and.intro h2d h2c)))) hpt },
end

-- The number of black cells in a subgrid behaves as expected under
-- transposition.
theorem transpose_sub_black (c : colouring) (a b : fin 2019) (k : ℕ) :
  sub_black c a b k = sub_black (transpose_colouring c) b a k :=
begin
  unfold sub_black,
  rw ←transpose_subcolouring,
  unfold transpose_colouring,
  rw card_image_of_injective _ transpose_cell_bijective.1
end

-- If a colouring is balanced for subgrids of side k, so is its
-- transpose.
theorem transpose_balanced_k (c : colouring) (k : ℕ) (h : balanced_k c k) :
  balanced_k (transpose_colouring c) k :=
begin
  unfold balanced_k,
  intros a b ha hb,
  unfold sub_balanced,
  rw imbalance_eq _ _ _ _ ha hb,
  rw ←transpose_sub_black,
  rw ← imbalance_eq _ _ _ _ hb ha,
  exact h b a hb ha
end

-- If a colouring is balanced, so is its transpose.
theorem transpose_balanced (c : colouring) (h : balanced c) :
  balanced (transpose_colouring c):=
begin
  intros k hk1 hk2,
  exact transpose_balanced_k c k (h k hk1 hk2)
end

-- A colouring is balanced if and only if its transpose is.
theorem transpose_balanced_iff (c : colouring) :
  balanced c ↔ balanced (transpose_colouring c):=
begin
  split,
  { apply transpose_balanced, },
  { intro h,
    convert transpose_balanced (transpose_colouring c) h,
    symmetry,
    exact transpose_colouring_involutive c },
end

-- Colourings with alternating rows.
def rows_alternate (c : colouring) : Prop :=
∀ (a b : fin 2019) (h : (a : ℕ) < 2018), (a, b) ∈ c ↔ ¬ (fin.of_nat (a + 1), b) ∈ c

-- Colourings with alternating columns.
def cols_alternate (c : colouring) : Prop :=
∀ (a b : fin 2019) (h : (b : ℕ) < 2018), (a, b) ∈ c ↔ ¬ (a, fin.of_nat (b + 1)) ∈ c

-- Rows alternate if and only if columns of transpose alternate.
theorem rows_alternate_iff_transpose (c : colouring) :
  rows_alternate c ↔ cols_alternate (transpose_colouring c) :=
begin
  split,
  { unfold rows_alternate cols_alternate transpose_colouring,
    intros h a b,
    intro hb,
    convert h b a hb using 1,
    { rw ←iff_eq_eq,
      exact (cell_in_transpose_iff c b a).symm },
    { rw ←iff_eq_eq,
      exact (cell_not_in_transpose_iff c _ _).symm } },
  { unfold rows_alternate cols_alternate transpose_colouring,
    intros h a b,
    intro ha,
    convert h b a ha using 1,
    { rw ←iff_eq_eq,
      exact cell_in_transpose_iff c a b },
    { rw ←iff_eq_eq,
      exact cell_not_in_transpose_iff c _ _ } }
end

-- Split into cases according to which of rows and columns alternate.

def not_rows_alternate (c : colouring) : Prop :=
¬ rows_alternate c

def not_cols_alternate (c : colouring) : Prop :=
¬ cols_alternate c

def balanced_colourings_r : finset colouring :=
balanced_colourings.filter rows_alternate

def balanced_colourings_no_r : finset colouring :=
balanced_colourings.filter not_rows_alternate

-- Together these are all balanced colourings.
theorem rows_alternate_or_not :
  balanced_colourings_r ∪ balanced_colourings_no_r = balanced_colourings :=
begin
  unfold balanced_colourings_r balanced_colourings_no_r,
  convert filter_union_filter_neg_eq balanced_colourings
end

-- These have empty intersection.
theorem rows_alternate_xor_not :
  balanced_colourings_r ∩ balanced_colourings_no_r = ∅ :=
begin
  unfold balanced_colourings_r balanced_colourings_no_r,
  convert filter_inter_filter_neg_eq balanced_colourings
end

-- Thus the cardinality of the set of balanced colourings.
theorem card_split_r :
  card balanced_colourings = card balanced_colourings_r + card balanced_colourings_no_r :=
begin
  rw ← rows_alternate_or_not,
  convert card_union_add_card_inter _ _,
  { rw rows_alternate_xor_not,
    simp }
end

-- Now repeat these arguments to split up again by whether columns
-- alternate or not.

def balanced_colourings_r_c : finset colouring :=
balanced_colourings_r.filter cols_alternate

def balanced_colourings_r_no_c : finset colouring :=
balanced_colourings_r.filter not_cols_alternate

def balanced_colourings_no_r_c : finset colouring :=
balanced_colourings_no_r.filter cols_alternate

def balanced_colourings_no_r_no_c : finset colouring :=
balanced_colourings_no_r.filter not_cols_alternate

theorem r_cols_alternate_or_not :
  balanced_colourings_r_c ∪ balanced_colourings_r_no_c = balanced_colourings_r :=
begin
  unfold balanced_colourings_r_c balanced_colourings_r_no_c,
  convert filter_union_filter_neg_eq balanced_colourings_r
end

theorem r_cols_alternate_xor_not :
  balanced_colourings_r_c ∩ balanced_colourings_r_no_c = ∅ :=
begin
  unfold balanced_colourings_r_c balanced_colourings_r_no_c,
  convert filter_inter_filter_neg_eq balanced_colourings_r
end

theorem card_split_r_c :
  card balanced_colourings_r = card balanced_colourings_r_c + card balanced_colourings_r_no_c :=
begin
  rw ← r_cols_alternate_or_not,
  convert card_union_add_card_inter _ _,
  { rw r_cols_alternate_xor_not,
    simp }
end

theorem no_r_cols_alternate_or_not :
  balanced_colourings_no_r_c ∪ balanced_colourings_no_r_no_c = balanced_colourings_no_r :=
begin
  unfold balanced_colourings_no_r_c balanced_colourings_no_r_no_c,
  convert filter_union_filter_neg_eq balanced_colourings_no_r
end

theorem no_r_cols_alternate_xor_not :
  balanced_colourings_no_r_c ∩ balanced_colourings_no_r_no_c = ∅ :=
begin
  unfold balanced_colourings_no_r_c balanced_colourings_no_r_no_c,
  convert filter_inter_filter_neg_eq balanced_colourings_no_r
end

theorem card_split_no_r_c :
  card balanced_colourings_no_r =
    card balanced_colourings_no_r_c + card balanced_colourings_no_r_no_c :=
begin
  rw ← no_r_cols_alternate_or_not,
  convert card_union_add_card_inter _ _,
  { rw no_r_cols_alternate_xor_not,
    simp }
end

-- Thus the cardinality of the set of balanced colourings, fully split.
theorem card_split_4 :
  card balanced_colourings = (card balanced_colourings_r_c + card balanced_colourings_r_no_c) +
    (card balanced_colourings_no_r_c + card balanced_colourings_no_r_no_c) :=
begin
  rw [card_split_r, card_split_r_c, card_split_no_r_c]
end

-- Two of those terms have the same value.
theorem card_r_no_c_eq_c_no_r :
  card balanced_colourings_r_no_c = card balanced_colourings_no_r_c :=
begin
  unfold balanced_colourings_r_no_c balanced_colourings_no_r_c balanced_colourings_r
    balanced_colourings_no_r,
  rw [filter_filter, filter_filter],
  convert card_image_of_injective (filter (λ (a : colouring), not_rows_alternate a ∧ cols_alternate a) balanced_colourings) transpose_colouring_bijective.1,
  ext,
  rw [mem_image, mem_filter],
  split,
  { intro h,
    rcases h with ⟨hb, hr, hnc⟩,
    unfold not_cols_alternate at hnc,
    use transpose_colouring a,
    rw mem_filter,
    unfold not_rows_alternate,
    rw [←rows_alternate_iff_transpose, rows_alternate_iff_transpose,
        transpose_colouring_twice_id'],
    unfold balanced_colourings at *,
    rw mem_filter at *,
    rw ←transpose_balanced_iff,
    exact and.intro (and.intro (and.intro (mem_univ _) hb.2) (and.intro hnc hr)) rfl },
  { intro h,
    cases h with b hb,
    cases hb with hb1 hb2,
    rw mem_filter at hb1,
    cases hb1 with hb1bal hb1b,
    cases hb1b with hb1nr hb1c,
    have hbx : transpose_colouring (transpose_colouring b) = transpose_colouring a, {rw hb2},
    rw transpose_colouring_twice_id' at hbx,
    rw hbx at hb1bal hb1nr hb1c,
    unfold not_rows_alternate at hb1nr,
    unfold not_cols_alternate,
    unfold balanced_colourings at *,
    rw mem_filter at *,
    rw ←transpose_balanced_iff at hb1bal,
    rw ←rows_alternate_iff_transpose at hb1c,
    rw [rows_alternate_iff_transpose, transpose_colouring_twice_id'] at hb1nr,
    exact and.intro (and.intro (mem_univ _) hb1bal.2) (and.intro hb1c hb1nr) }
end

-- Thus the cardinality of the set of balanced colourings, in three parts.
theorem card_split_3 :
  card balanced_colourings = card balanced_colourings_r_c +
    2 * card balanced_colourings_r_no_c + card balanced_colourings_no_r_no_c :=
begin
  rw [card_split_4, ←card_r_no_c_eq_c_no_r],
  ring
end

-- Having disposed of the trivial preliminaries, we now need to
-- classify balanced colourings to determine the three terms in the
-- above sum.

-- First, we use the property of being balanced for subgrids of side 2
-- to show that either rows alternate or columns alternate.

-- A subgrid of side 2 is balanced if and only if it has exactly two
-- black cells.
theorem sub_balanced_2 (c : colouring) (a b : fin 2019)
    (ha : (a : ℕ) < 2018) (hb : (b : ℕ) < 2018) :
  sub_balanced c a b 2 ↔ sub_black c a b 2 = 2 :=
begin
  unfold sub_balanced,
  rw [imbalance_eq c a b 2 (by linarith) (by linarith),
      (show (2 : ℤ) = ((2 : ℕ) : ℤ), by norm_cast),
      ←mul_sub_left_distrib ((2 : ℕ) : ℤ) _ _, int.nat_abs_mul, mul_comm],
  norm_cast,
  rw ←nat.le_div_iff_mul_le _ _ (dec_trivial : 2 > 0),
  norm_num,
  rw [add_comm, ←sub_eq_add_neg, sub_eq_zero_iff_eq],
  norm_cast
end

-- A subgrid of side 2 is made up of a given 4 cells.
theorem subcolouring_2 (c : colouring) (a b : fin 2019)
    (ha : (a : ℕ) < 2018) (hb : (b : ℕ) < 2018) :
  subcolouring c a b 2 = (c.filter (λ p, p = (a, b))) ∪
                         (c.filter (λ p, p = (a, fin.of_nat (b + 1)))) ∪
                         (c.filter (λ p, p = (fin.of_nat (a + 1), b))) ∪
                         (c.filter (λ p, p = (fin.of_nat (a + 1), fin.of_nat (b + 1)))) :=
begin
  unfold subcolouring,
  repeat {rw filter_union_right},
  ext,
  repeat {rw mem_filter},
  cases a with a_val ah,
  cases b with b_val bh,
  cases a_1 with x y,
  cases x with x_val xh,
  cases y with y_val yh,
  repeat { rw fin.coe_eq_val at * },
  unfold fin.val at ha hb,
  have hao1 : nat.succ a_val < 2019,
  { rw nat.succ_eq_add_one, linarith },
  have hbo1 : nat.succ b_val < 2019,
  { rw nat.succ_eq_add_one, linarith },
  have h2019 : nat.succ 2018 = 2019,
  { rw nat.succ_eq_add_one,
    norm_num },
  have hao : fin.of_nat (a_val + 1) = ⟨a_val + 1, hao1⟩,
  { unfold fin.of_nat,
    apply fin.eq_of_veq,
    unfold fin.val,
    rw h2019,
    apply nat.mod_eq_of_lt,
    linarith },
  have hbo : fin.of_nat (b_val + 1) = ⟨b_val + 1, hbo1⟩,
  { unfold fin.of_nat,
    apply fin.eq_of_veq,
    unfold fin.val,
    rw h2019,
    apply nat.mod_eq_of_lt,
    linarith },
  repeat { unfold prod.fst prod.snd fin.val, rw [fin.le_def, prod.mk.inj_iff, fin.eq_iff_veq,
                                                 hao, hbo] },
  repeat { unfold fin.val, rw [prod.mk.inj_iff, fin.eq_iff_veq] },
  repeat { rw fin.eq_iff_veq, unfold fin.val },
  rw fin.le_def,
  unfold fin.val,
  split,
  { intro h,
    rcases h with ⟨h1, h2, h3, h4, h5⟩,
    split,
    { exact h1 },
    { by_cases hxe : x_val = a_val,
      { by_cases hye : y_val = b_val,
        { tauto },
        { have hy1 : y_val = b_val + 1,
          { rw [(show b_val + 2 = b_val + 1 + 1, by ring), nat.lt_add_one_iff] at h5,
            by_contradiction hc,
            have hlt : y_val < b_val + 1 := lt_of_le_of_ne h5 hc,
            rw nat.lt_add_one_iff at hlt,
            exact hye (le_antisymm hlt h3) },
          tauto } },
      { have hx1 : x_val = a_val + 1,
        { rw [(show a_val + 2 = a_val + 1 + 1, by ring), nat.lt_add_one_iff] at h4,
            by_contradiction hc,
            have hlt : x_val < a_val + 1 := lt_of_le_of_ne h4 hc,
            rw nat.lt_add_one_iff at hlt,
            exact hxe (le_antisymm hlt h2) },
        by_cases hye : y_val = b_val,
        { tauto },
        { have hy1 : y_val = b_val + 1,
          { rw [(show b_val + 2 = b_val + 1 + 1, by ring), nat.lt_add_one_iff] at h5,
            by_contradiction hc,
            have hlt : y_val < b_val + 1 := lt_of_le_of_ne h5 hc,
            rw nat.lt_add_one_iff at hlt,
            exact hye (le_antisymm hlt h3) },
          tauto } } } },
  { intro h,
    cases h with h1 h,
    repeat { cases h },
    { split,
      { exact h1 },
      { repeat { rw [h_left, h_right] },
        exact and.intro (by refl) (and.intro (by refl) (and.intro
          (lt_add_of_pos_right _ dec_trivial) (lt_add_of_pos_right _ dec_trivial))) } },
    { split,
      { exact h1 },
      { repeat { rw [h_left, h_right] },
        exact and.intro (by refl) (and.intro (le_add_of_nonneg_right dec_trivial)
          (and.intro (lt_add_of_pos_right _ dec_trivial)
                     (by linarith))) } },
    { split,
      { exact h1 },
      { repeat { rw [h_left, h_right] },
        exact and.intro (le_add_of_nonneg_right dec_trivial) (and.intro (by refl) (and.intro
          (by linarith) (lt_add_of_pos_right _ dec_trivial))) } },
    { split,
      { exact h1 },
      { repeat { rw [h_left, h_right] },
        exact and.intro (le_add_of_nonneg_right dec_trivial) (and.intro
          (le_add_of_nonneg_right dec_trivial) (and.intro (by linarith) (by linarith))) } } }
end

-- A subgrid of side 2 has number of black cells given by the
-- corresponding four cells.
theorem sub_black_2 (c : colouring) (a b : fin 2019)
    (ha : (a : ℕ) < 2018) (hb : (b : ℕ) < 2018) :
  sub_black c a b 2 =
    (c.filter (λ p : grid, p = (a, b))).card +
    (c.filter (λ p : grid, p = (a, fin.of_nat (b + 1)))).card +
    (c.filter (λ p : grid, p = (fin.of_nat (a + 1), b))).card +
    (c.filter (λ p : grid, p = (fin.of_nat (a + 1), fin.of_nat (b + 1)))).card :=
begin
  repeat { rw fin.coe_eq_val at * },
  have hao1 : a.val + 1 < nat.succ 2018,
  { rw nat.succ_eq_add_one, linarith },
  have hbo1 : b.val + 1 < nat.succ 2018,
  { rw nat.succ_eq_add_one, linarith },
  have hao2 : (a.val + 1) % (nat.succ 2018) = a.val + 1 := nat.mod_eq_of_lt hao1,
  have hbo2 : (b.val + 1) % (nat.succ 2018) = b.val + 1 := nat.mod_eq_of_lt hbo1,
  unfold sub_black,
  rw subcolouring_2 c a b ha hb,
  convert card_union_add_card_inter
    ((c.filter (λ p, p = (a, b))) ∪
     (c.filter (λ p, p = (a, fin.of_nat (b + 1)))) ∪
     (c.filter (λ p, p = (fin.of_nat (a + 1), b))))
    (c.filter (λ p : grid, p = (fin.of_nat (a + 1), fin.of_nat (b + 1)))),
  { conv
    begin
      to_lhs,
      rw ←nat.add_zero (card ((c.filter (λ p, p = (a, b))) ∪
           (c.filter (λ p, p = (a, fin.of_nat (b + 1)))) ∪
           (c.filter (λ p, p = (fin.of_nat (a + 1), b))) ∪
           (c.filter (λ p, p = (fin.of_nat (a + 1), fin.of_nat (b + 1))))))
    end,
    rw add_left_cancel_iff,
    symmetry,
    rw [card_eq_zero, ←filter_or, ←filter_or, ←filter_and],
    convert filter_false c,
    { ext,
      split,
      { intro h,
        cases h with h1 h2,
        repeat { rw h2 at h1 },
        repeat { rw prod.mk.inj_iff at h1 },
        repeat { unfold fin.of_nat at h1 },
        repeat { rw fin.eq_iff_veq at h1, unfold fin.val at h1 },
        repeat { rw fin.coe_eq_val at h1 },
        repeat { rw hao2 at h1 },
        repeat { rw hbo2 at h1 },
        repeat { cases h1 },
        { exact nat.succ_ne_self a.val h1_left },
        { exact nat.succ_ne_self a.val h1_left },
        { exact nat.succ_ne_self b.val h1_right } },
      { exact false.elim } },
    { exact classical.dec_pred _ } },
  { symmetry,
    convert card_union_add_card_inter
      ((c.filter (λ p, p = (a, b))) ∪
       (c.filter (λ p, p = (a, fin.of_nat (b + 1)))))
      (c.filter (λ p, p = (fin.of_nat (a + 1), b))),
    { conv
      begin
        to_lhs,
        rw ←nat.add_zero (card ((c.filter (λ p, p = (a, b))) ∪
             (c.filter (λ p, p = (a, fin.of_nat (b + 1)))) ∪
             (c.filter (λ p, p = (fin.of_nat (a + 1), b)))))
      end,
      rw add_left_cancel_iff,
      symmetry,
      rw [card_eq_zero, ←filter_or, ←filter_and],
      convert filter_false c,
      { ext,
        split,
        { intro h,
          cases h with h1 h2,
          repeat { rw h2 at h1 },
          repeat { rw prod.mk.inj_iff at h1 },
          repeat { unfold fin.of_nat at h1 },
          repeat { rw fin.eq_iff_veq at h1, unfold fin.val at h1 },
          repeat { rw fin.coe_eq_val at h1 },
          repeat { rw fin.eq_iff_veq at h1 },
          unfold fin.val at h1,
          repeat { rw hao2 at h1 },
          repeat { rw hbo2 at h1 },
          repeat { cases h1 },
          { exact nat.succ_ne_self a.val h1_left },
          { exact nat.succ_ne_self a.val h1_left } },
        { exact false.elim } },
      { exact classical.dec_pred _ } },
    { symmetry,
      convert card_union_add_card_inter
        (c.filter (λ p, p = (a, b)))
        (c.filter (λ p, p = (a, fin.of_nat (b + 1)))),
      conv
      begin
        to_lhs,
        rw ←nat.add_zero (card ((c.filter (λ p, p = (a, b))) ∪
             (c.filter (λ p, p = (a, fin.of_nat (b + 1))))))
      end,
      rw add_left_cancel_iff,
      symmetry,
      rw [card_eq_zero, ←filter_and],
      convert filter_false c,
      { ext,
        split,
        { intro h,
          cases h with h1 h2,
          rw [h2, prod.mk.inj_iff, fin.coe_eq_val] at h1,
          unfold fin.of_nat at h1,
          repeat { rw fin.eq_iff_veq at h1 },
          unfold fin.val at h1,
          rw hbo2 at h1,
          exact nat.succ_ne_self b.val h1.2 },
        { exact false.elim } },
      { exact classical.dec_pred _ } } }
end

-- For rewriting in the next theorem.
theorem cell_eq_eq (a : grid) : (λ p : grid, p = a) = eq a :=
begin
  ext,
  exact eq_comm
end

-- For rewriting in the next theorem.
theorem cell_card_eq (c : colouring) (a : grid) :
  (c.filter (λ p : grid, p = a)).card = (ite (a ∈ c) 1 0) :=
begin
  conv
  begin
    to_lhs,
    congr,
    congr,
    rw cell_eq_eq
  end,
  rw filter_eq,
  by_cases a ∈ c,
  all_goals { finish }
end

-- Two rows alternate in position b if and only if they alternate in
-- position b + 1.
theorem rows_alternate_two_cols (c : colouring) (hbal2 : balanced_k c 2) (a b : fin 2019)
    (ha : (a : ℕ) < 2018) (hb : (b : ℕ) < 2018) :
  ((a, b) ∈ c ↔ ¬ (fin.of_nat (a + 1), b) ∈ c) ↔
    ((a, fin.of_nat (b + 1)) ∈ c ↔ ¬ (fin.of_nat (a + 1), fin.of_nat (b + 1)) ∈ c) :=
begin
  have hbal2a := hbal2 a b (by linarith) (by linarith),
  rw [sub_balanced_2 c a b ha hb, sub_black_2 c a b ha hb, cell_card_eq, cell_card_eq,
      cell_card_eq, cell_card_eq] at hbal2a,
  by_cases h1 : (a, b) ∈ c; by_cases h2 : (a, fin.of_nat (b + 1)) ∈ c;
    by_cases h3 : (fin.of_nat (a + 1), b) ∈ c;
    by_cases h4 : (fin.of_nat (a + 1), fin.of_nat (b + 1)) ∈ c,
  { tauto },
  { simp only [h1, h2, h3, h4, if_true, if_false] at hbal2a, norm_num at hbal2a },
  { simp only [h1, h2, h3, h4, if_true, if_false] at hbal2a, norm_num at hbal2a },
  { tauto },
  { simp only [h1, h2, h3, h4, if_true, if_false] at hbal2a, norm_num at hbal2a },
  { tauto },
  { tauto },
  { simp only [h1, h2, h3, h4, if_true, if_false] at hbal2a, norm_num at hbal2a },
  { simp only [h1, h2, h3, h4, if_true, if_false] at hbal2a, norm_num at hbal2a },
  { tauto },
  { tauto },
  { simp only [h1, h2, h3, h4, if_true, if_false] at hbal2a, norm_num at hbal2a },
  { tauto },
  { simp only [h1, h2, h3, h4, if_true, if_false] at hbal2a, norm_num at hbal2a },
  { simp only [h1, h2, h3, h4, if_true, if_false] at hbal2a, norm_num at hbal2a },
  { tauto }
end

-- Two rows alternate in position b if and only if they alternate in
-- all later positions.  b2 is in ℕ for convenience of induction.
theorem rows_alternate_two_cols_later (c : colouring) (hbal2 : balanced_k c 2) (a b : fin 2019)
    (b2 : ℕ) (ha : (a : ℕ) < 2018) (hb2 : (b : ℕ) < b2) (hb2a : b2 < 2019):
  ((a, b) ∈ c ↔ ¬ (fin.of_nat (a + 1), b) ∈ c) ↔
    ((a, fin.of_nat b2) ∈ c ↔ ¬ (fin.of_nat (a + 1), fin.of_nat b2) ∈ c) :=
begin
  rw fin.coe_eq_val at *,
  induction b2 with m hm,
  { exfalso,
    exact nat.not_lt_zero b.val hb2 },
  { by_cases h : b.val < m,
    { rw nat.succ_eq_add_one at hb2a,
      have hmx := hm (by linarith) h,
      rw hmx,
      have hb2ax : ((fin.of_nat m : fin 2019) : ℕ) < 2018,
      { rw fin.coe_eq_val,
        unfold fin.of_nat fin.val,
        rw nat.succ_eq_add_one,
        exact lt_of_le_of_lt (nat.mod_le _ _) (show m < 2018, by linarith) },
      convert rows_alternate_two_cols c hbal2 a (fin.of_nat m) ha hb2ax,
      { rw fin.coe_eq_val,
        unfold fin.of_nat fin.val,
        rw nat.succ_eq_add_one,
        symmetry,
        apply nat.mod_eq_of_lt,
        linarith },
      { rw fin.coe_eq_val,
        unfold fin.of_nat fin.val,
        rw nat.succ_eq_add_one,
        symmetry,
        apply nat.mod_eq_of_lt,
        linarith } },
    { have hbv : b.val = m := nat.eq_of_lt_succ_of_not_lt hb2 h,
      have hbv2 : b = fin.of_nat m,
      { rw ← hbv,
        unfold fin.of_nat,
        rw fin.eq_iff_veq,
        unfold fin.val,
        rw nat.succ_eq_add_one,
        symmetry,
        apply nat.mod_eq_of_lt,
        linarith },
      have hb2ax : ((fin.of_nat m : fin 2019) : ℕ) < 2018,
      { rw fin.coe_eq_val,
        unfold fin.of_nat fin.val,
        rw nat.succ_eq_add_one,
        exact lt_of_le_of_lt (nat.mod_le _ _) (show m < 2018, by linarith) },
      convert rows_alternate_two_cols c hbal2 a (fin.of_nat m) ha hb2ax,
      { rw [←hbv2, ←hbv, fin.coe_eq_val] },
      { rw [←hbv2, ←hbv, fin.coe_eq_val] } } },
end

-- Likewise, but with b2 in fin 2019.
theorem rows_alternate_two_cols_later' (c : colouring) (hbal2 : balanced_k c 2) (a b : fin 2019)
    (b2 : fin 2019) (ha : (a : ℕ) < 2018) (hb2 : b < b2):
  ((a, b) ∈ c ↔ ¬ (fin.of_nat (a + 1), b) ∈ c) ↔
    ((a, b2) ∈ c ↔ ¬ (fin.of_nat (a + 1), b2) ∈ c) :=
begin
  have hb2b : b2 = (fin.of_nat (b2 : ℕ)),
  { rw fin.coe_eq_val,
    unfold fin.of_nat,
    rw fin.eq_iff_veq,
    unfold fin.val,
    rw nat.succ_eq_add_one,
    symmetry,
    apply nat.mod_eq_of_lt,
    exact b2.is_lt },
  convert rows_alternate_two_cols_later c hbal2 a b (b2 : ℕ) ha _ _,
  { norm_cast,
    exact hb2 },
  { rw [fin.coe_eq_val],
    exact b2.is_lt }
end

-- Two rows alternate in position b if and only if they alternate in
-- position b2.
theorem rows_alternate_any_two_cols (c : colouring) (hbal2 : balanced_k c 2) (a b b2 : fin 2019)
    (ha : (a : ℕ) < 2018) :
  ((a, b) ∈ c ↔ ¬ (fin.of_nat (a + 1), b) ∈ c) ↔
    ((a, b2) ∈ c ↔ ¬ (fin.of_nat (a + 1), b2) ∈ c) :=
begin
  cases lt_trichotomy b b2,
  { exact rows_alternate_two_cols_later' c hbal2 a b b2 ha h },
  { cases h,
   { rw h },
   { symmetry,
     exact rows_alternate_two_cols_later' c hbal2 a b2 b ha h } },
end

-- Likewise, expressed in terms of not alternating.
theorem rows_alternate_any_two_cols' (c : colouring) (hbal2 : balanced_k c 2) (a b b2 : fin 2019)
    (ha : (a : ℕ) < 2018) :
  ((a, b) ∈ c ↔ (fin.of_nat (a + 1), b) ∈ c) ↔
    ((a, b2) ∈ c ↔ (fin.of_nat (a + 1), b2) ∈ c) :=
begin
  rw [←not_iff_not, not_iff, not_iff_comm, not_iff],
  conv
  begin
    congr,
    rw iff.comm,
    skip,
    rw [not_iff_comm, iff.comm]
  end,
  exact rows_alternate_any_two_cols c hbal2 a b b2 ha
end

-- Two columns alternate in position b if and only if they alternate
-- in position b2.
theorem cols_alternate_any_two_rows (c : colouring) (hbal2 : balanced_k c 2) (a b b2 : fin 2019)
    (ha : (a : ℕ) < 2018) :
  ((b, a) ∈ c ↔ ¬ (b, fin.of_nat (a + 1)) ∈ c) ↔
    ((b2, a) ∈ c ↔ ¬ (b2, fin.of_nat (a + 1)) ∈ c) :=
begin
  convert rows_alternate_any_two_cols (transpose_colouring c) (transpose_balanced_k c 2 hbal2)
    a b b2 ha using 1,
  { rw [cell_in_transpose_iff, cell_not_in_transpose_iff] },
  { rw [cell_in_transpose_iff, cell_not_in_transpose_iff] }
end

-- If two rows fail to alternate in column b, columns b and b + 1
-- alternate in row a.
theorem rows_not_alternate_two_cols (c : colouring) (hbal2 : balanced_k c 2) (a b : fin 2019)
    (ha : (a : ℕ) < 2018) (hb : (b : ℕ) < 2018)
    (hnalt : (a, b) ∈ c ↔ (fin.of_nat (a + 1), b) ∈ c) :
  (a, b) ∈ c ↔ ¬ (a, fin.of_nat (b + 1)) ∈ c :=
begin
  revert hnalt,
  have hbal2a := hbal2 a b (by linarith) (by linarith),
  rw [sub_balanced_2 c a b ha hb, sub_black_2 c a b ha hb, cell_card_eq, cell_card_eq,
      cell_card_eq, cell_card_eq] at hbal2a,
  by_cases h1 : (a, b) ∈ c; by_cases h2 : (a, fin.of_nat (b + 1)) ∈ c;
    by_cases h3 : (fin.of_nat (a + 1), b) ∈ c;
    by_cases h4 : (fin.of_nat (a + 1), fin.of_nat (b + 1)) ∈ c,
  { simp only [h1, h2, h3, h4, if_true, if_false] at hbal2a, norm_num at hbal2a },
  { simp only [h1, h2, h3, h4, if_true, if_false] at hbal2a, norm_num at hbal2a },
  { tauto },
  { tauto },
  { tauto },
  { tauto },
  { tauto },
  { tauto },
  { tauto },
  { tauto },
  { tauto },
  { tauto },
  { tauto },
  { tauto },
  { simp only [h1, h2, h3, h4, if_true, if_false] at hbal2a, norm_num at hbal2a },
  { simp only [h1, h2, h3, h4, if_true, if_false] at hbal2a, norm_num at hbal2a }
end

-- If two rows fail to alternate in any column b, columns b1 and b1 +
-- 1 alternate in row a.
theorem rows_not_alternate_any_two_cols (c : colouring) (hbal2 : balanced_k c 2) (a b : fin 2019)
    (b1 : fin 2019) (ha : (a : ℕ) < 2018) (hb1 : (b1 : ℕ) < 2018)
    (hnalt : (a, b) ∈ c ↔ (fin.of_nat (a + 1), b) ∈ c) :
  (a, b1) ∈ c ↔ ¬ (a, fin.of_nat (b1 + 1)) ∈ c :=
begin
  refine rows_not_alternate_two_cols c hbal2 a b1 ha hb1 _,
  rw ←rows_alternate_any_two_cols' c hbal2 a b b1 ha,
  exact hnalt
end

-- If two rows fail to alternate in any column b, columns b1 and b1 +
-- 1 alternate everywhere.
theorem rows_not_alternate_any_two_cols_alt (c : colouring) (hbal2 : balanced_k c 2)
    (a b : fin 2019) (a1 b1 : fin 2019) (ha : (a : ℕ) < 2018) (hb1 : (b1 : ℕ) < 2018)
    (hnalt : (a, b) ∈ c ↔ (fin.of_nat (a + 1), b) ∈ c) :
  (a1, b1) ∈ c ↔ ¬ (a1, fin.of_nat (b1 + 1)) ∈ c :=
begin
  rw cols_alternate_any_two_rows c hbal2 b1 a1 a hb1,
  exact rows_not_alternate_any_two_cols c hbal2 a b b1 ha hb1 hnalt
end

-- Either all rows alternate, or all columns alternate.
theorem rows_alternate_or_cols_alternate (c : colouring) (hbal2 : balanced_k c 2) :
  rows_alternate c ∨ cols_alternate c :=
begin
  by_cases h : rows_alternate c,
  { left,
    exact h },
  { right,
    unfold rows_alternate at h,
    rw not_forall at h,
    cases h with a ha,
    rw not_forall at ha,
    cases ha with b hb,
    rw not_imp at hb,
    cases hb with ha hx,
    rw [iff.comm, not_iff, not_not, iff.comm] at hx,
    intros a1 b1 hb1,
    exact rows_not_alternate_any_two_cols_alt c hbal2 a b a1 b1 ha hb1 hx }
end

-- So dispose of one of the three parts of the sum for the result.
theorem result_no_r_no_c : card balanced_colourings_no_r_no_c = 0 :=
begin
  convert card_empty,
  unfold balanced_colourings_no_r_no_c balanced_colourings_no_r balanced_colourings,
  rw [filter_filter, filter_filter, eq_empty_iff_forall_not_mem],
  intro c,
  rw mem_filter,
  intro h,
  rcases h with ⟨hu, hb, hnr, hnc⟩,
  unfold not_rows_alternate at hnr,
  unfold not_cols_alternate at hnc,
  have hb2 := hb 2 (by norm_num) (by norm_num),
  have hor := rows_alternate_or_cols_alternate c hb2,
  tauto
end

-- Now we need only consider balanced colourings where rows alternate.
-- These can be expressed as a function of their first row, so we can
-- reduce to counting first rows with certain properties.

abbreviation row := fin 2019

abbreviation row_colouring := finset row

-- A row-alternating colouring of the grid as a function of the first
-- row.
def colouring_of_row_colouring (c : row_colouring) : colouring :=
finset.univ.filter (λ p : grid, p.2 ∈ c ↔ (p.1 : ℕ) % 2 = 0)

-- The first row of the grid.
def row_colouring_of_colouring (c : colouring) : row_colouring :=
finset.univ.filter (λ p : row, ((0 : fin (nat.succ 2018)), (p : fin 2019)) ∈ c)

-- A row-alternating colouring is given by its first row, induction.
theorem row_alternating_first_row (c : colouring) (h : rows_alternate c) (a : ℕ) (b : fin 2019)
    (ha : a < 2019) :
  (fin.of_nat a, b) ∈ c ↔ (((0 : fin (nat.succ 2018)), b) ∈ c ↔ a % 2 = 0) :=
begin
  induction a with k hk,
  { unfold fin.of_nat,
    norm_num,
    exact iff.rfl },
  { rw ←not_iff_not,
    rw nat.succ_eq_add_one at ha,
    have hf : ((fin.of_nat k : fin 2019) : ℕ) = k,
    { unfold fin.of_nat,
      rw fin.coe_eq_val,
      unfold fin.val,
      rw nat.succ_eq_add_one,
      rw nat.mod_eq_of_lt,
      linarith },
    have ha1 : ((fin.of_nat k : fin 2019) : ℕ) < 2018,
    { rw hf,
      linarith },
    have ha2 : nat.succ k = ((fin.of_nat k : fin 2019) : ℕ) + 1,
    { rw hf },
    have hkx := hk (by linarith),
    rw [ha2, ←h (fin.of_nat k) b ha1, hkx, hf, ←nat.even_iff, ←nat.even_iff, nat.even_add,
        nat.even_iff, nat.even_iff],
    norm_num,
    rw [←nat.not_even_iff, nat.even_iff],
    tauto }
end

-- A row-alternating colouring is given by its first row.
theorem row_alternating_first_row' (c : colouring) (h : rows_alternate c) :
  c = colouring_of_row_colouring (row_colouring_of_colouring c) :=
begin
  unfold colouring_of_row_colouring row_colouring_of_colouring,
  ext,
  split,
  { intro ha,
    rw [mem_filter, mem_filter],
    have hf : a = (fin.of_nat a.fst.val, a.snd),
    { ext,
      { unfold prod.fst fin.of_nat,
        rw fin.eq_iff_veq,
        unfold fin.val,
        rw nat.mod_eq_of_lt,
        exact a.fst.is_lt },
      { refl } },
    rw [hf, row_alternating_first_row c h a.fst.val a.snd a.fst.is_lt] at ha,
    rw ha,
    split,
    { exact mem_univ a },
    { rw fin.coe_eq_val,
      have hu : a.snd ∈ univ := mem_univ a.snd,
      rw ←iff_true (a.snd ∈ univ) at hu,
      rw hu,
      tauto } },
  { intro ha,
    rw [mem_filter, mem_filter] at ha,
    cases ha with hau ha,
    have hu : a.snd ∈ univ := mem_univ a.snd,
    rw ←iff_true (a.snd ∈ univ) at hu,
    rw [hu, true_and] at ha,
    have hf : a = (fin.of_nat a.fst.val, a.snd),
    { ext,
      { unfold prod.fst fin.of_nat,
        rw fin.eq_iff_veq,
        unfold fin.val,
        rw nat.mod_eq_of_lt,
        exact a.fst.is_lt },
      { refl } },
    rw [hf, row_alternating_first_row c h a.fst.val a.snd a.fst.is_lt],
    rw fin.coe_eq_val at ha,
    exact ha }
end

-- colouring_of_row_colouring produces a row-alternating colouring.
theorem colouring_of_row_colouring_rows_alternate (c : row_colouring) :
  rows_alternate (colouring_of_row_colouring c) :=
begin
  unfold colouring_of_row_colouring,
  -- Why is unfolding filter here needed for the second rewrite to
  -- work?
  unfold filter,
  intros a b ha,
  rw fin.coe_eq_val at ha,
  have halt : a.val + 1 < 2018 + 1 := add_lt_add_right ha 1,
  erw mem_filter,
  erw mem_filter,
  unfold prod.fst prod.snd,
  split,
  { intro h,
    cases h with hu heq,
    intro h2,
    cases h2 with h2u h2,
    unfold fin.of_nat at h2,
    rw fin.coe_eq_val at *,
    rw fin.coe_eq_val at h2,
    unfold fin.val at h2,
    rw nat.succ_eq_add_one at h2,
    rw nat.mod_eq_of_lt halt at h2,
    rw ←nat.even_iff at *,
    rw nat.even_add at h2,
    norm_num at h2,
    rw [iff_not_comm, iff.comm, ←not_iff] at h2,
    exact h2 heq },
  { intro h,
    rw not_and at h,
    have h2 := h (mem_univ _),
    split,
    { exact mem_univ _ },
    { unfold fin.of_nat at h2,
      rw fin.coe_eq_val at *,
      rw fin.coe_eq_val at h2,
      unfold fin.val at h2,
      rw nat.succ_eq_add_one at h2,
      rw nat.mod_eq_of_lt halt at h2,
      rw ←nat.even_iff at *,
      rw nat.even_add at h2,
      norm_num at h2,
      rw [not_iff, not_iff_not] at h2,
      exact h2 } }
end

-- TODO: rest of solution.

-- The remaining two parts of the sum for the result.

theorem result_r_c : card balanced_colourings_r_c = 2 :=
begin
  sorry
end

theorem result_r_no_c : card balanced_colourings_r_no_c = 2^1011 - 4 :=
begin
  sorry
end

-- The result of the problem.
theorem p3_result : finset.card balanced_colourings = 2^1012 - 6 :=
begin
  rw [card_split_3, result_r_c, result_no_r_no_c, result_r_no_c],
  norm_num
end
