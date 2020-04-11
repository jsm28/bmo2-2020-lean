-- BMO2 2020 problem 3.

import data.finset
import data.fintype.basic
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

-- A rectangular subgrid of the coloured grid.  (This definition
-- allows the rectangle to go off the edges, so separate hypotheses
-- are needed where that is undesirable.)  Although the problem only
-- refers to square subgrids, rectangular ones are useful in the
-- solution when counting black squares in colourings made from
-- alternating rows.
def subcolouring (c : colouring) (a b : fin 2019) (k1 k2 : ℕ) : finset grid :=
finset.filter (λ p : grid, a ≤ p.1 ∧ b ≤ p.2 ∧
                               (p.1 : ℕ) < (a : ℕ) + k1 ∧ (p.2 : ℕ) < (b : ℕ) + k2) c

-- The complement of a colouring.
def complement (c : colouring) : colouring := finset.univ \ c

-- The number of black cells in a subgrid.
def sub_black (c : colouring) (a b : fin 2019) (k1 k2 : ℕ) : ℕ :=
finset.card (subcolouring c a b k1 k2)

-- The number of white cells in a subgrid.
def sub_white (c : colouring) (a b : fin 2019) (k1 k2 : ℕ) : ℕ :=
finset.card (subcolouring (complement c) a b k1 k2)

-- The imbalance of a subgrid.
def sub_imbalance (c : colouring) (a b : fin 2019) (k : ℕ) : ℕ :=
int.nat_abs (((sub_black c a b k k) : ℤ) - ((sub_white c a b k k) : ℤ))

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

-- Some lemmas about fin 2019 that are of use below.

theorem of_nat_val (a : ℕ) (h : a < 2019) : ((fin.of_nat a) : fin 2019).val = a :=
nat.mod_eq_of_lt h

theorem of_nat_val_self (a : fin 2019) : ((fin.of_nat a.val) : fin 2019).val = a.val :=
of_nat_val a.val a.is_lt

theorem of_nat_eq_self (a : fin 2019) : fin.of_nat a.val = a :=
begin
  rw fin.eq_iff_veq,
  exact of_nat_val_self a
end

theorem of_nat_coe (a : ℕ) (h : a < 2019) : (((fin.of_nat a) : fin 2019) : ℕ) = a :=
nat.mod_eq_of_lt h

-- Adding the numbers of black and white cells in a subgrid.
theorem sub_black_add_sub_white (c : colouring) (a b : fin 2019) (k : ℕ)
    (ha : (a : ℕ) + k ≤ 2019) (hb : (b : ℕ) + k ≤ 2019) :
  sub_black c a b k k + sub_white c a b k k = k * k :=
begin
  unfold sub_black sub_white subcolouring complement,
  rw [←card_union_add_card_inter, ←filter_union, filter_inter, inter_filter,
      union_sdiff_of_subset (subset_univ _), inter_sdiff_self, filter_empty, filter_empty,
      card_empty, add_zero],
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
      { unfold prod.fst,
        cases k with kk,
        { exfalso,
          exact nat.not_lt_zero _ ha2 },
        { rw [add_comm ((p.fst.val - a.val) * nat.succ kk) (p.snd.val - b.val),
              nat.add_mul_div_right _ _ (nat.zero_lt_succ _), nat.div_eq_of_lt hb2, zero_add,
              ←nat.add_sub_assoc ha1, nat.add_sub_cancel_left],
          exact of_nat_val_self p.fst } },
      { unfold prod.snd,
        cases k with kk,
        { exfalso,
          exact nat.not_lt_zero _ ha2 },
        { rw [add_comm ((p.fst.val - a.val) * nat.succ kk) (p.snd.val - b.val),
              nat.add_mul_mod_self_right, nat.mod_eq_of_lt hb2, ←nat.add_sub_assoc hb1,
              nat.add_sub_cancel_left],
          exact of_nat_val_self p.snd } } } },
  { intros i hi,
    rw mem_filter,
    split,
    { exact mem_univ _ },
    { repeat { rw fin.le_def },
      repeat { rw fin.coe_eq_val at * },
      unfold prod.fst prod.snd fin.val,
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
        rw of_nat_val _ hax,
        exact nat.le_add_right _ _ },
      { have hbx : (b.val + i % k) < 2019, {linarith},
        rw of_nat_val _ hbx,
        exact nat.le_add_right _ _ },
      { have hax : (a.val + i / k) < 2019, {linarith},
        rw of_nat_val _ hax,
        linarith },
      { have hbx : (b.val + i % k) < 2019, {linarith},
        rw of_nat_val _ hbx,
        linarith } } },
  { intros i j hi hj heq,
    rw prod.mk.inj_iff at heq,
    cases heq with heq1 heq2,
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
    rw [fin.eq_iff_veq, of_nat_val _ hai, of_nat_val _ haj, add_left_cancel_iff] at heq1,
    rw [fin.eq_iff_veq, of_nat_val _ hbi, of_nat_val _ hbj, add_left_cancel_iff] at heq2,
    rw [←nat.mod_add_div i k, ←nat.mod_add_div j k, heq1, heq2] }
end

-- Number of black cells in a subgrid, inequality.
theorem sub_black_le (c : colouring) (a b : fin 2019) (k : ℕ)
    (ha : (a : ℕ) + k ≤ 2019) (hb : (b : ℕ) + k ≤ 2019) : sub_black c a b k k ≤ k * k :=
begin
  rw ← sub_black_add_sub_white c a b k ha hb,
  exact nat.le_add_right _ _,
end

-- Number of white cells in a subgrid, more convenient form.
theorem sub_white_eq (c : colouring) (a b : fin 2019) (k : ℕ)
    (ha : (a : ℕ) + k ≤ 2019) (hb : (b : ℕ) + k ≤ 2019) :
  sub_white c a b k k = k * k - sub_black c a b k k :=
begin
  symmetry,
  rw [nat.sub_eq_iff_eq_add (sub_black_le c a b k ha hb), add_comm],
  symmetry,
  exact sub_black_add_sub_white c a b k ha hb
end

-- Imbalance in terms only of number of black cells.
theorem imbalance_eq (c : colouring) (a b : fin 2019) (k : ℕ)
    (ha : (a : ℕ) + k ≤ 2019) (hb : (b : ℕ) + k ≤ 2019) :
  sub_imbalance c a b k = int.nat_abs (2 * ((sub_black c a b k k) : ℤ) - ((k * k) : ℤ)) :=
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
  transpose_colouring (subcolouring c a b k k) = subcolouring (transpose_colouring c) b a k k :=
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
  sub_black c a b k k = sub_black (transpose_colouring c) b a k k :=
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
  balanced (transpose_colouring c) :=
begin
  intros k hk1 hk2,
  exact transpose_balanced_k c k (h k hk1 hk2)
end

-- A colouring is balanced if and only if its transpose is.
theorem transpose_balanced_iff (c : colouring) :
  balanced c ↔ balanced (transpose_colouring c) :=
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
  sub_balanced c a b 2 ↔ sub_black c a b 2 2 = 2 :=
begin
  unfold sub_balanced,
  rw [imbalance_eq c a b 2 (by linarith) (by linarith),
      (show (2 : ℤ) = ((2 : ℕ) : ℤ), by norm_cast),
      ←mul_sub_left_distrib ((2 : ℕ) : ℤ) _ _, int.nat_abs_mul, mul_comm],
  norm_cast,
  rw ←nat.le_div_iff_mul_le _ _ (dec_trivial : 2 > 0),
  norm_num,
  rw sub_eq_zero_iff_eq,
  norm_cast
end

-- A subgrid of side 2 is made up of a given 4 cells.
theorem subcolouring_2 (c : colouring) (a b : fin 2019)
    (ha : (a : ℕ) < 2018) (hb : (b : ℕ) < 2018) :
  subcolouring c a b 2 2 = (c.filter (λ p, p = (a, b))) ∪
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
  have hao : fin.of_nat (a_val + 1) = ⟨a_val + 1, hao1⟩,
  { apply fin.eq_of_veq,
    unfold fin.val,
    exact of_nat_val _ (by linarith only [ha]) },
  have hbo : fin.of_nat (b_val + 1) = ⟨b_val + 1, hbo1⟩,
  { apply fin.eq_of_veq,
    unfold fin.val,
    exact of_nat_val _ (by linarith only [hb]) },
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
  sub_black c a b 2 2 =
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
    (b2 : ℕ) (ha : (a : ℕ) < 2018) (hb2 : (b : ℕ) < b2) (hb2a : b2 < 2019) :
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
      { rw of_nat_coe m (by linarith),
        linarith },
      convert rows_alternate_two_cols c hbal2 a (fin.of_nat m) ha hb2ax,
      { exact (of_nat_coe m (by linarith)).symm },
      { exact (of_nat_coe m (by linarith)).symm } },
    { have hbv : b.val = m := nat.eq_of_lt_succ_of_not_lt hb2 h,
      have hbv2 : b = fin.of_nat m,
      { rw ← hbv,
        exact (of_nat_eq_self b).symm },
      have hb2ax : ((fin.of_nat m : fin 2019) : ℕ) < 2018,
      { rw [fin.coe_eq_val, ←hbv, of_nat_val_self _, hbv],
        linarith },
      convert rows_alternate_two_cols c hbal2 a (fin.of_nat m) ha hb2ax,
      { rw [←hbv2, ←hbv, fin.coe_eq_val] },
      { rw [←hbv2, ←hbv, fin.coe_eq_val] } } },
end

-- Likewise, but with b2 in fin 2019.
theorem rows_alternate_two_cols_later' (c : colouring) (hbal2 : balanced_k c 2) (a b : fin 2019)
    (b2 : fin 2019) (ha : (a : ℕ) < 2018) (hb2 : b < b2) :
  ((a, b) ∈ c ↔ ¬ (fin.of_nat (a + 1), b) ∈ c) ↔
    ((a, b2) ∈ c ↔ ¬ (fin.of_nat (a + 1), b2) ∈ c) :=
begin
  have hb2b : b2 = (fin.of_nat (b2 : ℕ)) := (of_nat_eq_self b2).symm,
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

-- Thus the cardinality of the set of balanced colourings, in two parts.
theorem card_split_2 :
  card balanced_colourings = card balanced_colourings_r_c +
    2 * card balanced_colourings_r_no_c :=
begin
  rw [card_split_3, result_no_r_no_c, add_zero]
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
    have hf : ((fin.of_nat k : fin 2019) : ℕ) = k := of_nat_coe _ (by linarith only [ha]),
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
      { unfold prod.fst,
        exact (of_nat_val_self a.fst).symm },
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
      { unfold prod.fst,
        exact (of_nat_val_self a.fst).symm },
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
  have halt : (a : ℕ) + 1 < 2018 + 1 := add_lt_add_right ha 1,
  norm_num at halt,
  erw mem_filter,
  erw mem_filter,
  unfold prod.fst prod.snd,
  split,
  { intro h,
    cases h with hu heq,
    intro h2,
    cases h2 with h2u h2,
    rw of_nat_coe _ halt at h2,
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
    { rw of_nat_coe _ halt at h2,
      rw fin.coe_eq_val at *,
      rw ←nat.even_iff at *,
      rw nat.even_add at h2,
      norm_num at h2,
      rw [not_iff, not_iff_not] at h2,
      exact h2 } }
end

-- colouring_of_row_colouring is injective.
theorem colouring_of_row_colouring_injective : function.injective colouring_of_row_colouring :=
begin
  apply function.injective_of_has_left_inverse,
  use row_colouring_of_colouring,
  intro c,
  unfold colouring_of_row_colouring row_colouring_of_colouring,
  ext,
  erw [mem_filter, mem_filter],
  unfold prod.fst prod.snd,
  norm_num
end

-- Whether a row colouring gives a balanced colouring of the grid.
-- (This will later be proved equivalent to a more convenient form.)
def gives_balanced (c : row_colouring) : Prop :=
balanced (colouring_of_row_colouring c)

-- Row colourings with alternating columns.
def row_cols_alternate (c : row_colouring) : Prop :=
∀ (a : fin 2019) (h : (a : ℕ) < 2018), a ∈ c ↔ ¬ fin.of_nat (a + 1) ∈ c

-- Columns alternate in the whole grid if and only if they do in a
-- row.
theorem row_cols_alternate_iff_cols_alternate (c : row_colouring) :
  row_cols_alternate c ↔ cols_alternate (colouring_of_row_colouring c) :=
begin
  unfold row_cols_alternate cols_alternate,
  split,
  { intros h a b hb,
    have hb2 := h b hb,
    unfold colouring_of_row_colouring,
    erw [mem_filter, mem_filter],
    unfold prod.fst prod.snd,
    by_cases ha : (a : ℕ) % 2 = 0,
    { simpa [ha] },
    { rw [iff.comm, not_iff_comm] at hb2,
      simpa [ha] } },
  { intros h a ha,
    have ha2 := h (fin.of_nat 0) a ha,
    unfold colouring_of_row_colouring at ha2,
    erw [mem_filter, mem_filter] at ha2,
    unfold prod.fst prod.snd fin.of_nat at ha2,
    norm_num at ha2,
    exact ha2 }
end

-- Convert the split into cases to one based on gives_balanced.

def row_not_cols_alternate (c : row_colouring) : Prop :=
¬ row_cols_alternate c

def gives_balanced_colourings : finset row_colouring :=
finset.univ.filter gives_balanced

def gives_balanced_colourings_r_c : finset row_colouring :=
gives_balanced_colourings.filter row_cols_alternate

def gives_balanced_colourings_r_no_c : finset row_colouring :=
gives_balanced_colourings.filter row_not_cols_alternate

theorem card_r_c_eq_gives_rc :
  card balanced_colourings_r_c = card gives_balanced_colourings_r_c :=
begin
  convert card_image_of_injective gives_balanced_colourings_r_c
    colouring_of_row_colouring_injective,
  ext c,
  rw mem_image,
  split,
  { intro h,
    use row_colouring_of_colouring c,
    split,
    { unfold gives_balanced_colourings_r_c gives_balanced_colourings,
      rw [mem_filter, mem_filter],
      unfold gives_balanced,
      unfold balanced_colourings_r_c balanced_colourings_r balanced_colourings at h,
      rw [mem_filter, mem_filter, mem_filter] at h,
      rw row_cols_alternate_iff_cols_alternate,
      have hc : colouring_of_row_colouring (row_colouring_of_colouring c) = c,
      { symmetry,
        exact row_alternating_first_row' c h.1.2 },
      rw hc,
      exact and.intro (and.intro (mem_univ _) h.1.1.2) h.2 },
    { symmetry,
      apply row_alternating_first_row',
      unfold balanced_colourings_r_c balanced_colourings_r at h,
      rw [mem_filter, mem_filter] at h,
      exact h.1.2 } },
  { intro h,
    cases h with rc hrc,
    cases hrc with hrc hcrc,
    unfold gives_balanced_colourings_r_c gives_balanced_colourings at hrc,
    rw [mem_filter, mem_filter] at hrc,
    unfold gives_balanced at hrc,
    rw hcrc at hrc,
    unfold balanced_colourings_r_c balanced_colourings_r balanced_colourings,
    rw [mem_filter, mem_filter, mem_filter],
    repeat { split },
    { exact mem_univ _ },
    { exact hrc.1.2 },
    { rw ←hcrc,
      exact colouring_of_row_colouring_rows_alternate rc },
    { rw [←hcrc, ←row_cols_alternate_iff_cols_alternate rc],
      exact hrc.2 } }
end

theorem card_r_no_c_eq_gives_r_no_c :
  card balanced_colourings_r_no_c = card gives_balanced_colourings_r_no_c :=
begin
  convert card_image_of_injective gives_balanced_colourings_r_no_c
    colouring_of_row_colouring_injective,
  ext c,
  rw mem_image,
  split,
  { intro h,
    use row_colouring_of_colouring c,
    split,
    { unfold gives_balanced_colourings_r_no_c gives_balanced_colourings,
      rw [mem_filter, mem_filter],
      unfold gives_balanced,
      unfold balanced_colourings_r_no_c balanced_colourings_r balanced_colourings at h,
      rw [mem_filter, mem_filter, mem_filter] at h,
      unfold row_not_cols_alternate,
      rw row_cols_alternate_iff_cols_alternate,
      have hc : colouring_of_row_colouring (row_colouring_of_colouring c) = c,
      { symmetry,
        exact row_alternating_first_row' c h.1.2 },
      rw hc,
      exact and.intro (and.intro (mem_univ _) h.1.1.2) h.2 },
    { symmetry,
      apply row_alternating_first_row',
      unfold balanced_colourings_r_no_c balanced_colourings_r at h,
      rw [mem_filter, mem_filter] at h,
      exact h.1.2 } },
  { intro h,
    cases h with rc hrc,
    cases hrc with hrc hcrc,
    unfold gives_balanced_colourings_r_no_c gives_balanced_colourings at hrc,
    rw [mem_filter, mem_filter] at hrc,
    unfold gives_balanced at hrc,
    rw hcrc at hrc,
    unfold balanced_colourings_r_no_c balanced_colourings_r balanced_colourings,
    rw [mem_filter, mem_filter, mem_filter],
    repeat { split },
    { exact mem_univ _ },
    { exact hrc.1.2 },
    { rw ←hcrc,
      exact colouring_of_row_colouring_rows_alternate rc },
    { unfold not_cols_alternate,
      unfold row_not_cols_alternate at hrc,
      rw [←hcrc, ←row_cols_alternate_iff_cols_alternate rc],
      exact hrc.2 } }
end

-- Thus the cardinality of the set of balanced colourings, in two
-- parts based on gives_balanced.
theorem card_split_2_gives :
  card balanced_colourings = card gives_balanced_colourings_r_c +
    2 * card gives_balanced_colourings_r_no_c :=
begin
  rw [card_split_2, card_r_c_eq_gives_rc, card_r_no_c_eq_gives_r_no_c]
end

-- Next, show that the gives_balanced property is equivalent to a
-- balanced property for odd numbers of consecutive cells in the row,
-- so completing the reduction of the problem to be based on
-- properties of row colourings only.

-- The number of black cells in a subgrid equals the sum of the
-- numbers in a division of its rows into two parts.  (Note: the use
-- of fin 2019 for row numbers means this does not cover the case
-- where the first part of the split ends at the end of the grid.)
theorem sub_black_split_rows (c : colouring) (a b : fin 2019) (k1_1 k1_2 k2 : ℕ)
    (h : (a : ℕ) + k1_1 < 2019) :
  sub_black c a b (k1_1 + k1_2) k2 =
    sub_black c a b k1_1 k2 + sub_black c (fin.of_nat ((a : ℕ) + k1_1)) b k1_2 k2 :=
begin
  unfold sub_black,
  rw [←card_union_add_card_inter],
  symmetry,
  convert nat.add_zero (card (subcolouring c a b (k1_1 + k1_2) k2)),
  { unfold subcolouring,
    rw ←filter_or,
    ext x,
    rw [mem_filter, mem_filter],
    split,
    { intro hm,
      cases hm with hmc hm,
      cases hm,
      { rcases hm with ⟨ha1, hb1, ha2, hb2⟩,
        repeat { split },
        { exact hmc },
        { exact ha1 },
        { exact hb1 },
        { linarith },
        { exact hb2 } },
      { rcases hm with ⟨ha1, hb1, ha2, hb2⟩,
        repeat { split },
        { exact hmc },
        { rw fin.le_iff_val_le_val at ha1,
          rw [of_nat_val _ h, fin.coe_eq_val] at ha1,
          rw fin.le_iff_val_le_val,
          linarith },
        { exact hb1 },
        { convert ha2 using 1,
          rw [of_nat_coe _ h, add_assoc] },
        { exact hb2 } } },
    { intro hm,
      rcases hm with ⟨hmc, ha1, hb1, ha2, hb2⟩,
      split,
      { exact hmc },
      { by_cases hx : (x.fst : ℕ) < (a : ℕ) + k1_1,
        { left,
          exact and.intro ha1 (and.intro hb1 (and.intro hx hb2)) },
        { right,
          rw [fin.le_iff_val_le_val, of_nat_val _ h, of_nat_coe _ h],
          repeat { split },
          { exact not_lt.mp hx },
          { exact hb1 },
          { convert ha2 using 1,
            rw add_assoc },
          { exact hb2 } } } } },
  { convert card_empty,
    unfold subcolouring,
    rw ←filter_and,
    convert filter_false c,
    { ext,
      split,
      { intro hx,
        rcases hx with ⟨⟨ha1, hb1, ha2, hb2⟩, ⟨ha3, hb3, ha4, hb4⟩⟩,
        rw fin.le_iff_val_le_val at ha3,
        rw of_nat_val _ h at ha3,
        rw fin.coe_eq_val at ha2,
        linarith },
      { exact false.elim } },
    { exact classical.dec_pred _ } }
end

-- There are no black cells in zero rows.
theorem sub_black_zero_rows (c : colouring) (a b : fin 2019) (k2 : ℕ) :
  sub_black c a b 0 k2 = 0 :=
begin
  unfold sub_black,
  convert card_empty,
  unfold subcolouring,
  convert filter_false c,
  { ext,
    split,
    { intro h,
      rcases h with ⟨ha1, hb1, ha2, hb2⟩,
      rw [fin.coe_eq_val, fin.coe_eq_val] at ha2,
      rw fin.le_iff_val_le_val at ha1,
      linarith },
    { exact false.elim } },
  { exact classical.dec_pred _ }
end

-- A subgrid of a row colouring.
def row_subcolouring (c : row_colouring) (a : fin 2019) (k2 : ℕ) : finset row :=
c.filter (λ p : row, a ≤ p ∧ (p : ℕ) < (a : ℕ) + k2)

-- The complement of a row colouring.
def row_complement (c : row_colouring) : row_colouring :=
finset.univ \ c

-- The number of black cells in a subgrid of a row colouring.
def row_sub_black (c : row_colouring) (a : fin 2019) (k2 : ℕ) : ℕ :=
finset.card (row_subcolouring c a k2)

-- The number of black cells in a subgrid of a row colouring and its
-- complement.
theorem row_sub_black_add_complement (c : row_colouring) (a : fin 2019) (k2 : ℕ)
    (hk2 : (a : ℕ) + k2 ≤ 2019) :
  row_sub_black c a k2 + row_sub_black (row_complement c) a k2 = k2 :=
begin
  unfold row_sub_black row_complement row_subcolouring,
  rw [←card_union_add_card_inter, ←filter_union, filter_inter, inter_filter,
      union_sdiff_of_subset (subset_univ _), inter_sdiff_self, filter_empty, filter_empty,
      card_empty, add_zero],
  refine card_eq_of_bijective (λ i h, fin.of_nat (a + i)) _ _ _,
  { intro p,
    intro hp,
    rw mem_filter at hp,
    use p.val - a.val,
    rw fin.le_iff_val_le_val at hp,
    rw fin.coe_eq_val at *,
    rw fin.coe_eq_val at hp,
    rcases hp with ⟨hpu, hpa, hpa2⟩,
    split,
    { exact (nat.sub_lt_left_iff_lt_add hpa).mpr hpa2 },
    { rw nat.add_sub_of_le hpa,
      exact of_nat_eq_self p } },
  { intros i hi,
    rw mem_filter,
    have hai : (a : ℕ) + i < 2019, {linarith},
    rw [fin.le_iff_val_le_val, of_nat_val _ hai, of_nat_coe _ hai],
    repeat { split },
    { exact mem_univ _ },
    { rw fin.coe_eq_val,
      linarith },
    { linarith } },
  { intros i j hi hj,
    rw fin.coe_eq_val at *,
    rw fin.eq_iff_veq,
    have hai : a.val + i < 2019, {linarith},
    have haj : a.val + j < 2019, {linarith},
    rw [of_nat_val _ hai, of_nat_val _ haj],
    intro hij,
    exact nat.add_left_cancel hij }
end


-- The number of black cells in a subgrid of the complement of a row
-- colouring.
theorem row_sub_black_complement (c : row_colouring) (a : fin 2019) (k2 : ℕ)
    (hk2 : (a : ℕ) + k2 ≤ 2019) :
  row_sub_black (row_complement c) a k2 = k2 - row_sub_black c a k2 :=
begin
  conv
  begin
    to_rhs,
    congr,
    rw ←row_sub_black_add_complement c a k2 hk2
  end,
  rw nat.add_sub_cancel_left
end

-- The number of black cells in an even row, derived from a row colouring.
theorem sub_black_even_row (c : row_colouring) (a b : fin 2019) (k2 : ℕ)
    (ha : (a : ℕ) % 2 = 0) (hk2 : (b : ℕ) + k2 ≤ 2019) :
  sub_black (colouring_of_row_colouring c) a b 1 k2 = (row_sub_black c b k2) :=
begin
  set f : row -> grid := λ p, (a, p) with hf,
  have hfi : function.injective f,
  { intros p1 p2 h,
    rw hf at h,
    unfold at h,
    rw prod.mk.inj_iff at h,
    exact h.2 },
  unfold sub_black row_sub_black,
  convert card_image_of_injective (row_subcolouring c b k2) hfi,
  unfold subcolouring row_subcolouring,
  ext p,
  rw [mem_filter, mem_image],
  split,
  { intro h,
    rcases h with ⟨hp, ha1, hb1, ha2, hb2⟩,
    unfold colouring_of_row_colouring at hp,
    rw mem_filter at hp,
    use p.snd,
    rw hf,
    rw mem_filter,
    unfold,
    rw fin.coe_eq_val at *,
    rw fin.coe_eq_val at *,
    cases hp with hpu hp,
    rw fin.le_iff_val_le_val at ha1,
    have hap : p.fst.val = a.val,
    { linarith },
    repeat { split },
    { rw hap at hp,
      tauto },
    { exact hb1 },
    { exact hb2 },
    { ext,
      { unfold prod.fst,
        exact hap.symm },
      { unfold prod.snd } } },
  { intro h,
    cases h with rp hp,
    cases hp with hp hp2,
    rw mem_filter at hp,
    rw hf at hp2,
    unfold at hp2,
    rw ←hp2,
    unfold prod.fst prod.snd,
    repeat { split },
    { unfold colouring_of_row_colouring,
      rw mem_filter,
      unfold prod.fst prod.snd,
      split,
      { exact mem_univ _ },
      { tauto } },
    { refl },
    { exact hp.2.1 },
    { exact nat.lt_succ_self _ },
    { exact hp.2.2 } }
end

-- The number of black cells in an odd row, derived from a row colouring.
theorem sub_black_odd_row (c : row_colouring) (a b : fin 2019) (k2 : ℕ)
    (ha : (a : ℕ) % 2 ≠ 0) (hk2 : (b : ℕ) + k2 ≤ 2019) :
  sub_black (colouring_of_row_colouring c) a b 1 k2 = k2 - (row_sub_black c b k2) :=
begin
  set f : row -> grid := λ p, (a, p) with hf,
  have hfi : function.injective f,
  { intros p1 p2 h,
    rw hf at h,
    unfold at h,
    rw prod.mk.inj_iff at h,
    exact h.2 },
  rw ←row_sub_black_complement,
  unfold sub_black row_sub_black,
  convert card_image_of_injective (row_subcolouring (row_complement c) b k2) hfi,
  unfold subcolouring row_subcolouring row_complement,
  ext p,
  rw [mem_filter, mem_image],
  split,
  { intro h,
    rcases h with ⟨hp, ha1, hb1, ha2, hb2⟩,
    unfold colouring_of_row_colouring at hp,
    rw mem_filter at hp,
    use p.snd,
    rw hf,
    rw mem_filter,
    unfold,
    rw fin.coe_eq_val at *,
    rw fin.coe_eq_val at *,
    cases hp with hpu hp,
    rw fin.le_iff_val_le_val at ha1,
    have hap : p.fst.val = a.val,
    { linarith },
    rw mem_sdiff,
    repeat { split },
    { exact mem_univ _ },
    { rw hap at hp,
      tauto },
    { exact hb1 },
    { exact hb2 },
    { ext,
      { unfold prod.fst,
        exact hap.symm },
      { unfold prod.snd } } },
  { intro h,
    cases h with rp hp,
    cases hp with hp hp2,
    rw mem_filter at hp,
    rw hf at hp2,
    unfold at hp2,
    rw ←hp2,
    unfold prod.fst prod.snd,
    repeat { split },
    { unfold colouring_of_row_colouring,
      rw mem_filter,
      unfold prod.fst prod.snd,
      split,
      { exact mem_univ _ },
      { cases hp with hpc hp3,
        rw mem_sdiff at hpc,
        cases hpc with hpu hpc,
        tauto } },
    { refl },
    { exact hp.2.1 },
    { exact nat.lt_succ_self _ },
    { exact hp.2.2 } },
  { exact hk2 }
end

-- The number of black cells in one row, derived from a row colouring.
theorem sub_black_one_row (c : row_colouring) (a b : fin 2019) (k2 : ℕ)
    (hk2 : (b : ℕ) + k2 ≤ 2019) :
  sub_black (colouring_of_row_colouring c) a b 1 k2 =
    ite ((a : ℕ) % 2 = 0) (row_sub_black c b k2) (k2 - (row_sub_black c b k2)) :=
begin
  by_cases ha : (a : ℕ) % 2 = 0,
  { rw if_pos ha,
    exact sub_black_even_row c a b k2 ha hk2 },
  { rw if_neg ha,
    exact sub_black_odd_row c a b k2 ha hk2 },
end

-- The number of black cells in two rows, derived from a row colouring.
theorem sub_black_two_rows (c : row_colouring) (a b : fin 2019) (k2 : ℕ)
    (ha : (a : ℕ) < 2018) (hk2 : (b : ℕ) + k2 ≤ 2019) :
  sub_black (colouring_of_row_colouring c) a b 2 k2 = k2 :=
begin
  rw sub_black_split_rows (colouring_of_row_colouring c) a b 1 1 k2
     (show (a : ℕ) + 1 < 2019, by linarith),
  have hf : ((fin.of_nat ((a : ℕ) + 1) : fin 2019) : ℕ) = (a : ℕ) + 1,
  { repeat { rw fin.coe_eq_val },
    rw fin.coe_eq_val at ha,
    exact of_nat_val _ (by linarith) },
  have hle : row_sub_black c b k2 ≤ k2 := nat.le.intro (row_sub_black_add_complement c b k2 hk2),
  by_cases ha2 : (a : ℕ) % 2 = 0,
  { rw sub_black_even_row c a b k2 ha2 hk2,
    have ha1 : ((fin.of_nat ((a : ℕ) + 1) : fin 2019) : ℕ) % 2 ≠ 0,
    { rw hf,
      intro ha3,
      rw ←nat.even_iff at *,
      rw nat.even_add at ha3,
      norm_num at ha3,
      exact ha3 ha2 },
    rw sub_black_odd_row c (fin.of_nat ((a : ℕ) + 1)) b k2 ha1 hk2,
    apply nat.add_sub_cancel',
    exact hle },
  { rw sub_black_odd_row c a b k2 ha2 hk2,
    have ha1 : ((fin.of_nat ((a : ℕ) + 1) : fin 2019) : ℕ) % 2 = 0,
    { rw hf,
      rw ←nat.even_iff at *,
      rw nat.even_add,
      norm_num,
      exact ha2 },
    rw sub_black_even_row c (fin.of_nat ((a : ℕ) + 1)) b k2 ha1 hk2,
    apply nat.sub_add_cancel,
    exact hle },
end

-- The number of black cells in an even number of rows, derived from a
-- row colouring.
theorem sub_black_even_rows (c : row_colouring) (a b : fin 2019) (k1 k2 : ℕ)
    (h : (a : ℕ) + (2 * k1) ≤ 2019) (hk2 : (b : ℕ) + k2 ≤ 2019) :
  sub_black (colouring_of_row_colouring c) a b (2 * k1) k2 = k1 * k2 :=
begin
  induction k1 with k1a hk1a,
  { rw [mul_zero, zero_mul],
    exact sub_black_zero_rows _ _ _ _ },
  { convert sub_black_split_rows (colouring_of_row_colouring c) a b (2 * k1a) 2 k2 _,
    { rw nat.succ_eq_add_one at h,
      rw [nat.succ_eq_add_one, hk1a (by linarith), add_mul, one_mul, add_left_cancel_iff],
      symmetry,
      refine sub_black_two_rows c _ b k2 _ hk2,
      have ha : ((a : ℕ) + 2 * k1a) < 2019, {linarith},
      rw of_nat_coe _ ha,
      linarith },
    { rw nat.succ_eq_add_one at h,
      linarith } }
end

-- The number of black cells in an odd number of rows, derived from a
-- row colouring.
theorem sub_black_odd_rows (c : row_colouring) (a b : fin 2019) (k1 k2 : ℕ)
    (h : (a : ℕ) + (2 * k1 + 1) ≤ 2019) (hk2 : (b : ℕ) + k2 ≤ 2019) :
  sub_black (colouring_of_row_colouring c) a b (2 * k1 + 1) k2 =
    (ite ((a : ℕ) % 2 = 0) (row_sub_black c b k2) (k2 - (row_sub_black c b k2))) + k1 * k2 :=
begin
  by_cases ha : (a : ℕ) + 1 < 2019,
  { convert sub_black_split_rows (colouring_of_row_colouring c) a b 1 (2 * k1) k2 _ using 1,
    { congr' 1,
      ring },
    { rw ←sub_black_one_row c a b k2 hk2,
      rw sub_black_even_rows c _ b k1 k2 _ hk2,
      rw of_nat_coe _ ha,
      linarith },
    { linarith } },
  { have hk1 : k1 = 0, {linarith},
    have ha2 : (a : ℕ) = 2018, {linarith},
    rw [hk1, ha2],
    norm_num,
    rw [sub_black_one_row _ _ _ _ hk2, ha2],
    norm_num }
end

-- colouring_of_row_colouring gives colourings balanced for subgrids
-- of even side.
theorem gives_balanced_even (c : row_colouring) (k : ℕ) :
  balanced_k (colouring_of_row_colouring c) (2 * k) :=
begin
  intros a b ha hb,
  unfold sub_balanced,
  rw imbalance_eq _ _ _ _ ha hb,
  rw sub_black_even_rows _ _ _ _ _ ha hb,
  norm_cast,
  ring,
  rw sub_self,
  norm_num
end

-- The imbalance of an odd subgrid of a row.
def row_odd_imbalance (c : row_colouring) (a : fin 2019) (k : ℕ)
    (ha : (a : ℕ) + (2 * k + 1) ≤ 2019) : ℕ :=
int.nat_abs (2 * ((row_sub_black c a (2 * k + 1)) : ℤ) - ((2 * k + 1) : ℤ))

-- Whether odd subgrids of a row are balanced.
def row_odd_balanced_k (c : row_colouring) (k : ℕ) : Prop :=
∀ (a : fin 2019) (ha : ((a : ℕ) + (2 * k + 1)) ≤ 2019), row_odd_imbalance c a k ha ≤ 1

-- The imbalance of a square subgrid of odd side equals the
-- corresponding imbalance for a row.
theorem imbalance_odd_eq (c : row_colouring) (a b : fin 2019) (k : ℕ)
    (ha : (a : ℕ) + (2 * k + 1) ≤ 2019) (hb : (b : ℕ) + (2 * k + 1) ≤ 2019) :
  sub_imbalance (colouring_of_row_colouring c) a b (2 * k + 1) = row_odd_imbalance c b k hb :=
begin
  rw [imbalance_eq _ _ _ _ ha hb, sub_black_odd_rows _ _ _ _ _ ha hb],
  unfold row_odd_imbalance,
  by_cases hae : ((a : ℕ) % 2 = 0),
  { rw if_pos hae,
    congr' 1,
    push_cast,
    ring,
    norm_cast,
    norm_num },
  { rw if_neg hae,
    rw ←int.nat_abs_neg,
    have hcoe : (((2 * k + 1 : ℕ) - row_sub_black c b (2 * k + 1) : ℕ) : ℤ) =
      ((2 * k + 1) : ℤ) - (row_sub_black c b (2 * k + 1) : ℤ),
    { norm_cast,
      apply int.coe_nat_sub,
      exact nat.le.intro (row_sub_black_add_complement _ _ _ hb) },
    have hcoe2 : (((2 * k + 1 : ℕ) - row_sub_black c b (2 * k + 1)  + k * (2 * k + 1) : ℕ) : ℤ) =
      ((2 * k + 1) : ℤ) - (row_sub_black c b (2 * k + 1) : ℤ) + (k * (2 * k + 1) : ℤ),
    { rw int.coe_nat_add,
      rw hcoe,
      norm_cast },
    rw hcoe2,
    congr' 1,
    push_cast,
    ring,
    norm_cast,
    norm_num,
    norm_cast,
    ring }
end

-- colouring_of_row_colouring gives colourings balanced for subgrids
-- of odd side if and only if their row_odd_imbalance is at most 1.
theorem gives_balanced_odd_iff (c : row_colouring) (k : ℕ) :
  balanced_k (colouring_of_row_colouring c) (2 * k + 1) ↔ row_odd_balanced_k c k :=
begin
  unfold balanced_k row_odd_balanced_k sub_balanced,
  split,
  { intros h a ha,
    rw ← imbalance_odd_eq _ _ _ _ ha ha,
    exact h a a ha ha },
  { intros h a b ha hb,
    rw imbalance_odd_eq _ _ _ _ ha hb,
    exact h b hb }
end

-- Whether a row colouring gives a balanced colouring of the grid,
-- without referring to the full grid at all.
def row_balanced (c : row_colouring) : Prop :=
∀ k : ℕ, k ≤ 1009 → row_odd_balanced_k c k

-- A row is gives_balanced if and only if it is row_balanced.
theorem gives_balanced_iff_row_balanced (c : row_colouring) :
  gives_balanced c ↔ row_balanced c :=
begin
  unfold gives_balanced row_balanced balanced,
  split,
  { intros h k hk,
    rw ← gives_balanced_odd_iff,
    exact h (2 * k + 1) (by linarith) (by linarith) },
  { intros h k hk1 hk2,
    by_cases he : k % 2 = 0,
    { convert gives_balanced_even c (k / 2),
      symmetry,
      exact nat.mul_div_cancel' (nat.dvd_of_mod_eq_zero he) },
    { rw [←nat.even_iff, nat.not_even_iff] at he,
      have he2 : 2 * (k / 2) + 1 = k,
      { rw add_comm,
        convert nat.mod_add_div k 2,
        exact he.symm },
      rw [←he2, gives_balanced_odd_iff _ _],
      exact h (k / 2) (by linarith) } }
end

-- So now rewrite the split in terms of row_balanced.

def row_balanced_colourings : finset row_colouring :=
finset.univ.filter row_balanced

theorem gives_balanced_eq_row_balanced : gives_balanced_colourings = row_balanced_colourings :=
begin
  unfold gives_balanced_colourings row_balanced_colourings,
  ext,
  rw [mem_filter, mem_filter],
  rw gives_balanced_iff_row_balanced
end

def row_balanced_colourings_r_c : finset row_colouring :=
row_balanced_colourings.filter row_cols_alternate

def row_balanced_colourings_r_no_c : finset row_colouring :=
row_balanced_colourings.filter row_not_cols_alternate

theorem card_gives_balanced_r_c_eq :
  card gives_balanced_colourings_r_c = card row_balanced_colourings_r_c :=
begin
  unfold gives_balanced_colourings_r_c row_balanced_colourings_r_c,
  rw gives_balanced_eq_row_balanced
end

theorem card_gives_balanced_r_no_c_eq :
  card gives_balanced_colourings_r_no_c = card row_balanced_colourings_r_no_c :=
begin
  unfold gives_balanced_colourings_r_no_c row_balanced_colourings_r_no_c,
  rw gives_balanced_eq_row_balanced
end

-- Thus the cardinality of the set of balanced colourings, in two
-- parts based on row_balanced.
theorem card_split_2_row :
  card balanced_colourings = card row_balanced_colourings_r_c +
    2 * card row_balanced_colourings_r_no_c :=
begin
  rw [card_split_2_gives, card_gives_balanced_r_c_eq, card_gives_balanced_r_no_c_eq]
end

-- The next aim is to prove that a row colouring is row_balanced if
-- and only if the positions (between two cells) where the colour does
-- *not* change all have the same parity.

-- The number of black cells in columns of a row, split into two
-- parts.
theorem row_sub_black_split_cols (c : row_colouring) (a : fin 2019) (k2_1 k2_2 : ℕ)
    (h : (a : ℕ) + k2_1 < 2019) :
  row_sub_black c a (k2_1 + k2_2) =
    row_sub_black c a k2_1 + row_sub_black c (fin.of_nat ((a : ℕ) + k2_1)) k2_2 :=
begin
  unfold row_sub_black,
  rw ←card_union_add_card_inter,
  symmetry,
  convert nat.add_zero (card (row_subcolouring c a (k2_1 + k2_2))),
  { unfold row_subcolouring,
    rw ←filter_or,
    ext x,
    rw [mem_filter, mem_filter],
    split,
    { intro hm,
      cases hm with hmc hm,
      cases hm,
      { repeat { split },
        { exact hmc },
        { exact hm.1 },
        { linarith } },
      { repeat { split },
        { exact hmc },
        { cases hm with hm1 hm2,
          rw [fin.le_iff_val_le_val, of_nat_val _ h, fin.coe_eq_val] at hm1,
          rw fin.le_iff_val_le_val,
          linarith },
        { cases hm with hm1 hm2,
          rw [of_nat_coe _ h, add_assoc] at hm2,
          exact hm2 } } },
    { intro hm,
      rcases hm with ⟨hmc, ha1, ha2⟩,
      split,
      { exact hmc },
      { by_cases hx : (x : ℕ) < (a : ℕ) + k2_1,
        { left,
          exact and.intro ha1 hx },
        { right,
          rw not_lt at hx,
          split,
          { rw [fin.le_iff_val_le_val, of_nat_val _ h, fin.coe_eq_val],
            rw [fin.coe_eq_val, fin.coe_eq_val] at hx,
            exact hx },
          { convert ha2 using 1,
            rw [of_nat_coe _ h, add_assoc] } } } } },
  { convert card_empty,
    unfold row_subcolouring,
    rw ←filter_and,
    convert filter_false c,
    { ext,
      split,
      { intro hx,
        rcases hx with ⟨⟨ha1, ha2⟩, ha3, ha4⟩,
        rw fin.le_iff_val_le_val at ha1,
        rw fin.coe_eq_val at *,
        rw fin.coe_eq_val at *,
        rw [fin.le_iff_val_le_val, of_nat_val _ h] at ha3,
        linarith },
      { exact false.elim } },
    { exact classical.dec_pred _ } }
end

-- There are no black cells in zero columns.
theorem row_sub_black_zero_cols (c : row_colouring) (a : fin 2019) : row_sub_black c a 0 = 0 :=
begin
  unfold row_sub_black,
  convert card_empty,
  unfold row_subcolouring,
  convert filter_false c,
  { ext,
    split,
    { intro h,
      cases h with h1 h2,
      rw fin.le_iff_val_le_val at h1,
      rw [fin.coe_eq_val, fin.coe_eq_val] at h2,
      linarith },
    { exact false.elim } },
  { exact classical.dec_pred _ }
end

-- The number of black cells in one column.
theorem row_sub_black_one_col (c : row_colouring) (a : fin 2019) :
  row_sub_black c a 1 = ite (a ∈ c) 1 0 :=
begin
  unfold row_sub_black,
  by_cases h : a ∈ c,
  { rw if_pos h,
    convert card_singleton a,
    unfold row_subcolouring,
    ext x,
    rw [mem_filter, mem_singleton],
    split,
    { intro hx,
      rcases hx with ⟨hxc, hxa1, hxa2⟩,
      rw fin.le_iff_val_le_val at hxa1,
      rw [fin.coe_eq_val, fin.coe_eq_val] at hxa2,
      have hxa : x.val = a.val, {linarith},
      rw ←fin.eq_iff_veq at hxa,
      exact hxa },
    { intro hx,
      rw hx,
      exact and.intro h (and.intro (by refl) (by linarith)) } },
  { rw if_neg h,
    convert card_empty,
    unfold row_subcolouring,
    ext x,
    rw mem_filter,
    split,
    { intro hx,
      rcases hx with ⟨hxc, hxa1, hxa2⟩,
      rw fin.le_iff_val_le_val at hxa1,
      rw [fin.coe_eq_val, fin.coe_eq_val] at hxa2,
      have hxa : x.val = a.val, {linarith},
      rw ←fin.eq_iff_veq at hxa,
      rw hxa at hxc,
      contradiction },
    { exact false.elim } }
end

-- The colour of individual cells in columns of a row that alternate
-- in colour.
theorem row_cols_alternate_colour (c : row_colouring) (a : fin 2019) (k2 : ℕ)
    (hk2 : (a : ℕ) + k2 ≤ 2019)
    (halt : ∀ k : ℕ, k + 1 < k2 → (fin.of_nat (a + k) ∈ c ↔ ¬ fin.of_nat (a + k + 1) ∈ c)) :
  ∀ k : ℕ, k < k2 → (fin.of_nat (a + k) ∈ c ↔ (a ∈ c ↔ k % 2 = 0)) :=
begin
  intros k,
  induction k with x hx,
  { intro h0,
    rw [add_zero, fin.coe_eq_val, of_nat_eq_self],
    simp },
  { intro hx2,
    rw nat.succ_eq_add_one at hx2,
    have hx3 : x < k2, {linarith},
    have hx4 := hx hx3,
    have hax := halt x hx2,
    conv
    begin
      congr,
      congr,
      congr,
      rw [nat.succ_eq_add_one, ←add_assoc],
    end,
    rw [←nat.even_iff, nat.even_succ, nat.even_iff],
    tauto }
end

-- The number of black cells in columns of a row that alternate in
-- colour.
theorem row_sub_black_cols_alternate (c : row_colouring) (a : fin 2019) (k2 : ℕ)
    (hk2 : (a : ℕ) + k2 ≤ 2019)
    (halt : ∀ k : ℕ, k + 1 < k2 → (fin.of_nat (a + k) ∈ c ↔ ¬ fin.of_nat (a + k + 1) ∈ c)) :
  row_sub_black c a k2 = ite (a ∈ c) ((k2 + 1) / 2) (k2 / 2) :=
begin
  induction k2 with x hx,
  { norm_num,
    exact row_sub_black_zero_cols c a },
  { conv
    begin
      to_lhs,
      rw nat.succ_eq_add_one
    end,
    rw [row_sub_black_split_cols c a x 1 hk2, row_sub_black_one_col _ _],
    rw hx _ _,
    { conv
      begin
        to_lhs,
        congr,
        skip,
        congr,
        rw row_cols_alternate_colour c a (nat.succ x) hk2 halt x (nat.lt_succ_self x)
      end,
      conv
      begin
        to_rhs,
        rw nat.succ_eq_add_one x,
      end,
      by_cases h : a ∈ c; by_cases he : nat.even x,
      { conv
        begin
          to_lhs,
          congr,
          skip,
          congr,
          rw ←nat.even_iff
        end,
        rw [if_pos h, if_pos h],
        conv
        begin
          to_lhs,
          congr,
          skip,
          congr,
          rw iff_true_intro (iff_of_true h he),
        end,
        rw if_true,
        rw nat.even_iff at he,
        rw [←nat.mod_add_div x 2, he, zero_add, add_assoc],
        conv
        begin
          to_lhs,
          congr,
          congr,
          rw add_comm
        end,
        rw nat.add_mul_div_left _ _ (dec_trivial : 2 > 0),
        conv
        begin
          to_rhs,
          rw add_comm
        end,
        rw nat.add_mul_div_left _ _ (dec_trivial : 2 > 0),
        norm_num,
        exact add_comm _ _ },
      { conv
        begin
          to_lhs,
          congr,
          skip,
          congr,
          rw ←nat.even_iff
        end,
        rw [if_pos h, if_pos h],
        have hn: ¬ (a ∈ c ↔ nat.even x), {tauto},
        conv
        begin
          to_lhs,
          congr,
          skip,
          congr,
          rw iff_false_intro hn,
        end,
        rw if_false,
        rw nat.not_even_iff at he,
        rw [←nat.mod_add_div x 2, he, add_zero],
        conv
        begin
          to_lhs,
          rw [add_comm, ←add_assoc, nat.add_mul_div_left _ _ (dec_trivial : 2 > 0)]
        end,
        rw [(show 1 + 2 * (x / 2) + 1 + 1 = 3 + 2 * (x / 2), by ring),
            nat.add_mul_div_left _ _ (dec_trivial : 2 > 0)],
        norm_num },
      { conv
        begin
          to_lhs,
          congr,
          skip,
          congr,
          rw ←nat.even_iff
        end,
        rw [if_neg h, if_neg h],
        have hn: ¬ (a ∈ c ↔ nat.even x), {tauto},
        conv
        begin
          to_lhs,
          congr,
          skip,
          congr,
          rw iff_false_intro hn,
        end,
        rw if_false,
        rw nat.even_iff at he,
        rw [←nat.mod_add_div x 2, he, add_zero, zero_add,
            nat.mul_div_cancel_left _ (dec_trivial : 2 > 0), add_comm,
            nat.add_mul_div_left _ _ (dec_trivial : 2 > 0)],
        norm_num },
      { conv
        begin
          to_lhs,
          congr,
          skip,
          congr,
          rw ←nat.even_iff
        end,
        rw [if_neg h, if_neg h],
        have hn: (a ∈ c ↔ nat.even x), {tauto},
        conv
        begin
          to_lhs,
          congr,
          skip,
          congr,
          rw iff_true_intro hn,
        end,
        rw if_true,
        rw nat.not_even_iff at he,
        rw [←nat.mod_add_div x 2, he, add_zero, nat.add_mul_div_left _ _ (dec_trivial : 2 > 0)],
        conv
        begin
          to_rhs,
          rw add_assoc,
          congr,
          congr,
          skip,
          rw add_comm,
        end,
        rw [←add_assoc, nat.add_mul_div_left _ _ (dec_trivial : 2 > 0)],
        norm_num,
        exact add_comm _ _ } },
    { rw nat.succ_eq_add_one at hk2,
      linarith },
    { intros k hk,
      have hks : k + 1 < nat.succ x,
      { rw nat.succ_eq_add_one,
        linarith },
      exact halt k hks } }
end

-- The number of black cells in an even number of columns of a row,
-- where each pair alternate in colour.
theorem row_sub_black_even_cols_alternate (c : row_colouring) (a : fin 2019) (k2 : ℕ)
    (hk2 : (a : ℕ) + 2 * k2 ≤ 2019)
    (halt : ∀ k : ℕ, k < k2 → (fin.of_nat (a + 2 * k) ∈ c ↔ ¬ fin.of_nat (a + 2 * k + 1) ∈ c)) :
  row_sub_black c a (2 * k2) = k2 :=
begin
  induction k2 with k2x hk2x,
  { norm_num,
    exact row_sub_black_zero_cols c a },
  { rw [nat.succ_eq_add_one, nat.left_distrib],
    norm_num,
    rw [nat.succ_eq_add_one, nat.left_distrib] at hk2,
    have ha : (a : ℕ) + 2 * k2x < 2019, {linarith},
    rw row_sub_black_split_cols _ _ _ _ ha,
    { congr,
      { apply hk2x,
        { exact le_of_lt ha },
        { intros k hk,
          have hks : k < nat.succ k2x, { exact nat.lt.step hk },
          exact halt k hks } },
      { convert row_sub_black_cols_alternate c (fin.of_nat ((a : ℕ) + 2 * k2x)) 2 _ _,
        { norm_num },
        { rw of_nat_coe _ ha,
          norm_num at hk2,
          rw add_assoc,
          exact hk2 },
        { intros k hk,
          rw of_nat_coe _ ha,
          have hk0 : k = 0, {linarith},
          rw [hk0, add_zero],
          apply halt,
          exact nat.lt_succ_self k2x } } } }
end

-- The number of black cells in an odd number of columns of a row,
-- where pairs in even positions (relative to the starting point of
-- those columns) alternate in colour.
theorem row_sub_black_odd_cols_alternate_0 (c : row_colouring) (a : fin 2019) (k2 : ℕ)
    (hk2 : (a : ℕ) + 2 * k2 + 1 ≤ 2019)
    (halt : ∀ k : ℕ, k < k2 → (fin.of_nat (a + 2 * k) ∈ c ↔ ¬ fin.of_nat (a + 2 * k + 1) ∈ c)) :
  row_sub_black c a (2 * k2 + 1) = ite (fin.of_nat (a + 2 * k2) ∈ c) (k2 + 1) k2 :=
begin
  rw [row_sub_black_split_cols _ _ _ _ hk2, row_sub_black_one_col],
  have hk2a : (a : ℕ) + 2 * k2 ≤ 2019, {linarith},
  rw row_sub_black_even_cols_alternate _ _ _ hk2a halt,
  by_cases h : fin.of_nat (a + 2 * k2) ∈ c,
  { rw [if_pos h, if_pos h] },
  { rw [if_neg h, if_neg h, add_zero] }
end

-- Thus, the odd imbalance in that case.
theorem row_odd_imbalance_cols_alternate_0 (c : row_colouring) (a : fin 2019) (k2 : ℕ)
    (hk2 : (a : ℕ) + 2 * k2 + 1 ≤ 2019)
    (halt : ∀ k : ℕ, k < k2 → (fin.of_nat (a + 2 * k) ∈ c ↔ ¬ fin.of_nat (a + 2 * k + 1) ∈ c)) :
  row_odd_imbalance c a k2 hk2 = 1 :=
begin
  unfold row_odd_imbalance,
  rw row_sub_black_odd_cols_alternate_0 c a k2 hk2 halt,
  by_cases h : fin.of_nat (a + 2 * k2) ∈ c,
  { rw if_pos h,
    push_cast,
    ring },
  { rw if_neg h,
    ring }
end

-- The number of black cells in an odd number of columns of a row,
-- where pairs in odd positions (relative to the starting point of
-- those columns) alternate in colour.
theorem row_sub_black_odd_cols_alternate_1 (c : row_colouring) (a : fin 2019) (k2 : ℕ)
    (hk2 : (a : ℕ) + 2 * k2 + 1 ≤ 2019)
    (halt : ∀ k : ℕ, k < k2 → (fin.of_nat (a + 1 + 2 * k) ∈ c ↔
                                ¬ fin.of_nat (a + 1 + 2 * k + 1) ∈ c)) :
  row_sub_black c a (2 * k2 + 1) = ite (a ∈ c) (k2 + 1) k2 :=
begin
  rw add_comm,
  by_cases h0 : k2 = 0,
  { rw h0,
    norm_num,
    exact row_sub_black_one_col _ _ },
  { have hk2pos : 0 < k2 := nat.pos_of_ne_zero h0,
    have hk2a : (a : ℕ) + 1 < 2019, {linarith},
    rw [row_sub_black_split_cols _ _ _ _ hk2a, row_sub_black_one_col],
    rw [add_assoc, add_comm (2 * k2) 1, ←add_assoc, ←of_nat_coe ((a : ℕ) + 1) hk2a] at hk2,
    rw row_sub_black_even_cols_alternate _ _ _ hk2 _,
    { by_cases h : a ∈ c,
      { rw [if_pos h, if_pos h],
        exact add_comm _ _ },
      { rw [if_neg h, if_neg h, zero_add] }  },
    { intros k hk,
      rw of_nat_coe _ hk2a,
      exact halt k hk } }
end

-- Thus, the odd imbalance in that case.
theorem row_odd_imbalance_cols_alternate_1 (c : row_colouring) (a : fin 2019) (k2 : ℕ)
    (hk2 : (a : ℕ) + 2 * k2 + 1 ≤ 2019)
    (halt : ∀ k : ℕ, k < k2 → (fin.of_nat (a + 1 + 2 * k) ∈ c ↔
                                ¬ fin.of_nat (a + 1 + 2 * k + 1) ∈ c)) :
  row_odd_imbalance c a k2 hk2 = 1 :=
begin
  unfold row_odd_imbalance,
  rw row_sub_black_odd_cols_alternate_1 c a k2 hk2 halt,
  by_cases h : a ∈ c,
  { rw if_pos h,
    push_cast,
    ring },
  { rw if_neg h,
    ring }
end

-- The columns of a row always alternate at the given parity.
def row_cols_alternate_at_parity (c : row_colouring) (parity : ℕ) : Prop :=
∀ k : ℕ, k < 2018 → k % 2 = parity → (fin.of_nat k ∈ c ↔ ¬ fin.of_nat (k + 1) ∈ c)

-- The columns of a row always alternate at some parity.
def row_cols_alternate_some_parity (c : row_colouring) : Prop :=
row_cols_alternate_at_parity c 0 ∨ row_cols_alternate_at_parity c 1

-- If the columns of a row always alternate at some parity, it is
-- row_balanced.
theorem row_balanced_if_row_cols_alternate_at_some_parity (c : row_colouring)
    (halt : row_cols_alternate_some_parity c) : row_balanced c :=
begin
  intros k hk a ha,
  convert le_refl 1,
  have hapar : (a : ℕ) % 2 = 0 ∨ (a : ℕ) % 2 = 1,
  { by_cases h : (a : ℕ) % 2 = 0,
    { left,
      exact h },
    { right,
      have h2 : (a : ℕ) % 2 < 2 := nat.mod_lt _ (by norm_num),
      have h3 : 0 < (a : ℕ) % 2 := nat.pos_of_ne_zero h,
      linarith } },
  cases halt; cases hapar,
  { apply row_odd_imbalance_cols_alternate_0 c a k ha,
    intros k1 hk1,
    unfold row_cols_alternate_at_parity at halt,
    apply halt,
    { linarith },
    { simpa } },
  { apply row_odd_imbalance_cols_alternate_1 c a k ha,
    intros k1 hk1,
    unfold row_cols_alternate_at_parity at halt,
    apply halt,
    { linarith },
    { rw nat.add_mul_mod_self_left,
      have ham := (nat.mod_add_div (a : ℕ) 2).symm,
      rw hapar at ham,
      rw [ham, add_assoc, add_comm _ 1, ←add_assoc],
      norm_num } },
  { apply row_odd_imbalance_cols_alternate_1 c a k ha,
    intros k1 hk1,
    unfold row_cols_alternate_at_parity at halt,
    apply halt,
    { linarith },
    { rw nat.add_mul_mod_self_left,
      have ham := (nat.mod_add_div (a : ℕ) 2).symm,
      rw hapar at ham,
      rw [ham, add_assoc, add_comm _ 1, ←add_assoc],
      norm_num } },
  { apply row_odd_imbalance_cols_alternate_0 c a k ha,
    intros k1 hk1,
    unfold row_cols_alternate_at_parity at halt,
    apply halt,
    { linarith },
    { simpa } }
end

-- If an odd number of columns of a row alternate in colour except
-- possibly at the ends, the middle part alternates in colour.
theorem row_cols_alternate_ends_middle_alt (c : row_colouring) (a : fin 2019) (k2 : ℕ)
    (hk2 : (a : ℕ) + 2 * k2 + 3 ≤ 2019)
    (halt : ∀ k : ℕ, 0 < k → k < 2 * k2 + 1 →
                     (fin.of_nat (a + k) ∈ c ↔ ¬ fin.of_nat (a + k + 1) ∈ c)) :
  ∀ (k : ℕ), k + 1 < 2 * k2 + 1 → (fin.of_nat ((a : ℕ) + 1 + k) ∈ c ↔ ¬ fin.of_nat ((a : ℕ) + 1 + k + 1) ∈ c) :=
begin
  intros k hk,
  rw (show (a : ℕ) + 1 + k = (a : ℕ) + (k + 1), by ring),
  apply halt (k + 1),
  { linarith },
  { exact hk }
end

-- The number of black cells in an odd number of columns of a row that
-- alternate in colour except at the ends.
theorem row_sub_black_cols_alternate_ends (c : row_colouring) (a : fin 2019) (k2 : ℕ)
    (hk2 : (a : ℕ) + 2 * k2 + 3 ≤ 2019)
    (halt : ∀ k : ℕ, 0 < k → k < 2 * k2 + 1 →
                     (fin.of_nat (a + k) ∈ c ↔ ¬ fin.of_nat (a + k + 1) ∈ c))
    (hnalt1 : a ∈ c ↔ fin.of_nat (a + 1) ∈ c)
    (hnalt2 : fin.of_nat (a + 2 * k2 + 1) ∈ c ↔ fin.of_nat (a + 2 * k2 + 2) ∈ c) :
  row_sub_black c a (2 * k2 + 3) = ite (a ∈ c) (k2 + 3) k2 :=
begin
  rw (show 2 * k2 + 3 = 1 + (2 * k2 + 1) + 1, by ring),
  have hs1 : (a : ℕ) + (1 + (2 * k2 + 1)) < 2019, {linarith},
  rw [row_sub_black_split_cols _ _ _ _ hs1, row_sub_black_one_col,
      (show (a : ℕ) + (1 + (2 * k2 + 1)) = (a : ℕ) + 2 * k2 + 2, by ring)],
  have hs2 : (a : ℕ) + 1 < 2019, {linarith},
  have hendcol : fin.of_nat (a + 2 * k2 + 2) ∈ c ↔ a ∈ c,
  { rw [hnalt1, ←hnalt2, (show (a : ℕ) + 2 * k2 + 1 = (a : ℕ) + 1 + 2 * k2, by ring)],
    conv
    begin
      to_lhs,
      congr,
      congr,
      rw ←of_nat_coe _ hs2
    end,
    rw row_cols_alternate_colour c (fin.of_nat ((a : ℕ) + 1)) (2 * k2 + 1) _ _ (2 * k2) _,
    all_goals { try { rw of_nat_coe _ hs2 } },
    { simp },
    { linarith },
    { exact row_cols_alternate_ends_middle_alt c a k2 hk2 halt },
    { linarith } },
  conv
  begin
    to_lhs,
    congr,
    skip,
    congr,
    rw hendcol
  end,
  rw [row_sub_black_split_cols _ _ _ _ hs2, row_sub_black_one_col],
  rw row_sub_black_cols_alternate c (fin.of_nat ((a : ℕ) + 1)) (2 * k2 + 1) _ _,
  all_goals { try { rw of_nat_coe _ hs2 } },
  { conv
    begin
      to_lhs,
      congr,
      congr,
      skip,
      congr,
      rw ←hnalt1
    end,
    by_cases h : a ∈ c,
    { simp [h, nat.succ_eq_add_one],
      ring },
    { conv
      begin
        to_lhs,
        congr,
        congr,
        skip,
        congr,
        skip,
        skip,
        rw [add_comm, nat.add_mul_div_left 1 k2 (show 2 > 0, by norm_num)],
        norm_num
      end,
      simp [h] } },
  { linarith },
  { exact row_cols_alternate_ends_middle_alt c a k2 hk2 halt }
end

-- Thus, the odd imbalance in that case.
theorem row_odd_imbalance_cols_alternate_ends (c : row_colouring) (a : fin 2019) (k2 : ℕ)
    (hk2 : (a : ℕ) + 2 * k2 + 3 ≤ 2019)
    (halt : ∀ k : ℕ, 0 < k → k < 2 * k2 + 1 →
                     (fin.of_nat (a + k) ∈ c ↔ ¬ fin.of_nat (a + k + 1) ∈ c))
    (hnalt1 : a ∈ c ↔ fin.of_nat (a + 1) ∈ c)
    (hnalt2 : fin.of_nat (a + 2 * k2 + 1) ∈ c ↔ fin.of_nat (a + 2 * k2 + 2) ∈ c) :
  row_odd_imbalance c a (k2 + 1) hk2 = 3 :=
begin
  unfold row_odd_imbalance,
  erw row_sub_black_cols_alternate_ends c a k2 hk2 halt hnalt1 hnalt2,
  by_cases h : a ∈ c,
  { rw if_pos h,
    push_cast,
    ring },
  { rw if_neg h,
    push_cast,
    ring }
end

-- TODO: rest of solution.

-- The remaining two parts of the sum for the result.

theorem result_r_c : card row_balanced_colourings_r_c = 2 :=
begin
  sorry
end

theorem result_r_no_c : card row_balanced_colourings_r_no_c = 2^1011 - 4 :=
begin
  sorry
end

-- The result of the problem.
theorem p3_result : finset.card balanced_colourings = 2^1012 - 6 :=
begin
  rw [card_split_2_row, result_r_c, result_r_no_c],
  norm_num
end
