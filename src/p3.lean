-- BMO2 2020 problem 3.

import data.finset
import data.fintype.basic
import data.nat.parity
import logic.function.basic
import tactic.interval_cases
import tactic.linarith
import tactic.ring_exp

noncomputable theory
open_locale classical

open finset

-- The grid.
abbreviation grid (n : ℕ) := fin n × fin n

-- A colouring of the grid (the set of black cells).
abbreviation colouring (n : ℕ) := finset (grid n)

-- A rectangular subgrid of the coloured grid.  (This definition
-- allows the rectangle to go off the edges, so separate hypotheses
-- are needed where that is undesirable.)  Although the problem only
-- refers to square subgrids, rectangular ones are useful in the
-- solution when counting black squares in colourings made from
-- alternating rows.
def subcolouring {n : ℕ} (c : colouring n) (a b : fin n) (k1 k2 : ℕ) : finset (grid n) :=
finset.filter (λ p : grid n, a ≤ p.1 ∧ b ≤ p.2 ∧
                             (p.1 : ℕ) < (a : ℕ) + k1 ∧ (p.2 : ℕ) < (b : ℕ) + k2) c

-- The complement of a colouring.
def complement {n : ℕ} (c : colouring n) : colouring n := finset.univ \ c

-- The number of black cells in a subgrid.
def sub_black {n : ℕ} (c : colouring n) (a b : fin n) (k1 k2 : ℕ) : ℕ :=
finset.card (subcolouring c a b k1 k2)

-- The number of white cells in a subgrid.
def sub_white {n : ℕ} (c : colouring n) (a b : fin n) (k1 k2 : ℕ) : ℕ :=
finset.card (subcolouring (complement c) a b k1 k2)

-- The imbalance of a subgrid.
def sub_imbalance {n : ℕ} (c : colouring n) (a b : fin n) (k : ℕ) : ℕ :=
int.nat_abs (((sub_black c a b k k) : ℤ) - ((sub_white c a b k k) : ℤ))

-- Whether a subgrid is balanced.
def sub_balanced {n : ℕ} (c : colouring n) (a b : fin n) (k : ℕ) : Prop :=
sub_imbalance c a b k ≤ 1

-- Whether a colouring is balanced for subgrids of side k.
def balanced_k {n : ℕ} (c : colouring n) (k : ℕ) : Prop :=
∀ (a b : fin n), (a : ℕ) + k ≤ n → (b : ℕ) + k ≤ n → sub_balanced c a b k

-- Whether a colouring is balanced.
def balanced {n : ℕ} (c : colouring n) : Prop :=
∀ (k : ℕ), 1 ≤ k → k ≤ n → balanced_k c k

-- The set of balanced colourings.
def balanced_colourings (n : ℕ) : finset (colouring n) :=
finset.univ.filter balanced

-- Adding the numbers of black and white cells in a subgrid.
theorem sub_black_add_sub_white {n : ℕ} (c : colouring (n + 1)) (a b : fin (n + 1)) (k : ℕ)
    (ha : (a : ℕ) + k ≤ n + 1) (hb : (b : ℕ) + k ≤ n + 1) :
  sub_black c a b k k + sub_white c a b k k = k * k :=
begin
  unfold sub_black sub_white subcolouring complement,
  rw [←card_union_add_card_inter, ←filter_union, filter_inter, inter_filter,
      union_sdiff_of_subset (subset_univ _), inter_sdiff_self, filter_empty, filter_empty,
      card_empty, add_zero],
  refine card_eq_of_bijective (λ i h, ⟨((a : ℕ) + i / k : ℕ), ((b : ℕ) + i % k : ℕ)⟩)
    _ _ _,
  { intros p hp,
    rw mem_filter at hp,
    rcases hp with ⟨hpu, ha1, hb1, ha2, hb2⟩,
    use ((p.fst : ℕ) - a) * k + ((p.snd : ℕ) - b),
    rw fin.le_iff_coe_le_coe at ha1,
    rw fin.le_iff_coe_le_coe at hb1,
    rw ←nat.sub_lt_left_iff_lt_add ha1 at ha2,
    rw ←nat.sub_lt_left_iff_lt_add hb1 at hb2,
    split,
    { have h1 : ((p.fst : ℕ) - (a : ℕ)) * k ≤ (k - 1) * k :=
        mul_le_mul_of_nonneg_right (nat.le_pred_of_lt ha2) (nat.zero_le _),
      have h2 : k * k = (k - 1) * k + k,
      { cases k with kk,
        { norm_num },
        { simp [nat.succ_eq_add_one],
          ring } },
      linarith },
    { ext,
      { unfold prod.fst,
        cases k with kk,
        { exfalso,
          exact nat.not_lt_zero _ ha2 },
        { rw [add_comm (((p.fst : ℕ) - a) * nat.succ kk) ((p.snd : ℕ) - b),
              nat.add_mul_div_right _ _ (nat.zero_lt_succ _), nat.div_eq_of_lt hb2, zero_add,
              ←nat.add_sub_assoc ha1, nat.add_sub_cancel_left, fin.coe_coe_eq_self p.fst] } },
      { unfold prod.snd,
        cases k with kk,
        { exfalso,
          exact nat.not_lt_zero _ ha2 },
        { rw [add_comm (((p.fst : ℕ) - a) * nat.succ kk) ((p.snd : ℕ) - b),
              nat.add_mul_mod_self_right, nat.mod_eq_of_lt hb2, ←nat.add_sub_assoc hb1,
              nat.add_sub_cancel_left, fin.coe_coe_eq_self p.snd] } } } },
  { intros i hi,
    rw mem_filter,
    split,
    { exact mem_univ _ },
    { simp only [fin.le_iff_coe_le_coe],
      have hkpos : 0 < k,
      { by_contradiction,
        have hk0 : k = 0, { linarith },
        rw [hk0, mul_zero] at hi,
        exact nat.not_lt_zero _ hi },
      have hidiv : i / k < k,
      { rw nat.div_lt_iff_lt_mul _ _ hkpos,
        exact hi },
      have himod : i % k < k := nat.mod_lt _ hkpos,
      repeat { split },
      { have hax : ((a : ℕ) + i / k) < n + 1, { linarith },
        rw fin.coe_coe_of_lt hax,
        exact nat.le_add_right _ _ },
      { have hbx : ((b : ℕ) + i % k) < n + 1, { linarith },
        rw fin.coe_coe_of_lt hbx,
        exact nat.le_add_right _ _ },
      { have hax : ((a : ℕ) + i / k) < n + 1, { linarith },
        rw fin.coe_coe_of_lt hax,
        linarith },
      { have hbx : ((b : ℕ) + i % k) < n + 1, { linarith },
        rw fin.coe_coe_of_lt hbx,
        linarith } } },
  { intros i j hi hj heq,
    rw prod.mk.inj_iff at heq,
    cases heq with heq1 heq2,
    have hkpos : 0 < k,
    { by_contradiction,
      have hk0 : k = 0, { linarith },
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
    have hai : (a : ℕ) + i / k < n + 1, { linarith },
    have haj : (a : ℕ) + j / k < n + 1, { linarith },
    have hbi : (b : ℕ) + i % k < n + 1, { linarith },
    have hbj : (b : ℕ) + j % k < n + 1, { linarith },
    rw [fin.ext_iff, fin.coe_coe_of_lt hai, fin.coe_coe_of_lt haj,
        add_left_cancel_iff] at heq1,
    rw [fin.ext_iff, fin.coe_coe_of_lt hbi, fin.coe_coe_of_lt hbj,
        add_left_cancel_iff] at heq2,
    rw [←nat.mod_add_div i k, ←nat.mod_add_div j k, heq1, heq2] }
end

-- Number of black cells in a subgrid, inequality.
theorem sub_black_le {n : ℕ} (c : colouring (n + 1)) (a b : fin (n + 1)) (k : ℕ)
    (ha : (a : ℕ) + k ≤ (n + 1)) (hb : (b : ℕ) + k ≤ (n + 1)) : sub_black c a b k k ≤ k * k :=
begin
  rw ← sub_black_add_sub_white c a b k ha hb,
  exact nat.le_add_right _ _,
end

-- Number of white cells in a subgrid, more convenient form.
theorem sub_white_eq {n : ℕ} (c : colouring (n + 1)) (a b : fin (n + 1)) (k : ℕ)
    (ha : (a : ℕ) + k ≤ n + 1) (hb : (b : ℕ) + k ≤ n + 1) :
  sub_white c a b k k = k * k - sub_black c a b k k :=
begin
  symmetry,
  rw [nat.sub_eq_iff_eq_add (sub_black_le c a b k ha hb), add_comm],
  symmetry,
  exact sub_black_add_sub_white c a b k ha hb
end

-- Imbalance in terms only of number of black cells.
theorem imbalance_eq {n : ℕ} (c : colouring (n + 1)) (a b : fin (n + 1)) (k : ℕ)
    (ha : (a : ℕ) + k ≤ n + 1) (hb : (b : ℕ) + k ≤ n + 1) :
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
def transpose_cell {n : ℕ} (p : grid n) : grid n := ⟨p.snd, p.fst⟩

-- Transposing twice produces the original cell.
theorem transpose_cell_involutive {n : ℕ} : function.involutive (@transpose_cell n) :=
begin
  intro p,
  unfold transpose_cell,
  ext,
  { unfold prod.fst },
  { unfold prod.snd },
end

-- And transposing is thus bijective.
theorem transpose_cell_bijective {n : ℕ} : function.bijective (@transpose_cell n) :=
function.involutive.bijective transpose_cell_involutive

-- And the composition is the identity.
theorem transpose_cell_twice_id {n : ℕ} : (@transpose_cell n) ∘ (@transpose_cell n) = id :=
begin
  rw ←function.involutive_iff_iter_2_eq_id.elim_left transpose_cell_involutive,
  refl
end

-- And the composition is the identity, variant form.
theorem transpose_cell_twice_id' {n : ℕ} (p : grid n) :
  transpose_cell (transpose_cell p) = p :=
begin
  change (transpose_cell ∘ transpose_cell) p = p,
  rw transpose_cell_twice_id,
  refl
end

-- A colouring, transposed.
def transpose_colouring {n : ℕ} (c : colouring n) : colouring n := c.image transpose_cell

-- Transposing twice produces the original colouring.
theorem transpose_colouring_involutive {n : ℕ} : function.involutive (@transpose_colouring n) :=
begin
  intro p,
  unfold transpose_colouring,
  rw image_image,
  rw transpose_cell_twice_id,
  exact image_id
end

-- And transposing is thus bijective.
theorem transpose_colouring_bijective {n : ℕ} : function.bijective (@transpose_colouring n) :=
function.involutive.bijective transpose_colouring_involutive

-- And the composition is the identity.
theorem transpose_colouring_twice_id {n : ℕ} :
  (@transpose_colouring n) ∘ (@transpose_colouring n) = id :=
begin
  rw ←function.involutive_iff_iter_2_eq_id.elim_left transpose_colouring_involutive,
  refl
end

-- And the composition is the identity, variant form.
theorem transpose_colouring_twice_id' {n : ℕ} (c : colouring n) :
  transpose_colouring (transpose_colouring c) = c :=
begin
  change (transpose_colouring ∘ transpose_colouring) c = c,
  rw transpose_colouring_twice_id,
  refl
end

-- Condition for a cell to be in the transpose.
theorem cell_in_transpose_iff {n : ℕ} (c : colouring n) (a b : fin n) :
  (a, b) ∈ c ↔ (b, a) ∈ transpose_colouring c :=
begin
  unfold transpose_colouring,
  rw mem_image,
  split,
  { intro h,
    use [(a, b), h],
    refl },
  { rintros ⟨x, hx1, hx2⟩,
    have hx3 : (a, b) = transpose_cell (transpose_cell x),
    { rw hx2,
      unfold transpose_cell },
    rw transpose_cell_twice_id' at hx3,
    convert hx1 }
end

-- Condition for a cell not to be in the transpose.
theorem cell_not_in_transpose_iff {n : ℕ} (c : colouring n) (a b : fin n) :
  (a, b) ∉ c ↔ (b, a) ∉ transpose_colouring c :=
begin
  rw not_iff_not,
  exact cell_in_transpose_iff c a b
end

-- Transposing a subcolouring produces the same results as taking the
-- corresponding subcolouring of the transpose.
theorem transpose_subcolouring {n : ℕ} (c : colouring n) (a b : fin n) (k : ℕ) :
  transpose_colouring (subcolouring c a b k k) = subcolouring (transpose_colouring c) b a k k :=
begin
  unfold transpose_colouring subcolouring,
  ext,
  rw [mem_image, mem_filter, mem_image],
  split,
  { rintros ⟨p, hp2, hpt⟩,
    rw mem_filter at hp2,
    split,
    { exact ⟨p, hp2.1, hpt⟩ },
    { unfold transpose_cell at hpt,
      rw ←hpt,
      unfold prod.fst prod.snd,
      rcases hp2 with ⟨hp2a, hp2b, hp2c, hp2d, hp2e⟩,
      exact ⟨hp2c, hp2b, hp2e, hp2d⟩ } },
  { rintros ⟨⟨p, hp1, hpt⟩, h2⟩,
    unfold transpose_cell at hpt,
    rw ←hpt at h2,
    unfold prod.fst prod.snd at h2,
    rcases h2 with ⟨h2a, h2b, h2c, h2d⟩,
    use p,
    rw mem_filter,
    exact ⟨⟨hp1, h2b, h2a, h2d, h2c⟩, hpt⟩ },
end

-- The number of black cells in a subgrid behaves as expected under
-- transposition.
theorem transpose_sub_black {n : ℕ} (c : colouring n) (a b : fin n) (k : ℕ) :
  sub_black c a b k k = sub_black (transpose_colouring c) b a k k :=
begin
  unfold sub_black,
  rw ←transpose_subcolouring,
  unfold transpose_colouring,
  rw card_image_of_injective _ transpose_cell_bijective.1
end

-- If a colouring is balanced for subgrids of side k, so is its
-- transpose.
theorem transpose_balanced_k {n : ℕ} (c : colouring (n + 1)) (k : ℕ) (h : balanced_k c k) :
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
theorem transpose_balanced {n : ℕ} (c : colouring (n + 1)) (h : balanced c) :
  balanced (transpose_colouring c) :=
begin
  intros k hk1 hk2,
  exact transpose_balanced_k c k (h k hk1 hk2)
end

-- A colouring is balanced if and only if its transpose is.
theorem transpose_balanced_iff {n : ℕ} (c : colouring (n + 1)) :
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
def rows_alternate {n : ℕ} (c : colouring (n + 1)) : Prop :=
∀ (a b : fin (n + 1)) (h : (a : ℕ) < n),
  (a, b) ∈ c ↔ ¬ ((((a : ℕ) + 1 : ℕ) : fin (n + 1)), b) ∈ c

-- Colourings with alternating columns.
def cols_alternate {n : ℕ} (c : colouring (n + 1)) : Prop :=
∀ (a b : fin (n + 1)) (h : (b : ℕ) < n),
  (a, b) ∈ c ↔ ¬ (a, (((b : ℕ) + 1 : ℕ) : fin (n + 1))) ∈ c

-- Rows alternate if and only if columns of transpose alternate.
theorem rows_alternate_iff_transpose {n : ℕ} (c : colouring (n + 1)) :
  rows_alternate c ↔ cols_alternate (transpose_colouring c) :=
begin
  split,
  { unfold rows_alternate cols_alternate transpose_colouring,
    intros h a b hb,
    convert h b a hb using 1,
    { rw ←iff_eq_eq,
      exact (cell_in_transpose_iff c b a).symm },
    { rw ←iff_eq_eq,
      exact (cell_not_in_transpose_iff c _ _).symm } },
  { unfold rows_alternate cols_alternate transpose_colouring,
    intros h a b ha,
    convert h b a ha using 1,
    { rw ←iff_eq_eq,
      exact cell_in_transpose_iff c a b },
    { rw ←iff_eq_eq,
      exact cell_not_in_transpose_iff c _ _ } }
end

-- Split into cases according to which of rows and columns alternate.

def not_rows_alternate {n : ℕ} (c : colouring (n + 1)) : Prop :=
¬ rows_alternate c

def not_cols_alternate {n : ℕ} (c : colouring (n + 1)) : Prop :=
¬ cols_alternate c

def balanced_colourings_r (n : ℕ) : finset (colouring (n + 1)) :=
(balanced_colourings (n + 1)).filter rows_alternate

def balanced_colourings_no_r (n : ℕ) : finset (colouring (n + 1)) :=
(balanced_colourings (n + 1)).filter not_rows_alternate

-- Together these are all balanced colourings.
theorem rows_alternate_or_not (n : ℕ) :
  balanced_colourings_r n ∪ balanced_colourings_no_r n = balanced_colourings (n + 1) :=
begin
  unfold balanced_colourings_r balanced_colourings_no_r,
  convert filter_union_filter_neg_eq _ (balanced_colourings (n + 1)),
  exact classical.dec_pred _
end

-- These have empty intersection.
theorem rows_alternate_xor_not (n : ℕ) :
  balanced_colourings_r n ∩ balanced_colourings_no_r n = ∅ :=
begin
  unfold balanced_colourings_r balanced_colourings_no_r,
  convert filter_inter_filter_neg_eq _ (balanced_colourings (n + 1))
end

-- Thus the cardinality of the set of balanced colourings.
theorem card_split_r (n : ℕ) :
  card (balanced_colourings (n + 1)) =
    card (balanced_colourings_r n) + card (balanced_colourings_no_r n) :=
begin
  rw ← rows_alternate_or_not,
  convert card_union_add_card_inter _ _,
  { rw rows_alternate_xor_not,
    simp }
end

-- Now repeat these arguments to split up again by whether columns
-- alternate or not.

def balanced_colourings_r_c (n : ℕ) : finset (colouring (n + 1)) :=
(balanced_colourings_r n).filter cols_alternate

def balanced_colourings_r_no_c (n : ℕ) : finset (colouring (n + 1)) :=
(balanced_colourings_r n).filter not_cols_alternate

def balanced_colourings_no_r_c (n : ℕ) : finset (colouring (n + 1)) :=
(balanced_colourings_no_r n).filter cols_alternate

def balanced_colourings_no_r_no_c (n : ℕ) : finset (colouring (n + 1)) :=
(balanced_colourings_no_r n).filter not_cols_alternate

theorem r_cols_alternate_or_not (n : ℕ) :
  balanced_colourings_r_c n ∪ balanced_colourings_r_no_c n = balanced_colourings_r n :=
begin
  unfold balanced_colourings_r_c balanced_colourings_r_no_c,
  convert filter_union_filter_neg_eq _ (balanced_colourings_r n),
  exact classical.dec_pred _
end

theorem r_cols_alternate_xor_not (n : ℕ) :
  balanced_colourings_r_c n ∩ balanced_colourings_r_no_c n = ∅ :=
begin
  unfold balanced_colourings_r_c balanced_colourings_r_no_c,
  convert filter_inter_filter_neg_eq _ (balanced_colourings_r n)
end

theorem card_split_r_c (n : ℕ) :
  card (balanced_colourings_r n) =
    card (balanced_colourings_r_c n) + card (balanced_colourings_r_no_c n) :=
begin
  rw ← r_cols_alternate_or_not,
  convert card_union_add_card_inter _ _,
  { rw r_cols_alternate_xor_not,
    simp }
end

theorem no_r_cols_alternate_or_not (n : ℕ) :
  balanced_colourings_no_r_c n ∪ balanced_colourings_no_r_no_c n = balanced_colourings_no_r n :=
begin
  unfold balanced_colourings_no_r_c balanced_colourings_no_r_no_c,
  convert filter_union_filter_neg_eq _ (balanced_colourings_no_r n),
  exact classical.dec_pred _
end

theorem no_r_cols_alternate_xor_not (n : ℕ) :
  balanced_colourings_no_r_c n ∩ balanced_colourings_no_r_no_c n = ∅ :=
begin
  unfold balanced_colourings_no_r_c balanced_colourings_no_r_no_c,
  convert filter_inter_filter_neg_eq _ (balanced_colourings_no_r n)
end

theorem card_split_no_r_c (n : ℕ) :
  card (balanced_colourings_no_r n) =
    card (balanced_colourings_no_r_c n) + card (balanced_colourings_no_r_no_c n) :=
begin
  rw ← no_r_cols_alternate_or_not,
  convert card_union_add_card_inter _ _,
  { rw no_r_cols_alternate_xor_not,
    simp }
end

-- Thus the cardinality of the set of balanced colourings, fully split.
theorem card_split_4 (n : ℕ) :
  card (balanced_colourings (n + 1)) =
    (card (balanced_colourings_r_c n) + card (balanced_colourings_r_no_c n)) +
      (card (balanced_colourings_no_r_c n) + card (balanced_colourings_no_r_no_c n)) :=
begin
  rw [card_split_r, card_split_r_c, card_split_no_r_c]
end

-- Two of those terms have the same value.
theorem card_r_no_c_eq_c_no_r (n : ℕ) :
  card (balanced_colourings_r_no_c n) = card (balanced_colourings_no_r_c n) :=
begin
  unfold balanced_colourings_r_no_c balanced_colourings_no_r_c balanced_colourings_r
    balanced_colourings_no_r,
  rw [filter_filter, filter_filter],
  convert card_image_of_injective
          (filter (λ (a : colouring (n + 1)), not_rows_alternate a ∧ cols_alternate a)
                  (balanced_colourings (n + 1)))
          transpose_colouring_bijective.1,
  ext,
  rw [mem_image, mem_filter],
  split,
  { rintros ⟨hb, hr, hnc⟩,
    unfold not_cols_alternate at hnc,
    use transpose_colouring a,
    rw mem_filter,
    unfold not_rows_alternate,
    rw [←rows_alternate_iff_transpose, rows_alternate_iff_transpose,
        transpose_colouring_twice_id'],
    unfold balanced_colourings at *,
    rw mem_filter at *,
    rw ←transpose_balanced_iff,
    exact ⟨⟨⟨(mem_univ _), hb.2⟩, hnc, hr⟩, rfl⟩ },
  { rintros ⟨b, hb1, hb2⟩,
    rw mem_filter at hb1,
    rcases hb1 with ⟨hb1bal, ⟨hb1nr, hb1c⟩⟩,
    have hbx : transpose_colouring (transpose_colouring b) = transpose_colouring a, { rw hb2 },
    rw transpose_colouring_twice_id' at hbx,
    rw hbx at hb1bal hb1nr hb1c,
    unfold not_rows_alternate at hb1nr,
    unfold not_cols_alternate,
    unfold balanced_colourings at *,
    rw mem_filter at *,
    rw ←transpose_balanced_iff at hb1bal,
    rw ←rows_alternate_iff_transpose at hb1c,
    rw [rows_alternate_iff_transpose, transpose_colouring_twice_id'] at hb1nr,
    exact ⟨⟨(mem_univ _), hb1bal.2⟩, hb1c, hb1nr⟩ }
end

-- Thus the cardinality of the set of balanced colourings, in three parts.
theorem card_split_3 (n : ℕ) :
  card (balanced_colourings (n + 1)) = card (balanced_colourings_r_c n) +
    2 * card (balanced_colourings_r_no_c n) + card (balanced_colourings_no_r_no_c n) :=
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
theorem sub_balanced_2 {n : ℕ} (c : colouring (n + 1)) (a b : fin (n + 1))
    (ha : (a : ℕ) < n) (hb : (b : ℕ) < n) :
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
theorem subcolouring_2 {n : ℕ} (c : colouring (n + 1)) (a b : fin (n + 1))
    (ha : (a : ℕ) < n) (hb : (b : ℕ) < n) :
  subcolouring c a b 2 2 = (c.filter (λ p, p = (a, b))) ∪
                           (c.filter (λ p, p = (a, (((b : ℕ) + 1 : ℕ) : fin (n + 1))))) ∪
                           (c.filter (λ p, p = ((((a : ℕ) + 1 : ℕ) : fin (n + 1)), b))) ∪
                           (c.filter (λ p, p = ((((a : ℕ) + 1 : ℕ) : fin (n + 1)),
                                                (((b : ℕ) + 1 : ℕ) : fin (n + 1))))) :=
begin
  unfold subcolouring,
  repeat { rw filter_union_right },
  ext,
  repeat { rw mem_filter },
  cases a with a_val ah,
  cases b with b_val bh,
  rcases a_1 with ⟨⟨x_val, xh⟩, ⟨y_val, yh⟩⟩,
  rw fin.coe_mk at ha hb,
  have hao1 : nat.succ a_val < n + 1,
  { rw nat.succ_eq_add_one, linarith },
  have hbo1 : nat.succ b_val < n + 1,
  { rw nat.succ_eq_add_one, linarith },
  have hao : ((a_val + 1 : ℕ) : fin (n + 1)) = ⟨a_val + 1, hao1⟩,
  { apply fin.ext,
    rw fin.coe_mk,
    exact fin.coe_coe_of_lt (show a_val + 1 < n + 1, by linarith only [ha]) },
  have hbo : ((b_val + 1 : ℕ) : fin (n + 1)) = ⟨b_val + 1, hbo1⟩,
  { apply fin.ext,
    rw fin.coe_mk,
    exact fin.coe_coe_of_lt (show b_val + 1 < n + 1, by linarith only [hb]) },
  simp only [fin.le_iff_coe_le_coe, prod.mk.inj_iff, fin.ext_iff, fin.coe_mk, hao, hbo],
  split,
  { rintros ⟨h1, h2, h3, h4, h5⟩,
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
  { rintros ⟨h1, h⟩,
    repeat { cases h }; subst h_left; subst h_right,
    { split,
      { exact h1 },
      { exact ⟨le_rfl, le_rfl, (lt_add_of_pos_right _ dec_trivial),
               (lt_add_of_pos_right _ dec_trivial)⟩ } },
    { split,
      { exact h1 },
      { exact ⟨le_rfl, (le_add_of_nonneg_right dec_trivial),
               (lt_add_of_pos_right _ dec_trivial), (by linarith)⟩ } },
    { split,
      { exact h1 },
      { exact ⟨(le_add_of_nonneg_right dec_trivial), le_rfl, (by linarith),
               (lt_add_of_pos_right _ dec_trivial)⟩ } },
    { split,
      { exact h1 },
      { exact ⟨(le_add_of_nonneg_right dec_trivial), (le_add_of_nonneg_right dec_trivial),
               (by linarith), (by linarith)⟩ } } }
end

-- A subgrid of side 2 has number of black cells given by the
-- corresponding four cells.
theorem sub_black_2 {n : ℕ} (c : colouring (n + 1)) (a b : fin (n + 1))
    (ha : (a : ℕ) < n) (hb : (b : ℕ) < n) :
  sub_black c a b 2 2 =
    (c.filter (λ p : grid (n + 1), p = (a, b))).card +
    (c.filter (λ p : grid (n + 1), p = (a, (((b : ℕ) + 1 : ℕ) : fin (n + 1))))).card +
    (c.filter (λ p : grid (n + 1), p = ((((a : ℕ) + 1 : ℕ) : fin (n + 1)), b))).card +
    (c.filter (λ p : grid (n + 1), p = ((((a : ℕ) + 1 : ℕ) : fin (n + 1)),
                                        (((b : ℕ) + 1 : ℕ) : fin (n + 1))))).card :=
begin
  have hao1 : (a : ℕ) + 1 < n + 1, { linarith },
  have hbo1 : (b : ℕ) + 1 < n + 1, { linarith },
  unfold sub_black,
  rw subcolouring_2 c a b ha hb,
  convert card_union_add_card_inter
    ((c.filter (λ p, p = (a, b))) ∪
     (c.filter (λ p, p = (a, (((b : ℕ) + 1 : ℕ) : fin (n + 1))))) ∪
     (c.filter (λ p, p = ((((a : ℕ) + 1 : ℕ) : fin (n + 1)), b))))
    (c.filter (λ p : grid (n + 1), p = ((((a : ℕ) + 1 : ℕ) : fin (n + 1)),
                                        (((b : ℕ) + 1 : ℕ) : fin (n + 1))))),
  { conv_lhs { rw ←nat.add_zero (card ((c.filter (λ p, p = (a, b))) ∪
                    (c.filter (λ p, p = (a, (((b : ℕ) + 1 : ℕ) : fin (n + 1))))) ∪
                    (c.filter (λ p, p = ((((a : ℕ) + 1 : ℕ) : fin (n + 1)), b))) ∪
                    (c.filter (λ p, p = ((((a : ℕ) + 1 : ℕ) : fin (n + 1)),
                                         (((b : ℕ) + 1 : ℕ) : fin (n + 1))))))) },
    rw add_left_cancel_iff,
    symmetry,
    rw [card_eq_zero, ←filter_or, ←filter_or, ←filter_and],
    convert filter_false c,
    { ext,
      split,
      { rintros ⟨h1, rfl⟩,
        simp only [prod.mk.inj_iff, fin.ext_iff, fin.coe_coe_of_lt, hao1, hbo1, nat.succ_ne_self,
                   false_and, and_false, or_false] at h1,
        exact h1 },
      { exact false.elim } },
    { exact classical.dec_pred _ } },
  { symmetry,
    convert card_union_add_card_inter
      ((c.filter (λ p, p = (a, b))) ∪
       (c.filter (λ p, p = (a, (((b : ℕ) + 1 : ℕ) : fin (n + 1))))))
      (c.filter (λ p, p = ((((a : ℕ) + 1 : ℕ) : fin (n + 1)), b))),
    { conv_lhs { rw ←nat.add_zero (card ((c.filter (λ p, p = (a, b))) ∪
                      (c.filter (λ p, p = (a, (((b : ℕ) + 1 : ℕ) : fin (n + 1))))) ∪
                      (c.filter (λ p, p = ((((a : ℕ) + 1 : ℕ) : fin (n + 1)), b))))) },
      rw add_left_cancel_iff,
      symmetry,
      rw [card_eq_zero, ←filter_or, ←filter_and],
      convert filter_false c,
      { ext,
        split,
        { rintros ⟨h1, rfl⟩,
          simp only [prod.mk.inj_iff, fin.ext_iff, fin.coe_coe_of_lt, hao1, hbo1,
                     nat.succ_ne_self, false_and, and_false, or_false] at h1,
          exact h1 },
        { exact false.elim } },
      { exact classical.dec_pred _ } },
    { symmetry,
      convert card_union_add_card_inter
        (c.filter (λ p, p = (a, b)))
        (c.filter (λ p, p = (a, (((b : ℕ) + 1 : ℕ) : fin (n + 1))))),
      conv_lhs { rw ←nat.add_zero (card ((c.filter (λ p, p = (a, b))) ∪
                      (c.filter (λ p, p = (a, (((b : ℕ) + 1 : ℕ) : fin (n + 1))))))) },
      rw add_left_cancel_iff,
      symmetry,
      rw [card_eq_zero, ←filter_and],
      convert filter_false c,
      { ext,
        split,
        { rintros ⟨h1, rfl⟩,
          simp only [prod.mk.inj_iff, fin.ext_iff, fin.coe_coe_of_lt, hbo1] at h1,
          exact nat.succ_ne_self b h1.2 },
        { exact false.elim } },
      { exact classical.dec_pred _ } } }
end

-- For rewriting in the next theorem.
theorem cell_eq_eq {n : ℕ} (a : grid n) : (λ p : grid n, p = a) = eq a :=
begin
  ext,
  exact eq_comm
end

-- For rewriting in the next theorem.
theorem cell_card_eq {n : ℕ} (c : colouring n) (a : grid n) :
  (c.filter (λ p : grid n, p = a)).card = (ite (a ∈ c) 1 0) :=
begin
  conv_lhs { congr, congr, rw cell_eq_eq },
  rw filter_eq,
  by_cases a ∈ c,
  all_goals { finish }
end

-- Two rows alternate in position b if and only if they alternate in
-- position b + 1.
theorem rows_alternate_two_cols {n : ℕ} (c : colouring (n + 1)) (hbal2 : balanced_k c 2)
    (a b : fin (n + 1)) (ha : (a : ℕ) < n) (hb : (b : ℕ) < n) :
  ((a, b) ∈ c ↔ ¬ ((((a : ℕ) + 1 : ℕ) : fin (n + 1)), b) ∈ c) ↔
    ((a, (((b : ℕ) + 1 : ℕ) : fin (n + 1))) ∈ c ↔ ¬ ((((a : ℕ) + 1 : ℕ) : fin (n + 1)),
                                                     (((b : ℕ) + 1 : ℕ) : fin (n + 1))) ∈ c) :=
begin
  have hbal2a := hbal2 a b (by linarith) (by linarith),
  rw [sub_balanced_2 c a b ha hb, sub_black_2 c a b ha hb, cell_card_eq, cell_card_eq,
      cell_card_eq, cell_card_eq] at hbal2a,
  by_cases h1 : (a, b) ∈ c; by_cases h2 : (a, (((b : ℕ) + 1 : ℕ) : fin (n + 1))) ∈ c;
    by_cases h3 : ((((a : ℕ) + 1 : ℕ) : fin (n + 1)), b) ∈ c;
    by_cases h4 : ((((a : ℕ) + 1 : ℕ) : fin (n + 1)), (((b : ℕ) + 1 : ℕ) : fin (n + 1))) ∈ c,
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
theorem rows_alternate_two_cols_later {n : ℕ} (c : colouring (n + 1)) (hbal2 : balanced_k c 2)
    (a b : fin (n + 1)) (b2 : ℕ) (ha : (a : ℕ) < n) (hb2 : (b : ℕ) < b2) (hb2a : b2 < n + 1) :
  ((a, b) ∈ c ↔ ¬ ((((a : ℕ) + 1 : ℕ) : fin (n + 1)), b) ∈ c) ↔
    ((a, (b2 : fin (n + 1))) ∈ c ↔
      ¬ ((((a : ℕ) + 1 : ℕ) : fin (n + 1)), (b2 : fin (n + 1))) ∈ c) :=
begin
  induction b2 with m hm,
  { exfalso,
    exact nat.not_lt_zero b hb2 },
  { by_cases h : (b : ℕ) < m,
    { rw nat.succ_eq_add_one at hb2a,
      have hmx := hm h (by linarith),
      rw hmx,
      have hb2ax : ((m : fin (n + 1)) : ℕ) < n,
      { rw fin.coe_coe_of_lt (show m < n + 1, by linarith),
        linarith },
      convert rows_alternate_two_cols c hbal2 a (m : fin (n + 1)) ha hb2ax,
      { exact (fin.coe_coe_of_lt (show m < n + 1, by linarith)).symm },
      { exact (fin.coe_coe_of_lt (show m < n + 1, by linarith)).symm } },
    { have hbv : (b : ℕ) = m := nat.eq_of_lt_succ_of_not_lt hb2 h,
      have hbv2 : b = (m : fin (n + 1)),
      { rw ← hbv,
        exact (fin.coe_coe_eq_self b).symm },
      have hb2ax : ((m : fin (n + 1)) : ℕ) < n,
      { rw [←hbv, fin.coe_coe_eq_self _, hbv],
        linarith },
      convert rows_alternate_two_cols c hbal2 a (m : fin (n + 1)) ha hb2ax,
      { rw [←hbv2, ←hbv] },
      { rw [←hbv2, ←hbv] } } },
end

-- Likewise, but with b2 in fin (n + 1).
theorem rows_alternate_two_cols_later' {n : ℕ} (c : colouring (n + 1)) (hbal2 : balanced_k c 2)
    (a b : fin (n + 1)) (b2 : fin (n + 1)) (ha : (a : ℕ) < n) (hb2 : b < b2) :
  ((a, b) ∈ c ↔ ¬ ((((a : ℕ) + 1 : ℕ) : fin (n + 1)), b) ∈ c) ↔
    ((a, b2) ∈ c ↔ ¬ ((((a : ℕ) + 1 : ℕ) : fin (n + 1)), b2) ∈ c) :=
begin
  have hb2b : b2 = ((b2 : ℕ) : fin (n + 1)) := (fin.coe_coe_eq_self b2).symm,
  convert rows_alternate_two_cols_later c hbal2 a b (b2 : ℕ) ha _ _,
  { norm_cast,
    exact hb2 },
  { exact b2.is_lt }
end

-- Two rows alternate in position b if and only if they alternate in
-- position b2.
theorem rows_alternate_any_two_cols {n : ℕ} (c : colouring (n + 1)) (hbal2 : balanced_k c 2)
    (a b b2 : fin (n + 1)) (ha : (a : ℕ) < n) :
  ((a, b) ∈ c ↔ ¬ ((((a : ℕ) + 1 : ℕ) : fin (n + 1)), b) ∈ c) ↔
    ((a, b2) ∈ c ↔ ¬ ((((a : ℕ) + 1 : ℕ) : fin (n + 1)), b2) ∈ c) :=
begin
  cases lt_trichotomy b b2,
  { exact rows_alternate_two_cols_later' c hbal2 a b b2 ha h },
  { cases h,
   { rw h },
   { symmetry,
     exact rows_alternate_two_cols_later' c hbal2 a b2 b ha h } },
end

-- Likewise, expressed in terms of not alternating.
theorem rows_alternate_any_two_cols' {n : ℕ} (c : colouring (n + 1)) (hbal2 : balanced_k c 2)
    (a b b2 : fin (n + 1)) (ha : (a : ℕ) < n) :
  ((a, b) ∈ c ↔ ((((a : ℕ) + 1 : ℕ) : fin (n + 1)), b) ∈ c) ↔
    ((a, b2) ∈ c ↔ ((((a : ℕ) + 1 : ℕ) : fin (n + 1)), b2) ∈ c) :=
begin
  rw [←not_iff_not, not_iff, not_iff_comm, not_iff],
  conv { congr, rw iff.comm, skip, rw [not_iff_comm, iff.comm] },
  exact rows_alternate_any_two_cols c hbal2 a b b2 ha
end

-- Two columns alternate in position b if and only if they alternate
-- in position b2.
theorem cols_alternate_any_two_rows {n : ℕ} (c : colouring (n + 1)) (hbal2 : balanced_k c 2)
    (a b b2 : fin (n + 1)) (ha : (a : ℕ) < n) :
  ((b, a) ∈ c ↔ ¬ (b, (((a : ℕ) + 1 : ℕ) : fin (n + 1))) ∈ c) ↔
    ((b2, a) ∈ c ↔ ¬ (b2, (((a : ℕ) + 1 : ℕ) : fin (n + 1))) ∈ c) :=
begin
  convert rows_alternate_any_two_cols (transpose_colouring c) (transpose_balanced_k c 2 hbal2)
    a b b2 ha using 1,
  { rw [cell_in_transpose_iff, cell_not_in_transpose_iff] },
  { rw [cell_in_transpose_iff, cell_not_in_transpose_iff] }
end

-- If two rows fail to alternate in column b, columns b and b + 1
-- alternate in row a.
theorem rows_not_alternate_two_cols {n : ℕ} (c : colouring (n + 1)) (hbal2 : balanced_k c 2)
    (a b : fin (n + 1)) (ha : (a : ℕ) < n) (hb : (b : ℕ) < n)
    (hnalt : (a, b) ∈ c ↔ ((((a : ℕ) + 1 : ℕ) : fin (n + 1)), b) ∈ c) :
  (a, b) ∈ c ↔ ¬ (a, (((b : ℕ) + 1 : ℕ) : fin (n + 1))) ∈ c :=
begin
  revert hnalt,
  have hbal2a := hbal2 a b (by linarith) (by linarith),
  rw [sub_balanced_2 c a b ha hb, sub_black_2 c a b ha hb, cell_card_eq, cell_card_eq,
      cell_card_eq, cell_card_eq] at hbal2a,
  by_cases h1 : (a, b) ∈ c; by_cases h2 : (a, (((b : ℕ) + 1 : ℕ) : fin (n + 1))) ∈ c;
    by_cases h3 : ((((a : ℕ) + 1 : ℕ) : fin (n + 1)), b) ∈ c;
    by_cases h4 : ((((a : ℕ) + 1 : ℕ) : fin (n + 1)), (((b : ℕ) + 1 : ℕ) : fin (n + 1))) ∈ c,
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
theorem rows_not_alternate_any_two_cols {n : ℕ} (c : colouring (n + 1)) (hbal2 : balanced_k c 2)
    (a b : fin (n + 1)) (b1 : fin (n + 1)) (ha : (a : ℕ) < n) (hb1 : (b1 : ℕ) < n)
    (hnalt : (a, b) ∈ c ↔ ((((a : ℕ) + 1 : ℕ) : fin (n + 1)), b) ∈ c) :
  (a, b1) ∈ c ↔ ¬ (a, (((b1 : ℕ) + 1 : ℕ) : fin (n + 1))) ∈ c :=
begin
  refine rows_not_alternate_two_cols c hbal2 a b1 ha hb1 _,
  rw ←rows_alternate_any_two_cols' c hbal2 a b b1 ha,
  exact hnalt
end

-- If two rows fail to alternate in any column b, columns b1 and b1 +
-- 1 alternate everywhere.
theorem rows_not_alternate_any_two_cols_alt {n : ℕ} (c : colouring (n + 1))
    (hbal2 : balanced_k c 2) (a b : fin (n + 1)) (a1 b1 : fin (n + 1)) (ha : (a : ℕ) < n)
    (hb1 : (b1 : ℕ) < n) (hnalt : (a, b) ∈ c ↔ ((((a : ℕ) + 1 : ℕ) : fin (n + 1)), b) ∈ c) :
  (a1, b1) ∈ c ↔ ¬ (a1, (((b1 : ℕ) + 1 : ℕ) : fin (n + 1))) ∈ c :=
begin
  rw cols_alternate_any_two_rows c hbal2 b1 a1 a hb1,
  exact rows_not_alternate_any_two_cols c hbal2 a b b1 ha hb1 hnalt
end

-- Either all rows alternate, or all columns alternate.
theorem rows_alternate_or_cols_alternate {n : ℕ} (c : colouring (n + 1))
    (hbal2 : balanced_k c 2) :
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
theorem result_no_r_no_c (n : ℕ) : card (balanced_colourings_no_r_no_c n) = 0 :=
begin
  convert card_empty,
  unfold balanced_colourings_no_r_no_c balanced_colourings_no_r balanced_colourings,
  rw [filter_filter, filter_filter, eq_empty_iff_forall_not_mem],
  intro c,
  rw mem_filter,
  rintros ⟨hu, hb, hnr, hnc⟩,
  unfold not_rows_alternate at hnr,
  unfold not_cols_alternate at hnc,
  have hb2 : balanced_k c 2,
  { by_cases h2 : 2 ≤ n + 1,
    { exact hb 2 (by norm_num) h2 },
    { have hn0 : n = 0, { linarith },
      intros a b ha hb,
      linarith } },
  have hor := rows_alternate_or_cols_alternate c hb2,
  tauto
end

-- Thus the cardinality of the set of balanced colourings, in two parts.
theorem card_split_2 (n : ℕ) :
  card (balanced_colourings (n + 1)) = card (balanced_colourings_r_c n) +
    2 * card (balanced_colourings_r_no_c n) :=
begin
  rw [card_split_3, result_no_r_no_c, add_zero]
end

-- Now we need only consider balanced colourings where rows alternate.
-- These can be expressed as a function of their first row, so we can
-- reduce to counting first rows with certain properties.

abbreviation row (n : ℕ) := fin n

abbreviation row_colouring (n : ℕ) := finset (row n)

-- A row-alternating colouring of the grid as a function of the first
-- row.
def colouring_of_row_colouring {n : ℕ} (c : row_colouring n) : colouring n :=
finset.univ.filter (λ p : grid n, p.2 ∈ c ↔ (p.1 : ℕ) % 2 = 0)

-- The first row of the grid.
def row_colouring_of_colouring {n : ℕ} (c : colouring (n + 1)) : row_colouring (n + 1) :=
finset.univ.filter (λ p : row (n + 1), ((0 : fin (n + 1)), (p : fin (n + 1))) ∈ c)

-- A row-alternating colouring is given by its first row, induction.
theorem row_alternating_first_row {n : ℕ} (c : colouring (n + 1)) (h : rows_alternate c) (a : ℕ)
    (b : fin (n + 1)) (ha : a < n + 1) :
  ((a : fin (n + 1)), b) ∈ c ↔ (((0 : fin (n + 1)), b) ∈ c ↔ a % 2 = 0) :=
begin
  induction a with k hk,
  { norm_num },
  { rw ←not_iff_not,
    rw nat.succ_eq_add_one at ha,
    have hf : ((k : fin (n + 1)) : ℕ) = k :=
      fin.coe_coe_of_lt (show k < n + 1, by linarith only [ha]),
    have ha1 : ((k : fin (n + 1)) : ℕ) < n,
    { rw hf,
      linarith },
    have ha2 : nat.succ k = ((k : fin (n + 1)) : ℕ) + 1,
    { rw hf },
    have hkx := hk (by linarith),
    rw [ha2, ←h (k : fin (n + 1)) b ha1, hkx, hf, ←nat.even_iff, ←nat.even_iff, nat.even_add,
        nat.even_iff, nat.even_iff],
    norm_num,
    rw [←nat.not_even_iff, nat.even_iff],
    tauto }
end

-- A row-alternating colouring is given by its first row.
theorem row_alternating_first_row' {n : ℕ} (c : colouring (n + 1)) (h : rows_alternate c) :
  c = colouring_of_row_colouring (row_colouring_of_colouring c) :=
begin
  unfold colouring_of_row_colouring row_colouring_of_colouring,
  ext,
  split,
  { intro ha,
    rw [mem_filter, mem_filter],
    have hf : a = (((a.fst : ℕ) : fin (n + 1)), a.snd),
    { ext,
      { unfold prod.fst,
        rw fin.coe_coe_eq_self a.fst },
      { refl } },
    rw [hf, row_alternating_first_row c h a.fst a.snd a.fst.is_lt] at ha,
    rw ha,
    split,
    { exact mem_univ a },
    { have hu : a.snd ∈ univ := mem_univ a.snd,
      rw ←iff_true (a.snd ∈ univ) at hu,
      rw hu,
      tauto } },
  { intro ha,
    rw [mem_filter, mem_filter] at ha,
    cases ha with hau ha,
    have hu : a.snd ∈ univ := mem_univ a.snd,
    rw ←iff_true (a.snd ∈ univ) at hu,
    rw [hu, true_and] at ha,
    have hf : a = (((a.fst : ℕ) : fin (n + 1)), a.snd),
    { ext,
      { unfold prod.fst,
        rw fin.coe_coe_eq_self a.fst },
      { refl } },
    rw [hf, row_alternating_first_row c h a.fst a.snd a.fst.is_lt],
    exact ha }
end

-- colouring_of_row_colouring produces a row-alternating colouring.
theorem colouring_of_row_colouring_rows_alternate {n : ℕ} (c : row_colouring (n + 1)) :
  rows_alternate (colouring_of_row_colouring c) :=
begin
  unfold colouring_of_row_colouring,
  intros a b ha,
  have halt : (a : ℕ) + 1 < n + 1 := add_lt_add_right ha 1,
  erw mem_filter,
  erw mem_filter,
  unfold prod.fst prod.snd,
  split,
  { rintros ⟨hu, heq⟩ ⟨h2u, h2⟩,
    rw fin.coe_coe_of_lt halt at h2,
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
    { rw fin.coe_coe_of_lt halt at h2,
      rw ←nat.even_iff at *,
      rw nat.even_add at h2,
      norm_num at h2,
      rw [not_iff, not_iff_not] at h2,
      exact h2 } }
end

-- colouring_of_row_colouring is injective.
theorem colouring_of_row_colouring_injective (n : ℕ) :
  function.injective (@colouring_of_row_colouring (n + 1)) :=
begin
  apply function.has_left_inverse.injective,
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
def gives_balanced {n : ℕ} (c : row_colouring n) : Prop :=
balanced (colouring_of_row_colouring c)

-- Row colourings with alternating columns.
def row_cols_alternate {n : ℕ} (c : row_colouring (n + 1)) : Prop :=
∀ (a : fin (n + 1)) (h : (a : ℕ) < n), a ∈ c ↔ ¬ (((a : ℕ) + 1 : ℕ) : fin (n + 1)) ∈ c

-- Columns alternate in the whole grid if and only if they do in a
-- row.
theorem row_cols_alternate_iff_cols_alternate {n : ℕ} (c : row_colouring (n + 1)) :
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
    { simp at hb2,
      simpa [ha] },
    { rw [iff.comm, not_iff_comm] at hb2,
      simp at hb2,
      simpa [ha] } },
  { intros h a ha,
    have ha2 := h (0 : fin (n + 1)) a ha,
    unfold colouring_of_row_colouring at ha2,
    erw [mem_filter, mem_filter] at ha2,
    unfold prod.fst prod.snd at ha2,
    norm_num at ha2,
    simp [ha2] }
end

-- Convert the split into cases to one based on gives_balanced.

def row_not_cols_alternate {n : ℕ} (c : row_colouring (n + 1)) : Prop :=
¬ row_cols_alternate c

def gives_balanced_colourings (n : ℕ) : finset (row_colouring n) :=
finset.univ.filter gives_balanced

def gives_balanced_colourings_r_c (n : ℕ) : finset (row_colouring (n + 1)) :=
(gives_balanced_colourings (n + 1)).filter row_cols_alternate

def gives_balanced_colourings_r_no_c (n : ℕ) : finset (row_colouring (n + 1)) :=
(gives_balanced_colourings (n + 1)).filter row_not_cols_alternate

theorem card_r_c_eq_gives_rc (n : ℕ) :
  card (balanced_colourings_r_c n) = card (gives_balanced_colourings_r_c n) :=
begin
  convert card_image_of_injective (gives_balanced_colourings_r_c n)
    (colouring_of_row_colouring_injective n),
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
      exact ⟨⟨(mem_univ _), h.1.1.2⟩, h.2⟩ },
    { symmetry,
      apply row_alternating_first_row',
      unfold balanced_colourings_r_c balanced_colourings_r at h,
      rw [mem_filter, mem_filter] at h,
      exact h.1.2 } },
  { rintros ⟨rc, hrc, hcrc⟩,
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

theorem card_r_no_c_eq_gives_r_no_c (n : ℕ) :
  card (balanced_colourings_r_no_c n) = card (gives_balanced_colourings_r_no_c n) :=
begin
  convert card_image_of_injective (gives_balanced_colourings_r_no_c n)
    (colouring_of_row_colouring_injective n),
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
      exact ⟨⟨(mem_univ _), h.1.1.2⟩, h.2⟩ },
    { symmetry,
      apply row_alternating_first_row',
      unfold balanced_colourings_r_no_c balanced_colourings_r at h,
      rw [mem_filter, mem_filter] at h,
      exact h.1.2 } },
  { rintros ⟨rc, hrc, hcrc⟩,
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
theorem card_split_2_gives (n : ℕ) :
  card (balanced_colourings (n + 1)) = card (gives_balanced_colourings_r_c n) +
    2 * card (gives_balanced_colourings_r_no_c n) :=
begin
  rw [card_split_2, card_r_c_eq_gives_rc, card_r_no_c_eq_gives_r_no_c]
end

-- Next, show that the gives_balanced property is equivalent to a
-- balanced property for odd numbers of consecutive cells in the row,
-- so completing the reduction of the problem to be based on
-- properties of row colourings only.

-- The number of black cells in a subgrid equals the sum of the
-- numbers in a division of its rows into two parts.  (Note: the use
-- of fin (n + 1) for row numbers means this does not cover the case
-- where the first part of the split ends at the end of the grid.)
theorem sub_black_split_rows {n : ℕ} (c : colouring (n + 1)) (a b : fin (n + 1))
    (k1_1 k1_2 k2 : ℕ) (h : (a : ℕ) + k1_1 < n + 1) :
  sub_black c a b (k1_1 + k1_2) k2 =
    sub_black c a b k1_1 k2 + sub_black c (((a : ℕ) + k1_1 : ℕ) : fin (n + 1)) b k1_2 k2 :=
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
    { rintros ⟨hmc, hm⟩,
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
        { rw fin.le_iff_coe_le_coe at ha1,
          rw [fin.coe_coe_of_lt h] at ha1,
          rw fin.le_iff_coe_le_coe,
          linarith },
        { exact hb1 },
        { convert ha2 using 1,
          rw [fin.coe_coe_of_lt h, add_assoc] },
        { exact hb2 } } },
    { rintros ⟨hmc, ha1, hb1, ha2, hb2⟩,
      split,
      { exact hmc },
      { by_cases hx : (x.fst : ℕ) < (a : ℕ) + k1_1,
        { left,
          exact ⟨ha1, hb1, hx, hb2⟩ },
        { right,
          rw [fin.le_iff_coe_le_coe, fin.coe_coe_of_lt h],
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
      { rintros ⟨⟨ha1, hb1, ha2, hb2⟩, ⟨ha3, hb3, ha4, hb4⟩⟩,
        rw fin.le_iff_coe_le_coe at ha3,
        rw fin.coe_coe_of_lt h at ha3,
        linarith },
      { exact false.elim } },
    { exact classical.dec_pred _ } }
end

-- There are no black cells in zero rows.
theorem sub_black_zero_rows {n : ℕ} (c : colouring n) (a b : fin n) (k2 : ℕ) :
  sub_black c a b 0 k2 = 0 :=
begin
  unfold sub_black,
  convert card_empty,
  unfold subcolouring,
  convert filter_false c,
  { ext,
    split,
    { rintros ⟨ha1, hb1, ha2, hb2⟩,
      rw fin.le_iff_coe_le_coe at ha1,
      linarith },
    { exact false.elim } },
  { exact classical.dec_pred _ }
end

-- A subgrid of a row colouring.
def row_subcolouring {n : ℕ} (c : row_colouring n) (a : fin n) (k2 : ℕ) : finset (row n) :=
c.filter (λ p : row n, a ≤ p ∧ (p : ℕ) < (a : ℕ) + k2)

-- The complement of a row colouring.
def row_complement {n : ℕ} (c : row_colouring n) : row_colouring n :=
finset.univ \ c

-- The number of black cells in a subgrid of a row colouring.
def row_sub_black {n : ℕ} (c : row_colouring n) (a : fin n) (k2 : ℕ) : ℕ :=
finset.card (row_subcolouring c a k2)

-- The number of black cells in a subgrid of a row colouring and its
-- complement.
theorem row_sub_black_add_complement {n : ℕ} (c : row_colouring (n + 1)) (a : fin (n + 1))
    (k2 : ℕ) (hk2 : (a : ℕ) + k2 ≤ n + 1) :
  row_sub_black c a k2 + row_sub_black (row_complement c) a k2 = k2 :=
begin
  unfold row_sub_black row_complement row_subcolouring,
  rw [←card_union_add_card_inter, ←filter_union, filter_inter, inter_filter,
      union_sdiff_of_subset (subset_univ _), inter_sdiff_self, filter_empty, filter_empty,
      card_empty, add_zero],
  refine card_eq_of_bijective (λ i h, (((a : ℕ) + i : ℕ) : fin (n + 1))) _ _ _,
  { intros p hp,
    rw mem_filter at hp,
    use (p : ℕ) - a,
    rw fin.le_iff_coe_le_coe at hp,
    rcases hp with ⟨hpu, hpa, hpa2⟩,
    split,
    { exact (nat.sub_lt_left_iff_lt_add hpa).mpr hpa2 },
    { rw nat.add_sub_of_le hpa,
      exact fin.coe_coe_eq_self p } },
  { intros i hi,
    rw mem_filter,
    have hai : (a : ℕ) + i < n + 1, { linarith },
    rw [fin.le_iff_coe_le_coe, fin.coe_coe_of_lt hai],
    repeat { split },
    { exact mem_univ _ },
    { linarith },
    { linarith } },
  { intros i j hi hj,
    rw fin.ext_iff,
    have hai : (a : ℕ) + i < n + 1, { linarith },
    have haj : (a : ℕ) + j < n + 1, { linarith },
    rw [fin.coe_coe_of_lt hai, fin.coe_coe_of_lt haj],
    intro hij,
    exact nat.add_left_cancel hij }
end


-- The number of black cells in a subgrid of the complement of a row
-- colouring.
theorem row_sub_black_complement {n : ℕ} (c : row_colouring (n + 1)) (a : fin (n + 1)) (k2 : ℕ)
    (hk2 : (a : ℕ) + k2 ≤ n + 1) :
  row_sub_black (row_complement c) a k2 = k2 - row_sub_black c a k2 :=
begin
  conv_rhs { congr, rw ←row_sub_black_add_complement c a k2 hk2 },
  rw nat.add_sub_cancel_left
end

-- The number of black cells in an even row, derived from a row colouring.
theorem sub_black_even_row {n : ℕ} (c : row_colouring (n + 1)) (a b : fin (n + 1)) (k2 : ℕ)
    (ha : (a : ℕ) % 2 = 0) (hk2 : (b : ℕ) + k2 ≤ n + 1) :
  sub_black (colouring_of_row_colouring c) a b 1 k2 = (row_sub_black c b k2) :=
begin
  set f : row (n + 1) → grid (n + 1) := λ p, (a, p) with hf,
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
  { rintros ⟨hp, ha1, hb1, ha2, hb2⟩,
    unfold colouring_of_row_colouring at hp,
    rw mem_filter at hp,
    use p.snd,
    rw hf,
    rw mem_filter,
    unfold,
    cases hp with hpu hp,
    rw fin.le_iff_coe_le_coe at ha1,
    have hap : (p.fst : ℕ) = a,
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
  { rintros ⟨rp, hp, hp2⟩,
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
theorem sub_black_odd_row {n : ℕ} (c : row_colouring (n + 1)) (a b : fin (n + 1)) (k2 : ℕ)
    (ha : (a : ℕ) % 2 ≠ 0) (hk2 : (b : ℕ) + k2 ≤ n + 1) :
  sub_black (colouring_of_row_colouring c) a b 1 k2 = k2 - (row_sub_black c b k2) :=
begin
  set f : row (n + 1) → grid (n + 1) := λ p, (a, p) with hf,
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
  { rintros ⟨hp, ha1, hb1, ha2, hb2⟩,
    unfold colouring_of_row_colouring at hp,
    rw mem_filter at hp,
    use p.snd,
    rw hf,
    rw mem_filter,
    unfold,
    cases hp with hpu hp,
    rw fin.le_iff_coe_le_coe at ha1,
    have hap : (p.fst : ℕ) = a,
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
  { rintros ⟨rp, hp, hp2⟩,
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
theorem sub_black_one_row {n : ℕ} (c : row_colouring (n + 1)) (a b : fin (n + 1)) (k2 : ℕ)
    (hk2 : (b : ℕ) + k2 ≤ n + 1) :
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
theorem sub_black_two_rows {n : ℕ} (c : row_colouring (n + 1)) (a b : fin (n + 1)) (k2 : ℕ)
    (ha : (a : ℕ) < n) (hk2 : (b : ℕ) + k2 ≤ n + 1) :
  sub_black (colouring_of_row_colouring c) a b 2 k2 = k2 :=
begin
  rw sub_black_split_rows (colouring_of_row_colouring c) a b 1 1 k2
     (show (a : ℕ) + 1 < n + 1, by linarith),
  have hf : ((((a : ℕ) + 1 : ℕ) : fin (n + 1)) : ℕ) = (a : ℕ) + 1,
  { exact fin.coe_coe_of_lt (show (a : ℕ) + 1 < n + 1, by linarith) },
  have hle : row_sub_black c b k2 ≤ k2 := nat.le.intro (row_sub_black_add_complement c b k2 hk2),
  by_cases ha2 : (a : ℕ) % 2 = 0,
  { rw sub_black_even_row c a b k2 ha2 hk2,
    have ha1 : ((((a : ℕ) + 1 : ℕ) : fin (n + 1)) : ℕ) % 2 ≠ 0,
    { rw hf,
      intro ha3,
      rw ←nat.even_iff at *,
      rw nat.even_add at ha3,
      norm_num at ha3,
      exact ha3 ha2 },
    rw sub_black_odd_row c (((a : ℕ) + 1 : ℕ) : fin (n + 1)) b k2 ha1 hk2,
    apply nat.add_sub_cancel',
    exact hle },
  { rw sub_black_odd_row c a b k2 ha2 hk2,
    have ha1 : ((((a : ℕ) + 1 : ℕ) : fin (n + 1)) : ℕ) % 2 = 0,
    { rw hf,
      rw ←nat.even_iff at *,
      rw nat.even_add,
      norm_num,
      exact ha2 },
    rw sub_black_even_row c (((a : ℕ) + 1 : ℕ) : fin (n + 1)) b k2 ha1 hk2,
    apply nat.sub_add_cancel,
    exact hle },
end

-- The number of black cells in an even number of rows, derived from a
-- row colouring.
theorem sub_black_even_rows {n : ℕ} (c : row_colouring (n + 1)) (a b : fin (n + 1)) (k1 k2 : ℕ)
    (h : (a : ℕ) + (2 * k1) ≤ n + 1) (hk2 : (b : ℕ) + k2 ≤ n + 1) :
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
      have ha : ((a : ℕ) + 2 * k1a) < n + 1, { linarith },
      rw fin.coe_coe_of_lt ha,
      linarith },
    { rw nat.succ_eq_add_one at h,
      linarith } }
end

-- The number of black cells in an odd number of rows, derived from a
-- row colouring.
theorem sub_black_odd_rows {n : ℕ} (c : row_colouring (n + 1)) (a b : fin (n + 1)) (k1 k2 : ℕ)
    (h : (a : ℕ) + (2 * k1 + 1) ≤ n + 1) (hk2 : (b : ℕ) + k2 ≤ n + 1) :
  sub_black (colouring_of_row_colouring c) a b (2 * k1 + 1) k2 =
    (ite ((a : ℕ) % 2 = 0) (row_sub_black c b k2) (k2 - (row_sub_black c b k2))) + k1 * k2 :=
begin
  by_cases ha : (a : ℕ) + 1 < n + 1,
  { convert sub_black_split_rows (colouring_of_row_colouring c) a b 1 (2 * k1) k2 _ using 1,
    { congr' 1,
      ring },
    { rw ←sub_black_one_row c a b k2 hk2,
      rw sub_black_even_rows c _ b k1 k2 _ hk2,
      rw fin.coe_coe_of_lt ha,
      linarith },
    { linarith } },
  { have hk1 : k1 = 0, { linarith },
    have ha2 : (a : ℕ) = n, { linarith },
    rw [hk1, ha2],
    norm_num,
    rw [sub_black_one_row _ _ _ _ hk2, ha2] }
end

-- colouring_of_row_colouring gives colourings balanced for subgrids
-- of even side.
theorem gives_balanced_even {n : ℕ} (c : row_colouring (n + 1)) (k : ℕ) :
  balanced_k (colouring_of_row_colouring c) (2 * k) :=
begin
  intros a b ha hb,
  unfold sub_balanced,
  rw imbalance_eq _ _ _ _ ha hb,
  rw sub_black_even_rows _ _ _ _ _ ha hb,
  simp [mul_assoc]
end

-- The imbalance of an odd subgrid of a row.
def row_odd_imbalance {n : ℕ} (c : row_colouring n) (a : fin n) (k : ℕ)
    (ha : (a : ℕ) + (2 * k + 1) ≤ n) : ℕ :=
int.nat_abs (2 * ((row_sub_black c a (2 * k + 1)) : ℤ) - ((2 * k + 1) : ℤ))

-- Whether odd subgrids of a row are balanced.
def row_odd_balanced_k {n : ℕ} (c : row_colouring n) (k : ℕ) : Prop :=
∀ (a : fin n) (ha : ((a : ℕ) + (2 * k + 1)) ≤ n), row_odd_imbalance c a k ha ≤ 1

-- The imbalance of a square subgrid of odd side equals the
-- corresponding imbalance for a row.
theorem imbalance_odd_eq {n : ℕ} (c : row_colouring (n + 1)) (a b : fin (n + 1)) (k : ℕ)
    (ha : (a : ℕ) + (2 * k + 1) ≤ n + 1) (hb : (b : ℕ) + (2 * k + 1) ≤ n + 1) :
  sub_imbalance (colouring_of_row_colouring c) a b (2 * k + 1) = row_odd_imbalance c b k hb :=
begin
  rw [imbalance_eq _ _ _ _ ha hb, sub_black_odd_rows _ _ _ _ _ ha hb],
  unfold row_odd_imbalance,
  by_cases hae : ((a : ℕ) % 2 = 0),
  { rw if_pos hae,
    congr' 1,
    push_cast,
    ring },
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
    ring }
end

-- colouring_of_row_colouring gives colourings balanced for subgrids
-- of odd side if and only if their row_odd_imbalance is at most 1.
theorem gives_balanced_odd_iff {n : ℕ} (c : row_colouring (n + 1)) (k : ℕ) :
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
def row_balanced {n : ℕ} (c : row_colouring (n + 1)) : Prop :=
∀ k : ℕ, 2 * k ≤ n → row_odd_balanced_k c k

-- A row is gives_balanced if and only if it is row_balanced.
theorem gives_balanced_iff_row_balanced {n : ℕ} (c : row_colouring (n + 1)) :
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

def row_balanced_colourings (n : ℕ) : finset (row_colouring (n + 1)) :=
finset.univ.filter row_balanced

theorem gives_balanced_eq_row_balanced (n : ℕ) :
  gives_balanced_colourings (n + 1) = row_balanced_colourings n :=
begin
  unfold gives_balanced_colourings row_balanced_colourings,
  ext,
  rw [mem_filter, mem_filter],
  rw gives_balanced_iff_row_balanced
end

def row_balanced_colourings_r_c (n : ℕ) : finset (row_colouring (n + 1)) :=
(row_balanced_colourings n).filter row_cols_alternate

def row_balanced_colourings_r_no_c (n : ℕ) : finset (row_colouring (n + 1)) :=
(row_balanced_colourings n).filter row_not_cols_alternate

theorem card_gives_balanced_r_c_eq (n : ℕ) :
  card (gives_balanced_colourings_r_c n) = card (row_balanced_colourings_r_c n) :=
begin
  unfold gives_balanced_colourings_r_c row_balanced_colourings_r_c,
  rw gives_balanced_eq_row_balanced
end

theorem card_gives_balanced_r_no_c_eq (n : ℕ) :
  card (gives_balanced_colourings_r_no_c n) = card (row_balanced_colourings_r_no_c n) :=
begin
  unfold gives_balanced_colourings_r_no_c row_balanced_colourings_r_no_c,
  rw gives_balanced_eq_row_balanced
end

-- Thus the cardinality of the set of balanced colourings, in two
-- parts based on row_balanced.
theorem card_split_2_row (n : ℕ) :
  card (balanced_colourings (n + 1)) = card (row_balanced_colourings_r_c n) +
    2 * card (row_balanced_colourings_r_no_c n) :=
begin
  rw [card_split_2_gives, card_gives_balanced_r_c_eq, card_gives_balanced_r_no_c_eq]
end

-- The next aim is to prove that a row colouring is row_balanced if
-- and only if the positions (between two cells) where the colour does
-- *not* change all have the same parity.

-- The number of black cells in columns of a row, split into two
-- parts.
theorem row_sub_black_split_cols {n : ℕ} (c : row_colouring (n + 1)) (a : fin (n + 1))
    (k2_1 k2_2 : ℕ) (h : (a : ℕ) + k2_1 < n + 1) :
  row_sub_black c a (k2_1 + k2_2) =
    row_sub_black c a k2_1 + row_sub_black c (((a : ℕ) + k2_1 : ℕ) : fin (n + 1)) k2_2 :=
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
    { rintros ⟨hmc, hm⟩,
      cases hm,
      { repeat { split },
        { exact hmc },
        { exact hm.1 },
        { linarith } },
      { repeat { split },
        { exact hmc },
        { cases hm with hm1 hm2,
          rw [fin.le_iff_coe_le_coe, fin.coe_coe_of_lt h] at hm1,
          rw fin.le_iff_coe_le_coe,
          linarith },
        { cases hm with hm1 hm2,
          rw [fin.coe_coe_of_lt h, add_assoc] at hm2,
          exact hm2 } } },
    { rintros ⟨hmc, ha1, ha2⟩,
      split,
      { exact hmc },
      { by_cases hx : (x : ℕ) < (a : ℕ) + k2_1,
        { left,
          exact ⟨ha1, hx⟩ },
        { right,
          rw not_lt at hx,
          split,
          { rw [fin.le_iff_coe_le_coe, fin.coe_coe_of_lt h],
            exact hx },
          { convert ha2 using 1,
            rw [fin.coe_coe_of_lt h, add_assoc] } } } } },
  { convert card_empty,
    unfold row_subcolouring,
    rw ←filter_and,
    convert filter_false c,
    { ext,
      split,
      { rintros ⟨⟨ha1, ha2⟩, ha3, ha4⟩,
        rw fin.le_iff_coe_le_coe at ha1,
        rw [fin.le_iff_coe_le_coe, fin.coe_coe_of_lt h] at ha3,
        linarith },
      { exact false.elim } },
    { exact classical.dec_pred _ } }
end

-- There are no black cells in zero columns.
theorem row_sub_black_zero_cols {n : ℕ} (c : row_colouring n) (a : fin n) :
  row_sub_black c a 0 = 0 :=
begin
  unfold row_sub_black,
  convert card_empty,
  unfold row_subcolouring,
  convert filter_false c,
  { ext,
    split,
    { rintros ⟨h1, h2⟩,
      rw fin.le_iff_coe_le_coe at h1,
      linarith },
    { exact false.elim } },
  { exact classical.dec_pred _ }
end

-- The number of black cells in one column.
theorem row_sub_black_one_col {n : ℕ} (c : row_colouring n) (a : fin n) :
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
    { rintros ⟨hxc, hxa1, hxa2⟩,
      rw fin.le_iff_coe_le_coe at hxa1,
      have hxa : (x : ℕ) = a, { linarith },
      rw ←fin.ext_iff at hxa,
      exact hxa },
    { rintros rfl,
      exact ⟨h, le_rfl, (by linarith)⟩ } },
  { rw if_neg h,
    convert card_empty,
    unfold row_subcolouring,
    ext x,
    rw mem_filter,
    split,
    { rintros ⟨hxc, hxa1, hxa2⟩,
      rw fin.le_iff_coe_le_coe at hxa1,
      have hxa : (x : ℕ) = a, { linarith },
      rw ←fin.ext_iff at hxa,
      rw hxa at hxc,
      contradiction },
    { exact false.elim } }
end

-- The colour of individual cells in columns of a row that alternate
-- in colour.
theorem row_cols_alternate_colour {n : ℕ} (c : row_colouring (n + 1)) (a : fin (n + 1)) (k2 : ℕ)
    (hk2 : (a : ℕ) + k2 ≤ n + 1)
    (halt : ∀ k : ℕ, k + 1 < k2 →
      ((((a : ℕ) + k : ℕ) : fin (n + 1)) ∈ c ↔ ¬ (((a : ℕ) + k + 1 : ℕ) : fin (n + 1)) ∈ c)) :
  ∀ k : ℕ, k < k2 → ((((a : ℕ) + k : ℕ) : fin (n + 1)) ∈ c ↔ (a ∈ c ↔ k % 2 = 0)) :=
begin
  intro k,
  induction k with x hx,
  { intro h0,
    simp },
  { intro hx2,
    rw nat.succ_eq_add_one at hx2,
    have hx3 : x < k2, { linarith },
    have hx4 := hx hx3,
    have hax := halt x hx2,
    conv { congr, congr, congr, rw [nat.succ_eq_add_one, ←add_assoc] },
    rw [←nat.even_iff, nat.even_succ, nat.even_iff],
    tauto }
end

-- The number of black cells in columns of a row that alternate in
-- colour.
theorem row_sub_black_cols_alternate {n : ℕ} (c : row_colouring (n + 1)) (a : fin (n + 1))
    (k2 : ℕ) (hk2 : (a : ℕ) + k2 ≤ n + 1)
    (halt : ∀ k : ℕ, k + 1 < k2 →
      ((((a : ℕ) + k : ℕ) : fin (n + 1)) ∈ c ↔ ¬ (((a : ℕ) + k + 1 : ℕ) : fin (n + 1)) ∈ c)) :
  row_sub_black c a k2 = ite (a ∈ c) ((k2 + 1) / 2) (k2 / 2) :=
begin
  induction k2 with x hx,
  { norm_num,
    exact row_sub_black_zero_cols c a },
  { conv_lhs { rw nat.succ_eq_add_one },
    rw [row_sub_black_split_cols c a x 1 hk2, row_sub_black_one_col _ _],
    rw hx _ _,
    { conv_lhs
      { congr, skip, congr,
        rw row_cols_alternate_colour c a (nat.succ x) hk2 halt x (nat.lt_succ_self x) },
      conv_rhs { rw nat.succ_eq_add_one x },
      by_cases h : a ∈ c; by_cases he : even x,
      { conv_lhs { congr, skip, congr, rw ←nat.even_iff },
        rw [if_pos h, if_pos h],
        conv_lhs { congr, skip, congr, rw iff_true_intro (iff_of_true h he) },
        rw if_true,
        rw nat.even_iff at he,
        rw [←nat.mod_add_div x 2, he, zero_add, add_assoc],
        conv_lhs { congr, congr, rw add_comm },
        rw nat.add_mul_div_left _ _ (dec_trivial : 2 > 0),
        conv_rhs { rw add_comm },
        rw nat.add_mul_div_left _ _ (dec_trivial : 2 > 0),
        norm_num,
        exact add_comm _ _ },
      { conv_lhs { congr, skip, congr, rw ←nat.even_iff },
        rw [if_pos h, if_pos h],
        have hn: ¬ (a ∈ c ↔ even x), { tauto },
        conv_lhs { congr, skip, congr, rw iff_false_intro hn },
        rw if_false,
        rw nat.not_even_iff at he,
        rw [←nat.mod_add_div x 2, he, add_zero],
        conv_lhs { rw [add_comm, ←add_assoc, nat.add_mul_div_left _ _ (dec_trivial : 2 > 0)] },
        rw [(show 1 + 2 * (x / 2) + 1 + 1 = 3 + 2 * (x / 2), by ring),
            nat.add_mul_div_left _ _ (dec_trivial : 2 > 0)],
        norm_num },
      { conv_lhs { congr, skip, congr, rw ←nat.even_iff },
        rw [if_neg h, if_neg h],
        have hn: ¬ (a ∈ c ↔ even x), { tauto },
        conv_lhs { congr, skip, congr, rw iff_false_intro hn },
        rw if_false,
        rw nat.even_iff at he,
        rw [←nat.mod_add_div x 2, he, add_zero, zero_add,
            nat.mul_div_cancel_left _ (dec_trivial : 2 > 0), add_comm,
            nat.add_mul_div_left _ _ (dec_trivial : 2 > 0)],
        norm_num },
      { conv_lhs { congr, skip, congr, rw ←nat.even_iff },
        rw [if_neg h, if_neg h],
        have hn: (a ∈ c ↔ even x), { tauto },
        conv_lhs { congr, skip, congr, rw iff_true_intro hn },
        rw if_true,
        rw nat.not_even_iff at he,
        rw [←nat.mod_add_div x 2, he, nat.add_mul_div_left _ _ (dec_trivial : 2 > 0)],
        conv_rhs { rw add_assoc, congr, congr, skip, rw add_comm },
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
theorem row_sub_black_even_cols_alternate {n : ℕ} (c : row_colouring (n + 1)) (a : fin (n + 1))
    (k2 : ℕ) (hk2 : (a : ℕ) + 2 * k2 ≤ n + 1)
    (halt : ∀ k : ℕ, k < k2 →
      ((((a : ℕ) + 2 * k : ℕ) : fin (n + 1)) ∈ c ↔
        ¬ (((a : ℕ) + 2 * k + 1 : ℕ) : fin (n + 1)) ∈ c)) :
  row_sub_black c a (2 * k2) = k2 :=
begin
  induction k2 with k2x hk2x,
  { norm_num,
    exact row_sub_black_zero_cols c a },
  { rw [nat.succ_eq_add_one, nat.left_distrib],
    norm_num,
    rw [nat.succ_eq_add_one, nat.left_distrib] at hk2,
    have ha : (a : ℕ) + 2 * k2x < n + 1, { linarith },
    rw row_sub_black_split_cols _ _ _ _ ha,
    { congr,
      { apply hk2x,
        { exact le_of_lt ha },
        { intros k hk,
          have hks : k < nat.succ k2x, { exact nat.lt.step hk },
          exact halt k hks } },
      { convert row_sub_black_cols_alternate c (((a : ℕ) + 2 * k2x : ℕ) : fin (n + 1)) 2 _ _,
        { norm_num },
        { rw fin.coe_coe_of_lt ha,
          norm_num at hk2,
          rw add_assoc,
          exact hk2 },
        { intros k hk,
          rw fin.coe_coe_of_lt ha,
          have hk0 : k = 0, { linarith },
          rw hk0,
          apply halt,
          exact nat.lt_succ_self k2x } } } }
end

-- The number of black cells in an odd number of columns of a row,
-- where pairs in even positions (relative to the starting point of
-- those columns) alternate in colour.
theorem row_sub_black_odd_cols_alternate_0 {n : ℕ} (c : row_colouring (n + 1)) (a : fin (n + 1))
    (k2 : ℕ) (hk2 : (a : ℕ) + 2 * k2 + 1 ≤ n + 1)
    (halt : ∀ k : ℕ, k < k2 →
      ((((a : ℕ) + 2 * k : ℕ) : fin (n + 1)) ∈ c ↔
        ¬ (((a : ℕ) + 2 * k + 1 : ℕ) : fin (n + 1)) ∈ c)) :
  row_sub_black c a (2 * k2 + 1) =
    ite ((((a : ℕ) + 2 * k2 : ℕ) : fin (n + 1)) ∈ c) (k2 + 1) k2 :=
begin
  rw [row_sub_black_split_cols _ _ _ _ hk2, row_sub_black_one_col],
  have hk2a : (a : ℕ) + 2 * k2 ≤ n + 1, { linarith },
  rw row_sub_black_even_cols_alternate _ _ _ hk2a halt,
  by_cases h : (((a : ℕ) + 2 * k2 : ℕ) : fin (n + 1)) ∈ c,
  { rw [if_pos h, if_pos h] },
  { rw [if_neg h, if_neg h, add_zero] }
end

-- Thus, the odd imbalance in that case.
theorem row_odd_imbalance_cols_alternate_0 {n : ℕ} (c : row_colouring (n + 1)) (a : fin (n + 1))
    (k2 : ℕ) (hk2 : (a : ℕ) + 2 * k2 + 1 ≤ n + 1)
    (halt : ∀ k : ℕ, k < k2 →
      ((((a : ℕ) + 2 * k : ℕ) : fin (n + 1)) ∈ c ↔
        ¬ (((a : ℕ) + 2 * k + 1 : ℕ) : fin (n + 1)) ∈ c)) :
  row_odd_imbalance c a k2 hk2 = 1 :=
begin
  unfold row_odd_imbalance,
  rw row_sub_black_odd_cols_alternate_0 c a k2 hk2 halt,
  by_cases h : (((a : ℕ) + 2 * k2 : ℕ) : fin (n + 1)) ∈ c,
  { rw if_pos h,
    push_cast,
    ring },
  { rw if_neg h,
    ring }
end

-- The number of black cells in an odd number of columns of a row,
-- where pairs in odd positions (relative to the starting point of
-- those columns) alternate in colour.
theorem row_sub_black_odd_cols_alternate_1 {n : ℕ} (c : row_colouring (n + 1)) (a : fin (n + 1))
    (k2 : ℕ) (hk2 : (a : ℕ) + 2 * k2 + 1 ≤ n + 1)
    (halt : ∀ k : ℕ, k < k2 → ((((a : ℕ) + 1 + 2 * k : ℕ) : fin (n + 1)) ∈ c ↔
                                ¬ (((a : ℕ) + 1 + 2 * k + 1 : ℕ) : fin (n + 1)) ∈ c)) :
  row_sub_black c a (2 * k2 + 1) = ite (a ∈ c) (k2 + 1) k2 :=
begin
  rw add_comm (2 * k2) 1,
  by_cases h0 : k2 = 0,
  { rw h0,
    norm_num,
    exact row_sub_black_one_col _ _ },
  { have hk2pos : 0 < k2 := nat.pos_of_ne_zero h0,
    have hk2a : (a : ℕ) + 1 < n + 1, { linarith },
    rw [row_sub_black_split_cols _ _ _ _ hk2a, row_sub_black_one_col],
    rw [add_assoc, add_comm (2 * k2) 1, ←add_assoc, ←fin.coe_coe_of_lt hk2a] at hk2,
    rw row_sub_black_even_cols_alternate _ _ _ hk2 _,
    { by_cases h : a ∈ c,
      { rw [if_pos h, if_pos h],
        exact add_comm _ _ },
      { rw [if_neg h, if_neg h, zero_add] }  },
    { intros k hk,
      rw fin.coe_coe_of_lt hk2a,
      exact halt k hk } }
end

-- Thus, the odd imbalance in that case.
theorem row_odd_imbalance_cols_alternate_1 {n : ℕ} (c : row_colouring (n + 1)) (a : fin (n + 1))
    (k2 : ℕ) (hk2 : (a : ℕ) + 2 * k2 + 1 ≤ n + 1)
    (halt : ∀ k : ℕ, k < k2 → ((((a : ℕ) + 1 + 2 * k : ℕ) : fin (n + 1)) ∈ c ↔
                                ¬ (((a : ℕ) + 1 + 2 * k + 1 : ℕ) : fin (n + 1)) ∈ c)) :
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
def row_cols_alternate_at_parity {n : ℕ} (c : row_colouring (n + 1)) (parity : ℕ) : Prop :=
∀ k : ℕ, k < n → k % 2 = parity → ((k : fin (n + 1)) ∈ c ↔ ¬ ((k + 1 : ℕ) : fin (n + 1)) ∈ c)

-- The columns of a row always alternate at some parity.
def row_cols_alternate_some_parity {n : ℕ} (c : row_colouring (n + 1)) : Prop :=
row_cols_alternate_at_parity c 0 ∨ row_cols_alternate_at_parity c 1

-- If the columns of a row always alternate at some parity, it is
-- row_balanced.
theorem row_balanced_if_row_cols_alternate_at_some_parity {n : ℕ} (c : row_colouring (n + 1))
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
theorem row_cols_alternate_ends_middle_alt {n : ℕ} (c : row_colouring (n + 1)) (a : fin (n + 1))
    (k2 : ℕ) (hk2 : (a : ℕ) + 2 * k2 + 3 ≤ n + 1)
    (halt : ∀ k : ℕ, 0 < k → k < 2 * k2 + 1 →
      ((((a : ℕ) + k : ℕ) : fin (n + 1)) ∈ c ↔ ¬ (((a : ℕ) + k + 1 : ℕ) : fin (n + 1)) ∈ c)) :
  ∀ (k : ℕ), k + 1 < 2 * k2 + 1 →
    ((((a : ℕ) + 1 + k : ℕ) : fin (n + 1)) ∈ c ↔
      ¬ (((a : ℕ) + 1 + k + 1 : ℕ) : fin (n + 1)) ∈ c) :=
begin
  intros k hk,
  rw (show (a : ℕ) + 1 + k = (a : ℕ) + (k + 1), by ring),
  apply halt (k + 1),
  { linarith },
  { exact hk }
end

-- The number of black cells in an odd number of columns of a row that
-- alternate in colour except at the ends.
theorem row_sub_black_cols_alternate_ends {n : ℕ} (c : row_colouring (n + 1)) (a : fin (n + 1))
    (k2 : ℕ) (hk2 : (a : ℕ) + 2 * k2 + 3 ≤ n + 1)
    (halt : ∀ k : ℕ, 0 < k → k < 2 * k2 + 1 →
                     ((((a : ℕ) + k : ℕ) : fin (n + 1)) ∈ c ↔
                      ¬ (((a : ℕ) + k + 1 : ℕ) : fin (n + 1)) ∈ c))
    (hnalt1 : a ∈ c ↔ (((a : ℕ) + 1 : ℕ) : fin (n + 1)) ∈ c)
    (hnalt2 : (((a : ℕ) + 2 * k2 + 1 : ℕ) : fin (n + 1)) ∈ c ↔
               (((a : ℕ) + 2 * k2 + 2 : ℕ) : fin (n + 1)) ∈ c) :
  row_sub_black c a (2 * k2 + 3) = ite (a ∈ c) (k2 + 3) k2 :=
begin
  rw (show 2 * k2 + 3 = 1 + (2 * k2 + 1) + 1, by ring),
  have hs1 : (a : ℕ) + (1 + (2 * k2 + 1)) < n + 1, { linarith },
  rw [row_sub_black_split_cols _ _ _ _ hs1, row_sub_black_one_col,
      (show (a : ℕ) + (1 + (2 * k2 + 1)) = (a : ℕ) + 2 * k2 + 2, by ring)],
  have hs2 : (a : ℕ) + 1 < n + 1, { linarith },
  have hendcol : (((a : ℕ) + 2 * k2 + 2 : ℕ) : fin (n + 1)) ∈ c ↔ a ∈ c,
  { rw [hnalt1, ←hnalt2, (show (a : ℕ) + 2 * k2 + 1 = (a : ℕ) + 1 + 2 * k2, by ring)],
    conv_lhs { congr, congr, rw ←fin.coe_coe_of_lt hs2 },
    rw row_cols_alternate_colour c (((a : ℕ) + 1 : ℕ) : fin (n + 1)) (2 * k2 + 1) _ _ (2 * k2) _,
    all_goals { try { rw fin.coe_coe_of_lt hs2 } },
    { simp },
    { linarith },
    { exact row_cols_alternate_ends_middle_alt c a k2 hk2 halt },
    { linarith } },
  conv_lhs { congr, skip, congr, rw hendcol },
  rw [row_sub_black_split_cols _ _ _ _ hs2, row_sub_black_one_col],
  rw row_sub_black_cols_alternate c (((a : ℕ) + 1 : ℕ) : fin (n + 1)) (2 * k2 + 1) _ _,
  all_goals { try { rw fin.coe_coe_of_lt hs2 } },
  { conv_lhs { congr, congr, skip, congr, rw ←hnalt1 },
    by_cases h : a ∈ c,
    { simp [h, (show 2 * k2 + 1 + 1 = 2 * (k2 + 1), by ring)],
      ring },
    { conv_lhs
      { congr, congr, skip, congr, skip, skip,
        rw [add_comm, nat.add_mul_div_left 1 k2 (show 2 > 0, by norm_num)],
        norm_num },
      simp [h] } },
  { linarith },
  { exact row_cols_alternate_ends_middle_alt c a k2 hk2 halt }
end

-- Thus, the odd imbalance in that case.
theorem row_odd_imbalance_cols_alternate_ends {n : ℕ} (c : row_colouring (n + 1))
    (a : fin (n + 1)) (k2 : ℕ) (hk2 : (a : ℕ) + 2 * k2 + 3 ≤ n + 1)
    (halt : ∀ k : ℕ, 0 < k → k < 2 * k2 + 1 →
      ((((a : ℕ) + k : ℕ) : fin (n + 1)) ∈ c ↔ ¬ (((a : ℕ) + k + 1 : ℕ) : fin (n + 1)) ∈ c))
    (hnalt1 : a ∈ c ↔ (((a : ℕ) + 1 : ℕ) : fin (n + 1)) ∈ c)
    (hnalt2 : (((a : ℕ) + 2 * k2 + 1 : ℕ) : fin (n + 1)) ∈ c ↔
      (((a : ℕ) + 2 * k2 + 2 : ℕ) : fin (n + 1)) ∈ c) :
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

-- Thus, not row_balanced in that case.
theorem not_row_balanced_cols_alternate_ends {n : ℕ} (c : row_colouring (n + 1))
    (a : fin (n + 1)) (k2 : ℕ) (hk2 : (a : ℕ) + 2 * k2 + 3 ≤ n + 1)
    (halt : ∀ k : ℕ, 0 < k → k < 2 * k2 + 1 →
      ((((a : ℕ) + k : ℕ) : fin (n + 1)) ∈ c ↔ ¬ (((a : ℕ) + k + 1 : ℕ) : fin (n + 1)) ∈ c))
    (hnalt1 : a ∈ c ↔ (((a : ℕ) + 1 : ℕ) : fin (n + 1)) ∈ c)
    (hnalt2 : (((a : ℕ) + 2 * k2 + 1 : ℕ) : fin (n + 1)) ∈ c ↔
      (((a : ℕ) + 2 * k2 + 2 : ℕ) : fin (n + 1)) ∈ c) :
  ¬ row_balanced c :=
begin
  intro hbal,
  have hbal2 := hbal (k2 + 1) (by linarith) a hk2,
  rw row_odd_imbalance_cols_alternate_ends c a k2 hk2 halt hnalt1 hnalt2 at hbal2,
  norm_num at hbal2
end

-- Given two non-alternating places an odd distance apart, we can find
-- such places for which the columns alternate in between.
theorem row_middle_alt_if_not_alternate_ends {n : ℕ} (c : row_colouring (n + 1))
    (a : fin (n + 1)) (k2 : ℕ) (hk2 : (a : ℕ) + 2 * k2 + 3 ≤ n + 1)
    (hnalt1 : a ∈ c ↔ (((a : ℕ) + 1 : ℕ) : fin (n + 1)) ∈ c)
    (hnalt2 : (((a : ℕ) + 2 * k2 + 1 : ℕ) : fin (n + 1)) ∈ c ↔
      (((a : ℕ) + 2 * k2 + 2 : ℕ) : fin (n + 1)) ∈ c) :
  ∃ (b : fin (n + 1)) (k3 : ℕ), (b : ℕ) + 2 * k3 + 3 ≤ n + 1 ∧
    (∀ k : ℕ, 0 < k → k < 2 * k3 + 1 →
      ((((b : ℕ) + k : ℕ) : fin (n + 1)) ∈ c ↔ ¬ (((b : ℕ) + k + 1 : ℕ) : fin (n + 1)) ∈ c)) ∧
    (b ∈ c ↔ (((b : ℕ) + 1 : ℕ) : fin (n + 1)) ∈ c) ∧
    ((((b : ℕ) + 2 * k3 + 1 : ℕ) : fin (n + 1)) ∈ c ↔
      (((b : ℕ) + 2 * k3 + 2 : ℕ) : fin (n + 1)) ∈ c) :=
begin
  induction k2 using nat.case_strong_induction_on with k2a hk2a generalizing a,
  { use [a, 0, hk2],
    split,
    { intros k hk0 hk1,
      exfalso,
      linarith },
    { exact ⟨hnalt1, hnalt2⟩ } },
  { by_cases hnalt : ∃ k : ℕ, 0 < k ∧ k < 2 * (nat.succ k2a) + 1 ∧
        ((((a : ℕ) + k : ℕ) : fin (n + 1)) ∈ c ↔ (((a : ℕ) + k + 1 : ℕ) : fin (n + 1)) ∈ c),
    { rcases hnalt with ⟨k, hk0, hk1, halt⟩,
      by_cases hpar : k % 2 = 0,
      { set k3 := k / 2 with hk3,
        have hk3a : 2 * k3 = k,
        { rw ←nat.dvd_iff_mod_eq_zero at hpar,
          rw [hk3, nat.mul_div_cancel' hpar] },
        set a2 : fin (n + 1) := (((a : ℕ) + 2 * k3 : ℕ) : fin (n + 1)) with ha2,
        have ha2a : (a : ℕ) + 2 * k3 < n + 1,
        { rw hk3a,
          linarith only [hk1, hk2] },
        set k4 : ℕ := nat.succ k2a - k3 with hk4,
        have hk3b : k3 ≤ nat.succ k2a,
        { rw ←hk3a at hk1,
          linarith only [hk1] },
        have hk3c : 1 ≤ k3,
        { linarith only [hk0, hk3a] },
        have hk4b : k4 ≤ k2a,
        { rw [hk4, nat.succ_eq_add_one],
          apply nat.sub_le_right_of_le_add,
          linarith only [hk3c] },
        have hk4c : k4 + k3 = nat.succ k2a,
        { rw hk4,
          apply nat.sub_add_cancel,
          exact hk3b },
        have hk4d : (a2 : ℕ) + 2 * k4 + 3 ≤ n + 1,
        { rw [ha2, fin.coe_coe_of_lt ha2a,
              (show (a : ℕ) + 2 * k3 + 2 * k4 = (a : ℕ) + 2 * (k4 + k3), by ring), hk4c],
          exact hk2 },
        rw [←hk3a, ←ha2, ←fin.coe_coe_of_lt ha2a, ←ha2] at halt,
        apply hk2a k4 hk4b a2 hk4d halt,
        rw [ha2, fin.coe_coe_of_lt ha2a,
            (show (a : ℕ) + 2 * k3 + 2 * k4 = (a : ℕ) + 2 * (k4 + k3), by ring), hk4c],
        exact hnalt2 },
      { rw [←nat.even_iff, nat.not_even_iff] at hpar,
        set k3 := k / 2 with hk3,
        have hk3a : 2 * k3 + 1 = k,
        { rw [hk3, add_comm],
          conv_lhs { congr, rw ←hpar },
          rw nat.mod_add_div },
        have hk3b : k3 ≤ k2a,
        { rw [←hk3a, nat.succ_eq_add_one] at hk1,
          linarith only [hk1] },
        rw [←hk3a, ←add_assoc,
            (show (a : ℕ) + 2 * k3 + 1 + 1 = (a : ℕ) + 2 * k3 + 2, by ring)] at halt,
        exact hk2a k3 hk3b a (by linarith) hnalt1 halt } },
    { use [a, nat.succ k2a, hk2],
      rw not_exists at hnalt,
      split,
      { intros k hk0 hk1,
        rw [iff.comm, ←not_iff, iff.comm],
        intro halt,
        exact hnalt k ⟨hk0, hk1, halt⟩ },
      { exact ⟨hnalt1, hnalt2⟩ } } }
end

-- Thus, not row_balanced in that case.
theorem not_row_balanced_if_not_alternate_ends {n : ℕ} (c : row_colouring (n + 1))
    (a : fin (n + 1)) (k2 : ℕ) (hk2 : (a : ℕ) + 2 * k2 + 3 ≤ n + 1)
    (hnalt1 : a ∈ c ↔ (((a : ℕ) + 1 : ℕ) : fin (n + 1)) ∈ c)
    (hnalt2 : (((a : ℕ) + 2 * k2 + 1 : ℕ) : fin (n + 1)) ∈ c ↔
      (((a : ℕ) + 2 * k2 + 2 : ℕ) : fin (n + 1)) ∈ c) :
  ¬ row_balanced c :=
begin
  have h := row_middle_alt_if_not_alternate_ends c a k2 hk2 hnalt1 hnalt2,
  rcases h with ⟨b, k3, ⟨hk3, halt, hbnalt1, hbnalt2⟩⟩,
  exact not_row_balanced_cols_alternate_ends c b k3 hk3 halt hbnalt1 hbnalt2
end

-- If a row colouring does not alternate at some parity, we can find
-- two non-alternating places an odd distance apart.

theorem not_alternate_ends_if_not_alt_some_parity {n : ℕ} (c : row_colouring (n + 1))
  (h : ¬ row_cols_alternate_some_parity c) : ∃ (a : fin (n + 1)) (k2 : ℕ),
    ((a : ℕ) + 2 * k2 + 3 ≤ n + 1) ∧
    (a ∈ c ↔ (((a : ℕ) + 1 : ℕ) : fin (n + 1)) ∈ c) ∧
    ((((a : ℕ) + 2 * k2 + 1 : ℕ) : fin (n + 1)) ∈ c ↔
      (((a : ℕ) + 2 * k2 + 2 : ℕ) : fin (n + 1)) ∈ c) :=
begin
  unfold row_cols_alternate_some_parity at h,
  rw not_or_distrib at h,
  unfold row_cols_alternate_at_parity at h,
  rw [not_forall, not_forall] at h,
  rcases h with ⟨⟨a1, ha1⟩, ⟨a2, ha2⟩⟩,
  rw [not_imp, not_imp] at ha1,
  rw [not_imp, not_imp] at ha2,
  rcases ha1 with ⟨ha1, ha1p, ha1nalt⟩,
  rcases ha2 with ⟨ha2, ha2p, ha2nalt⟩,
  rw [iff.comm, not_iff, iff.comm, not_not] at ha1nalt,
  rw [iff.comm, not_iff, iff.comm, not_not] at ha2nalt,
  by_cases h : a1 < a2,
  { set k2 := (a2 - a1) / 2 with hk2,
    use [(a1 : fin (n + 1)), k2],
    rw fin.coe_coe_of_lt (show a1 < n + 1, by linarith),
    have ha2a1 : a2 - a1 = 2 * k2 + 1,
    { rw hk2,
      rw add_comm,
      conv_lhs { rw ←nat.mod_add_div (a2 - a1) 2 },
      congr,
      rw [←nat.not_even_iff, nat.even_sub (le_of_lt h), nat.even_iff, nat.even_iff, ha1p, ha2p],
      norm_num },
    rw [(show a1 + 2 * k2 + 3 = a1 + (2 * k2 + 1) + 2, by ring),
        (show a1 + 2 * k2 + 2 = a1 + (2 * k2 + 1) + 1, by ring),
        (show a1 + 2 * k2 + 1 = a1 + (2 * k2 + 1), by ring), ←ha2a1, add_comm a1 (a2 - a1),
        nat.sub_add_cancel (le_of_lt h)],
    exact ⟨(by linarith), ha1nalt, ha2nalt⟩ },
  { set k2 := (a1 - a2) / 2 with hk2,
    use [(a2 : fin (n + 1)), k2],
    rw fin.coe_coe_of_lt (show a2 < n + 1, by linarith),
    have ha1a2 : a1 - a2 = 2 * k2 + 1,
    { rw hk2,
      rw add_comm,
      conv_lhs { rw ←nat.mod_add_div (a1 - a2) 2 },
      congr,
      rw [←nat.not_even_iff, nat.even_sub (le_of_not_lt h), nat.even_iff, nat.even_iff, ha1p,
          ha2p],
      norm_num },
    rw [(show a2 + 2 * k2 + 3 = a2 + (2 * k2 + 1) + 2, by ring),
        (show a2 + 2 * k2 + 2 = a2 + (2 * k2 + 1) + 1, by ring),
        (show a2 + 2 * k2 + 1 = a2 + (2 * k2 + 1), by ring), ←ha1a2, add_comm a2 (a1 - a2),
        nat.sub_add_cancel (le_of_not_lt h)],
    exact ⟨(by linarith), ha2nalt, ha1nalt⟩ }
end

-- Thus, not row_balanced in that case.
theorem not_row_balanced_if_not_alt_some_parity {n : ℕ} (c : row_colouring (n + 1))
  (h : ¬ row_cols_alternate_some_parity c) : ¬ row_balanced c :=
begin
  have h2 := not_alternate_ends_if_not_alt_some_parity c h,
  rcases h2 with ⟨a, k2, ⟨hk2, hnalt1, hnalt2⟩⟩,
  exact not_row_balanced_if_not_alternate_ends c a k2 hk2 hnalt1 hnalt2
end

-- Thus, row_cols_alternate_some_parity if and only if row_balanced.
theorem row_cols_alternate_some_parity_iff_row_balanced {n : ℕ} (c : row_colouring (n + 1)) :
  row_cols_alternate_some_parity c ↔ row_balanced c :=
begin
  split,
  { exact row_balanced_if_row_cols_alternate_at_some_parity c },
  { contrapose,
    exact not_row_balanced_if_not_alt_some_parity c }
end

-- So now rewrite the split in terms of
-- row_cols_alternate_some_parity.

def row_alt_colourings (n : ℕ) : finset (row_colouring (n + 1)) :=
finset.univ.filter row_cols_alternate_some_parity

theorem row_balanced_eq_row_alt (n : ℕ) : row_balanced_colourings n = row_alt_colourings n :=
begin
  unfold row_balanced_colourings row_alt_colourings,
  ext,
  rw [mem_filter, mem_filter],
  rw row_cols_alternate_some_parity_iff_row_balanced
end

def row_alt_colourings_r_c (n : ℕ) : finset (row_colouring (n + 1)) :=
(row_alt_colourings n).filter row_cols_alternate

def row_alt_colourings_r_no_c (n : ℕ) : finset (row_colouring (n + 1)) :=
(row_alt_colourings n).filter row_not_cols_alternate

theorem card_row_balanced_r_c_eq (n : ℕ) :
  card (row_balanced_colourings_r_c n) = card (row_alt_colourings_r_c n) :=
begin
  unfold row_balanced_colourings_r_c row_alt_colourings_r_c,
  rw row_balanced_eq_row_alt
end

theorem card_row_balanced_r_no_c_eq (n : ℕ) :
  card (row_balanced_colourings_r_no_c n) = card (row_alt_colourings_r_no_c n) :=
begin
  unfold row_balanced_colourings_r_no_c row_alt_colourings_r_no_c,
  rw row_balanced_eq_row_alt
end

-- Thus the cardinality of the set of balanced colourings, in two
-- parts based on row_cols_alternate_some_parity.
theorem card_split_2_alt (n : ℕ) :
  card (balanced_colourings (n + 1)) = card (row_alt_colourings_r_c n) +
    2 * card (row_alt_colourings_r_no_c n) :=
begin
  rw [card_split_2_row, card_row_balanced_r_c_eq, card_row_balanced_r_no_c_eq]
end

-- The most convenient form to calculate is in terms of those
-- alternating at odd parity, even parity or both parities, so now
-- convert into that form.

-- Columns alternate if and only if they alternate at both parities.
theorem row_cols_alternate_iff_alternate_both_parities {n : ℕ} (c : row_colouring (n + 1)) :
  row_cols_alternate c ↔ (row_cols_alternate_at_parity c 0 ∧ row_cols_alternate_at_parity c 1) :=
begin
  split,
  { intro h,
    split,
    { intros k hk hpar,
      set a : fin (n + 1) := (k : fin (n + 1)) with ha,
      have hk2 : k = (a : ℕ),
      { rw ha,
        symmetry,
        exact fin.coe_coe_of_lt (show k < n + 1, by linarith only [hk]) },
      rw hk2,
      rw hk2 at hk,
      exact h a hk },
    { intros k hk hpar,
      set a : fin (n + 1) := (k : fin (n + 1)) with ha,
      have hk2 : k = (a : ℕ),
      { rw ha,
        symmetry,
        exact fin.coe_coe_of_lt (show k < n + 1, by linarith only [hk]) },
      rw hk2,
      rw hk2 at hk,
      exact h a hk } },
  { rintros ⟨h0, h1⟩ a ha,
    by_cases hpar : (a : ℕ) % 2 = 0,
    { set k := (a : ℕ) with hk,
      have hk2 : a = (k : fin (n + 1)) := (fin.coe_coe_eq_self a).symm,
      rw hk2,
      exact h0 k ha hpar },
    { rw [←nat.even_iff, nat.not_even_iff] at hpar,
      set k := (a : ℕ) with hk,
      have hk2 : a = (k : fin (n + 1)) := (fin.coe_coe_eq_self a).symm,
      rw hk2,
      exact h1 k ha hpar } }
end

def row_cols_alternate_at_parity_0 {n : ℕ} (c : row_colouring (n + 1)) : Prop :=
row_cols_alternate_at_parity c 0

def row_cols_alternate_at_parity_1 {n : ℕ} (c : row_colouring (n + 1)) : Prop :=
row_cols_alternate_at_parity c 1

def row_alt_colourings_0 (n : ℕ) : finset (row_colouring (n + 1)) :=
finset.univ.filter row_cols_alternate_at_parity_0

def row_alt_colourings_1 (n : ℕ) : finset (row_colouring (n + 1)) :=
finset.univ.filter row_cols_alternate_at_parity_1

def row_alt_colourings_parity (n : ℕ) (parity : ℕ) : finset (row_colouring (n + 1)) :=
finset.univ.filter (λ c, row_cols_alternate_at_parity c parity)

theorem row_alt_colourings_0_eq (n : ℕ) :
  row_alt_colourings_0 n = row_alt_colourings_parity n 0 :=
rfl

theorem row_alt_colourings_1_eq (n : ℕ) :
  row_alt_colourings_1 n = row_alt_colourings_parity n 1 :=
rfl

def row_alt_colourings_01 (n : ℕ) : finset (row_colouring (n + 1)) :=
finset.univ.filter row_cols_alternate

theorem row_alt_colourings_union (n : ℕ) :
  row_alt_colourings n = row_alt_colourings_0 n ∪ row_alt_colourings_1 n :=
filter_or _ _ _

theorem row_alt_colourings_inter (n : ℕ) :
  row_alt_colourings_01 n = row_alt_colourings_0 n ∩ row_alt_colourings_1 n :=
begin
  ext,
  erw [mem_inter, mem_filter, mem_filter, mem_filter,
       row_cols_alternate_iff_alternate_both_parities],
  unfold row_cols_alternate_at_parity_0 row_cols_alternate_at_parity_1,
  simp
end

theorem row_alt_colourings_r_c_eq_row_alt_colourings_01 (n : ℕ) :
  row_alt_colourings_r_c n = row_alt_colourings_01 n :=
begin
  ext,
  erw [mem_filter, mem_filter, mem_filter, row_cols_alternate_iff_alternate_both_parities],
  unfold row_cols_alternate_some_parity,
  tauto
end

theorem row_alt_colourings_01_subset (n : ℕ) : row_alt_colourings_01 n ⊆ row_alt_colourings n :=
begin
  rw subset_iff,
  intro x,
  erw [mem_filter, mem_filter, row_cols_alternate_iff_alternate_both_parities],
  unfold row_cols_alternate_some_parity,
  tauto
end

theorem row_alt_colourings_r_no_c_eq_sdiff (n : ℕ) :
  row_alt_colourings_r_no_c n = row_alt_colourings n \ row_alt_colourings_01 n :=
begin
  ext,
  erw [mem_sdiff, mem_filter, mem_filter, mem_filter],
  unfold row_not_cols_alternate,
  tauto
end

theorem card_row_alt_r_c_eq (n : ℕ) :
  card (row_alt_colourings_r_c n) = card (row_alt_colourings_01 n) :=
begin
  rw row_alt_colourings_r_c_eq_row_alt_colourings_01
end

theorem card_row_alt_eq (n : ℕ) :
  card (row_alt_colourings n) =
    card (row_alt_colourings_0 n) + card (row_alt_colourings_1 n) -
      card (row_alt_colourings_01 n) :=
begin
  rw [row_alt_colourings_union, row_alt_colourings_inter],
  have h := card_union_add_card_inter (row_alt_colourings_0 n) (row_alt_colourings_1 n),
  rw ←h,
  simp
end

theorem card_row_alt_r_no_c_eq (n : ℕ) :
  card (row_alt_colourings_r_no_c n) =
    card (row_alt_colourings_0 n) + card (row_alt_colourings_1 n) -
      2 * card (row_alt_colourings_01 n) :=
begin
  rw [row_alt_colourings_r_no_c_eq_sdiff, card_sdiff (row_alt_colourings_01_subset n),
      card_row_alt_eq, nat.sub_sub],
  ring
end

-- Thus the cardinality of the set of balanced colourings, in two
-- parts based on the parity at which the row alternates.  (The form
-- here with a subtraction and addition not fully cancelled avoids
-- needing to prove inequalities required here for cancellation with ℕ
-- subtraction.)
theorem card_split_2_parity (n : ℕ) :
  card (balanced_colourings (n + 1)) =
    2 * card (row_alt_colourings_0 n) + 2 * card (row_alt_colourings_1 n) -
    4 * card (row_alt_colourings_01 n) + card (row_alt_colourings_01 n) :=
begin
  rw [card_split_2_alt, card_row_alt_r_c_eq, card_row_alt_r_no_c_eq, nat.mul_sub_left_distrib,
      nat.left_distrib, add_comm, ←mul_assoc],
  ring
end

-- Define a mapping from finset ℕ to infinite sequences of whether a
-- given natural number is in a set, where 0 is present if and only if
-- in the finset and subsequent elements say which odd n (parity = 0)
-- or even n (parity = 1) are positions where the set alternates.
-- This is used in turn to define such a mapping to row colourings.

def map_to_infinite_seq : ℕ → finset ℕ → ℕ → Prop
| parity x 0 := 0 ∈ x
| parity x (n + 1) :=
    ite (n % 2 = parity ∨ n / 2 + 1 ∈ x) (¬ map_to_infinite_seq parity x n)
                                         (map_to_infinite_seq parity x n)

def map_to_alt_colouring (n : ℕ) (parity : ℕ) (x : finset ℕ) : row_colouring n :=
finset.univ.filter (λ p : row n, map_to_infinite_seq parity x (p : ℕ))

def map_to_alt_colouring_domain (n : ℕ) : finset (finset ℕ) :=
powerset (Ico 0 n)

theorem card_map_to_alt_colouring_domain (n : ℕ) :
  card (map_to_alt_colouring_domain n) = 2 ^ n :=
begin
  unfold map_to_alt_colouring_domain,
  rw [card_powerset, Ico.card],
  simp
end

theorem map_to_alt_colouring_image (n : ℕ) (parity : ℕ) (hparity : parity < 2) :
  image (map_to_alt_colouring (n + 1) parity)
        (map_to_alt_colouring_domain ((n + parity) / 2 + 1)) =
    row_alt_colourings_parity n parity :=
begin
  ext c,
  split,
  { intro h,
    rw mem_image at h,
    rcases h with ⟨x, hx, hmx⟩,
    rw ←hmx,
    erw mem_filter,
    use mem_univ _,
    intros k hk hpar,
    erw [mem_filter, mem_filter],
    rw [fin.coe_coe_of_lt (show k < n + 1, by linarith),
        fin.coe_coe_of_lt (show k + 1 < n + 1, by linarith)],
    have hmk1 : map_to_infinite_seq parity x (k + 1) =
      ite (k % 2 = parity ∨ k / 2 + 1 ∈ x) (¬ map_to_infinite_seq parity x k)
                                           (map_to_infinite_seq parity x k),
    { refl },
    rw [hmk1, hpar],
    simp },
  { intro h,
    rw mem_image,
    use (Ico 0 ((n + parity) / 2 + 1)).filter
      (λ x, ((x = 0 ∧ (0 : fin (n + 1)) ∈ c) ∨
            (0 < x ∧ (((2 * x - 1 - parity : ℕ) : fin (n + 1)) ∈ c ↔
               ¬ ((2 * x - parity : ℕ) : fin (n + 1)) ∈ c)))),
    erw mem_powerset,
    use filter_subset _ _,
    have hn : ∀ k : ℕ, k < n + 1 →
      ((k : fin (n + 1)) ∈
        map_to_alt_colouring (n + 1) parity ((Ico 0 ((n + parity) / 2 + 1)).filter
      (λ x, ((x = 0 ∧ (0 : fin (n + 1)) ∈ c) ∨
            (0 < x ∧ (((2 * x - 1 - parity : ℕ) : fin (n + 1)) ∈ c ↔
              ¬ ((2 * x - parity : ℕ) : fin (n + 1)) ∈ c))))) ↔
      (k : fin (n + 1)) ∈ c),
    { intro k,
      induction k with t ht,
      { erw mem_filter,
        intro h0,
        rw [nat.cast_zero, fin.coe_zero],
        unfold map_to_infinite_seq,
        rw mem_filter,
        interval_cases parity; norm_num },
      { intro hst,
        erw mem_filter,
        erw mem_filter at ht,
        rw fin.coe_coe_of_lt hst,
        unfold map_to_infinite_seq,
        rw nat.succ_eq_add_one at hst,
        replace ht := ht (by linarith only [hst]),
        rw [iff_true_intro (mem_univ _), true_and,
            fin.coe_coe_of_lt (show t < n + 1, by linarith only [hst])] at ht,
        rw [ht, iff_true_intro (mem_univ _), true_and],
        conv_lhs
        { congr,
          rw [mem_filter, Ico.mem, iff_true_intro (zero_le _), iff_true_intro (nat.succ_pos _),
              iff_false_intro (nat.succ_ne_zero _), true_and, true_and, false_and, false_or] },
        erw mem_filter at h,
        cases h with hcu h,
        unfold row_cols_alternate_at_parity at h,
        by_cases hpar : t % 2 = parity,
        { rw nat.succ_eq_add_one t,
          have hht := h t (by linarith only [hst]) hpar,
          interval_cases parity; simp [hpar]; tauto },
        { conv_lhs { congr, rw [iff_false_intro hpar, false_or, nat.left_distrib] },
          have hpar2 : t % 2 = 1 - parity,
          { interval_cases parity,
            { rw [←nat.even_iff, nat.not_even_iff] at hpar,
              rw nat.sub_zero,
              exact hpar },
            { rw [←nat.not_even_iff, not_not, nat.even_iff] at hpar,
              rw nat.sub_self,
              exact hpar } },
          have ht4 := nat.mod_add_div t 2,
          rw [hpar2, add_comm] at ht4,
          rw nat.succ_eq_add_one t,
          have hst4 : t / 2 + 1 < (n + parity) / 2 + 1,
          { interval_cases parity,
            { have hst2 : t + 1 ≤ n, { linarith only [hst] },
              rw [←ht4, (show 2 * (t / 2) + 1 + 1 = 2 * (t / 2 + 1), by ring)] at hst2,
              have hst3 : 2 * (t / 2 + 1) / 2 ≤ n / 2 := nat.div_le_div_right hst2,
              rw nat.mul_div_right _ (show 2 > 0, by norm_num) at hst3,
              conv_rhs { congr, rw add_zero },
              linarith only [hst3] },
            { have hst2 : t + 1 + 1 ≤ n + 1, { linarith only [hst] },
              rw [nat.sub_self, add_zero] at ht4,
              rw [←ht4, (show 2 * (t / 2) + 1 + 1 = 2 * (t / 2 + 1), by ring),
                  ←nat.mod_add_div (n + 1) 2] at hst2,
              have hst3 : 2 * (t / 2 + 1) / 2 ≤ ((n + 1) % 2 + 2 * ((n + 1) / 2)) / 2 :=
                nat.div_le_div_right hst2,
              rw [nat.mul_div_right _ (show 2 > 0, by norm_num),
                  nat.add_mul_div_left _ _ (show 2 > 0, by norm_num),
                  nat.div_eq_of_lt (nat.mod_lt _ (show 2 > 0, by norm_num))] at hst3,
              linarith only [hst3] } },
          conv { congr, congr, rw iff_true_intro hst4 },
          norm_num,
          rw [nat.add_sub_assoc (show parity ≤ 1, by linarith only [hparity]),
              nat.add_sub_assoc (show parity ≤ 2, by linarith only [hparity]),
              (show 2 - parity = 1 + 1 - parity, by ring),
              nat.add_sub_assoc (show parity ≤ 1, by linarith only [hparity]) 1,
              add_comm 1 _, ←add_assoc, ht4],
          by_cases halt : (t : fin (n + 1)) ∈ c ↔ ¬ ((t + 1 : ℕ) : fin (n + 1)) ∈ c,
          { simp [halt] },
          { simp [halt, -nat.cast_succ, -nat.cast_add],
            tauto } } } },
    ext a,
    rw ←fin.coe_coe_eq_self a,
    exact hn a a.is_lt }
end

-- The remaining parts of the expression for the result.

theorem result_parity (n : ℕ) (parity : ℕ) (hparity : parity < 2) :
  card (row_alt_colourings_parity n parity) = 2 ^ ((n + parity) / 2 + 1) :=
begin
  rw [←map_to_alt_colouring_image n parity hparity, ←card_map_to_alt_colouring_domain],
  apply card_image_of_inj_on,
  intros x hx y hy heq,
  ext,
  by_cases h : a = 0,
  { rw h,
    have h0 : (0 : fin (n + 1)) ∈ map_to_alt_colouring (n + 1) parity x ↔
      (0 : fin (n + 1)) ∈ map_to_alt_colouring (n + 1) parity y,
    { rw heq },
    erw [mem_filter, mem_filter] at h0,
    rw fin.coe_zero at h0,
    unfold map_to_infinite_seq at h0,
    simp only [true_and, mem_univ] at h0,
    exact h0 },
  { have ha : (((2 * a - 1 - parity : ℕ) : fin (n + 1)) ∈ map_to_alt_colouring (n + 1) parity x ↔
               ((2 * a - parity : ℕ) : fin (n + 1)) ∈ map_to_alt_colouring (n + 1) parity x) ↔
              (((2 * a - 1 - parity : ℕ) : fin (n + 1)) ∈ map_to_alt_colouring (n + 1) parity y ↔
               ((2 * a - parity : ℕ) : fin (n + 1)) ∈ map_to_alt_colouring (n + 1) parity y),
    { rw heq },
    erw [mem_filter, mem_filter, mem_filter, mem_filter] at ha,
    have h1 : 1 ≤ a, { linarith only [nat.pos_of_ne_zero h] },
    set b := a - 1 with hb,
    have hb1 : a = b + 1, { rw [hb, nat.sub_add_cancel h1] },
    rw [hb1, (show 2 * (b + 1) = 2 * b + 1 + 1, by ring), nat.add_sub_cancel,
        nat.add_sub_assoc (show parity ≤ 1, by linarith only [hparity]),
        nat.add_sub_assoc (show parity ≤ 1, by linarith only [hparity]) (2 * b + 1),
        (show 2 * b + 1 + (1 - parity) = 2 * b + (1 - parity) + 1, by ring)] at ha,
    by_cases hble : 2 * b + 1 + (1 - parity) ≤ n,
    { rw [fin.coe_coe_of_lt (show 2 * b + (1 - parity) < n + 1, by linarith only [hble]),
          fin.coe_coe_of_lt (show 2 * b + (1 - parity) + 1 < n + 1,
                             by linarith only [hble])] at ha,
      have hux : map_to_infinite_seq parity x (2 * b + (1 - parity) + 1) =
        ite ((2 * b + (1 - parity)) % 2 = parity ∨ (2 * b + (1 - parity)) / 2 + 1 ∈ x)
            (¬ map_to_infinite_seq parity x (2 * b + (1 - parity)))
            (map_to_infinite_seq parity x (2 * b + (1 - parity))), { refl },
      have huy : map_to_infinite_seq parity y (2 * b + (1 - parity) + 1) =
        ite ((2 * b + (1 - parity)) % 2 = parity ∨ (2 * b + (1 - parity)) / 2 + 1 ∈ y)
            (¬ map_to_infinite_seq parity y (2 * b + (1 - parity)))
            (map_to_infinite_seq parity y (2 * b + (1 - parity))), { refl },
      have h1p : ¬ (1 - parity) % 2 = parity,
      { interval_cases parity; norm_num },
      have h1p2 : (1 - parity) / 2 = 0,
      { apply nat.div_eq_of_lt,
        apply nat.sub_lt_succ },
      rw [hux, huy, add_comm (2 * b) (1 - parity), nat.add_mul_mod_self_left (1 - parity) 2 b,
          nat.add_mul_div_left _ _ (show 2 > 0, by norm_num), iff_true_intro (mem_univ _),
          iff_true_intro (mem_univ _), true_and, true_and, true_and, true_and, add_assoc,
          ←hb1, h1p2, zero_add] at ha,
      by_cases hax : a ∈ x; by_cases hay : a ∈ y; simp [hax, hay, h1p] at ha; tauto },
    { have hage : n + 1 ≤ 2 * b + (1 - parity) + 1, { linarith },
      erw mem_powerset at hx,
      erw mem_powerset at hy,
      have hnx : ¬ a ∈ x,
      { intro hax,
        have hax2 := mem_of_subset hx hax,
        rw Ico.mem at hax2,
        cases hax2 with hax2a hax2b,
        rw hb1 at hax2b,
        have hax2b2 : b + 1 ≤ (n + parity) / 2, { linarith only [hax2b] },
        rw nat.le_div_iff_mul_le _ _ (show 2 > 0, by norm_num) at hax2b2,
        interval_cases parity; linarith only [hage, hax2b2] },
      have hny : ¬ a ∈ y,
      { intro hay,
        have hay2 := mem_of_subset hy hay,
        rw Ico.mem at hay2,
        cases hay2 with hay2a hay2b,
        rw hb1 at hay2b,
        have hay2b2 : b + 1 ≤ (n + parity) / 2, { linarith only [hay2b] },
        rw nat.le_div_iff_mul_le _ _ (show 2 > 0, by norm_num) at hay2b2,
        interval_cases parity; linarith only [hage, hay2b2] },
      tauto } }
end

theorem result_0 (n : ℕ) : card (row_alt_colourings_0 n) = 2 ^ (n / 2 + 1) :=
begin
  rw [row_alt_colourings_0_eq, result_parity _ _ (show 0 < 2, by norm_num)],
  refl
end

theorem result_1 (n : ℕ) : card (row_alt_colourings_1 n) = 2 ^ ((n + 1) / 2 + 1) :=
begin
  rw [row_alt_colourings_1_eq, result_parity _ _ (show 1 < 2, by norm_num)]
end

-- The colour of individual cells in a row_cols_alternate colouring.
theorem row_cols_alternate_colour' {n : ℕ} (c : row_colouring (n + 1))
    (halt: row_cols_alternate c)
    (a : fin (n + 1)) : a ∈ c ↔ ((0 : fin (n + 1)) ∈ c ↔ (a : ℕ) % 2 = 0) :=
begin
  set a0 : fin (n + 1) := (0 : fin (n + 1)) with ha0,
  set k : ℕ := (a : ℕ) with hk,
  have ha : a = (((a0 : ℕ) + k : ℕ) : fin (n + 1)),
  { rw [ha0, fin.coe_zero, zero_add, hk, fin.coe_coe_eq_self a] },
  rw ha,
  apply row_cols_alternate_colour c a0 (n + 1),
  { rw [ha0, fin.coe_zero, zero_add] },
  { intros k2 hk2,
    rw [ha0, fin.coe_zero, zero_add],
    convert halt (k2 : fin (n + 1)) _,
    { exact (fin.coe_coe_of_lt (show k2 < n + 1, by linarith)).symm },
    { rw fin.coe_coe_of_lt (show k2 < n + 1, by linarith),
      linarith } },
  { rw hk,
    exact a.is_lt }
end

theorem result_01 (n : ℕ) : card (row_alt_colourings_01 n) = 2 :=
begin
  refine card_eq_of_bijective (λ i h, finset.univ.filter (λ x, (x : ℕ) % 2 = i % 2)) _ _ _,
  { intros c hc,
    unfold row_alt_colourings_01 at hc,
    rw mem_filter at hc,
    cases hc with hcu hc,
    use ite ((0 : fin (n + 1)) ∈ c) 0 1,
    split,
    { by_cases h : (0 : fin (n + 1)) ∈ c,
      all_goals { simp [h] } },
    { ext x,
      rw [mem_filter, row_cols_alternate_colour' c hc x],
      by_cases h : (0 : fin (n + 1)) ∈ c,
      all_goals { simp [h] },
      all_goals { norm_num } } },
  { intros i hi,
    unfold row_alt_colourings_01,
    rw mem_filter,
    split,
    { exact mem_univ _ },
    { intros a ha,
      erw [mem_filter, mem_filter],
      split,
      { intro h,
        cases h with hau hai,
        intro ha1,
        cases ha1 with ha1u ha1i,
        rw fin.coe_coe_of_lt (show (a : ℕ) + 1 < n + 1, by linarith only [ha]) at ha1i,
        rw ←hai at ha1i,
        have ha1ib := nat.sub_mod_eq_zero_of_mod_eq ha1i,
        simpa using ha1ib },
      { intro h,
        rw not_and at h,
        replace h := h (mem_univ _),
        use mem_univ _,
        rw fin.coe_coe_of_lt (show (a : ℕ) + 1 < n + 1, by linarith only [ha]) at h,
        by_cases hpar : i % 2 = 0,
        { rw [hpar, ←nat.even_iff, nat.even_succ, not_not, nat.even_iff] at h,
          rw [hpar, h] },
        { rw [←nat.even_iff, nat.not_even_iff] at hpar,
          rw [hpar, ←nat.not_even_iff, not_not, nat.even_succ, nat.not_even_iff] at h,
          rw [hpar, h] } } } },
  { intros i j hi hj heq,
    rw ext_iff at heq,
    have heq0 := heq (0 : fin (n + 1)),
    rw [mem_filter, mem_filter, fin.coe_zero] at heq0,
    norm_num at heq0,
    by_cases h : i = 0,
    { rw h at heq0,
      norm_num at heq0,
      rw nat.mod_eq_of_lt hj at heq0,
      cc },
    { have h1 : 0 < i := nat.pos_of_ne_zero h,
      have h2 : i = 1, { linarith only [h1, hi] },
      rw h2 at heq0,
      norm_num at heq0,
      rw [eq_comm, ←nat.even_iff, nat.not_even_iff, nat.mod_eq_of_lt hj] at heq0,
      cc } }
end

-- The result of the problem, for n + 1 (and in a slightly odd form
-- because of Lean's ℕ subtraction).
theorem p3_result_n1 (n : ℕ) : finset.card (balanced_colourings (n + 1)) =
  2 ^ (n / 2 + 2) + 2 ^ ((n + 1) / 2 + 2) - 8 + 2 :=
begin
  rw [card_split_2_parity, result_0, result_1, result_01,
      mul_comm 2 _, mul_comm 2 _],
  norm_num,
  ring
end

-- The result of the problem, for 2019.
theorem p3_result : finset.card (balanced_colourings 2019) = 2 ^ 1012 - 6 :=
begin
  rw [(show 2019 = 2018 + 1, by norm_num), p3_result_n1],
  norm_num
end
