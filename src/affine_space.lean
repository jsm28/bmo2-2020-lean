-- Affine spaces, to the extent needed for some Euclidean geometry.

import analysis.normed_space.basic
import linear_algebra.basis

noncomputable theory

/-!
# Affine spaces

This file defines affine spaces and subspaces and the affine span of a
set of points.

## Notations

This file defines the notation `+ᵥ` for adding a vector to a point and
`-ᵥ` for subtracting two points to produce a vector.

## Implementation notes

This file is very minimal and many things are surely omitted. Most
results can be deduced from corresponding results for vector spaces.
It may be appropriate to refactor in future as a special case of
torsors of additive group actions (currently mathlib only has
multiplicative group actions).  The variables `k` and `V` are explicit
rather than implicit arguments to lemmas because otherwise the
elaborator has problems inferring appropriate types and type class
instances.  Definitions of affine spaces vary as to whether a space
with no points is permitted; here, we require a nonempty type of
points.

## References

* https://en.wikipedia.org/wiki/Affine_space

-/

/-- Type class for the `+ᵥ` and `-ᵥ` notation. -/
class has_vadd (V : Type*) (P : Type*) :=
(vadd : P → V → P)
(vsub : P → P → V)

/-- Addition of a vector to a point, yielding a point. -/
def vadd {V : Type*} {P : Type*} [has_vadd V P] : P → V → P := has_vadd.vadd

/-- Subtraction of two points, yielding a vector. -/
def vsub {V : Type*} {P : Type*} [has_vadd V P] : P → P → V := has_vadd.vsub

infix `+ᵥ`:65 := vadd
infix `-ᵥ`:65 := vsub

/-- An `affine_space k V P` gives an affine space structure to the
nonempty type `P`, acted on by a `vector_space k V` with a transitive
and free action given by the `+ᵥ` operation and a corresponding
subtraction given by the `-ᵥ` operation. (The result of adding a zero
vector does not need to be included here because it is deduced below
from the other axioms for an affine space.) -/
class affine_space (k : Type*) (V : Type*) (P : Type*) [field k] [add_comm_group V]
    [vector_space k V] [nonempty P] [has_vadd V P] :=
(vadd_assoc : ∀ (p : P) (v1 v2 : V), p +ᵥ v1 +ᵥ v2 = p +ᵥ (v1 + v2))
(vadd_vsub : ∀ (p1 p2 : P), p1 +ᵥ (p2 -ᵥ p1 : V) = p2)
(vsub_vadd : ∀ (p : P) (v : V), p +ᵥ v -ᵥ p = v)

/-- A vector space is an affine space over itself. -/
instance vector_space_has_vadd (k : Type*) (V : Type*) [field k] [add_comm_group V]
    [vector_space k V] : has_vadd V V :=
{ vadd := has_add.add,
  vsub := has_sub.sub }
instance vector_space_is_affine_space (k : Type*) (V : Type*) [field k] [nonempty V]
  [add_comm_group V] [vector_space k V] : affine_space k V V :=
{ vadd_assoc := add_assoc,
  vadd_vsub := λ a b, add_eq_of_eq_sub' rfl,
  vsub_vadd := add_sub_cancel' }

namespace affine_space

variables (k : Type*) (V : Type*) {P : Type*} [field k] [add_comm_group V] [vector_space k V]
          [nonempty P] [has_vadd V P] [S : affine_space k V P]
include S

/-- Adding two vectors to a point produces the same result as adding
their sum. -/
lemma vadd_add_assoc (p : P) (v1 v2 : V) : p +ᵥ v1 +ᵥ v2 = p +ᵥ (v1 + v2) :=
affine_space.vadd_assoc k p v1 v2

/-- Adding the result of subtracting from another point produces that
point. -/
@[simp] lemma vadd_vsub_self (p1 p2 : P) : p1 +ᵥ (p2 -ᵥ p1 : V) = p2 :=
affine_space.vadd_vsub k p1 p2

/-- Adding a vector then subtracting the original point produces that
vector. -/
@[simp] lemma vsub_vadd_self (p : P) (v : V) : p +ᵥ v -ᵥ p = v :=
affine_space.vsub_vadd k p v

/-- Adding two vectors to a point produces the same result in either
order. -/
lemma vadd_comm (p : P) (v1 v2 : V) : p +ᵥ v1 +ᵥ v2 = p +ᵥ v2 +ᵥ v1 :=
by rw [vadd_add_assoc k V p v1 v2, vadd_add_assoc k V p v2 v1, add_comm]

/-- If the same point added to two vectors produces equal results,
those vectors are equal. -/
lemma vadd_cancel_left (p : P) (v1 v2 : V) (h : p +ᵥ v1 = p +ᵥ v2) : v1 = v2 :=
by rw [←vsub_vadd_self k V p v1, h, vsub_vadd_self k V p v2]

/-- Adding the zero vector to a point gives the same point. -/
@[simp] lemma vadd_zero (p : P) : p +ᵥ (0 : V) = p :=
begin
  have h : p +ᵥ (0 : V) +ᵥ (0 : V) +ᵥ (p -ᵥ (p +ᵥ (0 : V))) = p +ᵥ (0 : V) +ᵥ (p -ᵥ (p +ᵥ (0 : V))),
  { rw [vadd_add_assoc k V p (0 : V) (0 : V), add_zero] },
  rwa [vadd_vsub_self k V (p +ᵥ (0 : V)), vadd_comm k V (p +ᵥ (0 : V)),
       vadd_vsub_self k V (p +ᵥ (0 : V))] at h
end

/-- Adding a vector to a point, then subtracting another point,
produces the same result as subtracting the points then adding the
vector. -/
lemma vadd_vsub_comm (p1 p2 : P) (v : V) : p1 +ᵥ v -ᵥ p2 = (p1 -ᵥ p2) + v :=
begin
  apply vadd_cancel_left k V p2,
  rw [vadd_vsub_self k V p2, ←vadd_add_assoc k V p2, vadd_vsub_self k V p2]
end

/-- Subtracting the result of adding a vector produces the same result
as subtracting the points and subtracting that vector. -/
lemma vsub_vadd_eq_vsub_sub (p1 p2 : P) (v : V) : p1 -ᵥ (p2 +ᵥ v) = (p1 -ᵥ p2) - v :=
begin
  apply vadd_cancel_left k V (p2 +ᵥ v),
  rw [vadd_vsub_self k V (p2 +ᵥ v), vadd_comm k V p2, vadd_add_assoc k V p2, sub_add_cancel,
      vadd_vsub_self k V p2]
end

/-- Subtracting a point from itself produces 0. -/
@[simp] lemma vsub_self (p : P) : p -ᵥ p = (0 : V) :=
by rw [←add_zero (p -ᵥ p : V), ←vadd_vsub_comm k V p, vsub_vadd_self k V p]

/-- If subtracting two points produces 0, they are equal. -/
lemma eq_of_vsub_eq_zero {p1 p2 : P} (h : p1 -ᵥ p2 = (0 : V)) : p1 = p2 :=
by rw [←vadd_vsub_self k V p2 p1, h, vadd_zero k V p2]

/-- Subtracting two points produces 0 if and only if they are
equal. -/
lemma vsub_eq_zero_iff_eq (p1 p2 : P) : p1 -ᵥ p2 = (0 : V) ↔ p1 = p2 :=
iff.intro (eq_of_vsub_eq_zero k V) (λ h, h ▸ vsub_self k V _)

/-- Subtracting two points in the reverse order produces the negation
of subtracting them. -/
lemma vsub_rev_eq_neg_vsub (p1 p2 : P) : (p2 -ᵥ p1 : V) = -(p1 -ᵥ p2) :=
begin
  symmetry,
  apply neg_eq_of_add_eq_zero,
  apply vadd_cancel_left k V p2,
  rw [vadd_zero k V p2, ←vadd_add_assoc k V p2, vadd_vsub_self k V p2, vadd_vsub_self k V p1]
end

/-- If the same vector added to two points produces equal results,
those points are equal. -/
lemma vadd_cancel_right (p1 p2 : P) (v : V) (h : p1 +ᵥ v = p2 +ᵥ v) : p1 = p2 :=
begin
  have h2 : p1 +ᵥ v +ᵥ -v = p2 +ᵥ v +ᵥ -v, { rw h },
  rwa [vadd_add_assoc k V p1 v (-v), vadd_add_assoc k V p2 v (-v), add_right_neg,
      vadd_zero k V p1, vadd_zero k V p2] at h2
end

/-- Cancellation adding the results of two subtractions. -/
@[simp] lemma vadd_vsub_vsub_cancel (p1 p2 p3 : P) : (p1 -ᵥ p2 : V) + (p2 -ᵥ p3) = (p1 -ᵥ p3) :=
begin
  apply vadd_cancel_left k V p3,
  rw [add_comm, ←vadd_add_assoc k V p3, vadd_vsub_self k V p3, vadd_vsub_self k V p2,
      vadd_vsub_self k V p3]
end

/-- The pairwise differences of a set of points. -/
def vsub_set (s : set P) : set V := ⋃₀((λ p1 : P, (λ p2 : P, p1 -ᵥ p2) '' s) '' s)

/-- The vector subspace spanning the differences of a (possibly empty)
set of points. -/
def vector_span (s : set P) : subspace k V := submodule.span k (vsub_set k V s)

/-- The points in the affine span of a (possibly empty) set of
points. -/
def span_points (s : set P) : set P :=
⋃₀((λ p : P, (λ v : V, p +ᵥ v) '' (vector_span k V s).carrier) '' s)

/-- The set of points in the affine span of a nonempty set of points
is nonempty. -/
lemma span_points_nonempty_of_nonempty {s : set P} (h : s.nonempty) :
  (span_points k V s).nonempty :=
begin
  cases h with p hp,
  use p,
  unfold span_points,
  rw [set.sUnion_image, set.mem_Union],
  use p,
  rw set.mem_Union,
  use hp,
  rw set.mem_image,
  use 0,
  exact and.intro (submodule.zero _) (vadd_zero k V p)
end

/-- Adding a point in the affine span and a vector in the spanning
subspace produces a point in the affine span. -/
lemma vadd_mem_span_points_of_mem_span_points_of_mem_vector_span {s : set P} {p : P} {v : V}
    (hp : p ∈ span_points k V s) (hv : v ∈ vector_span k V s) : p +ᵥ v ∈ span_points k V s :=
begin
  unfold span_points at hp,
  rw [set.sUnion_image, set.mem_Union] at hp,
  cases hp with p2 hp2,
  rw set.mem_Union at hp2,
  cases hp2 with hp2 hp3,
  rw set.mem_image at hp3,
  rcases hp3 with ⟨v2, ⟨hv2, hv2p⟩⟩,
  rw [←hv2p, vadd_add_assoc k V p2],
  unfold span_points,
  rw [set.sUnion_image, set.mem_Union],
  use p2,
  rw set.mem_Union,
  use hp2,
  rw set.mem_image,
  use v2 + v,
  exact and.intro ((vector_span k V s).add hv2 hv) rfl
end

/-- Subtracting two points in the affine span produces a vector in the
spanning subspace. -/
lemma vsub_mem_vector_span_of_mem_span_points_of_mem_span_points {s : set P} {p1 p2 : P}
    (hp1 : p1 ∈ span_points k V s) (hp2 : p2 ∈ span_points k V s) :
  p1 -ᵥ p2 ∈ vector_span k V s :=
begin
  unfold span_points at hp1 hp2,
  rw [set.sUnion_image, set.mem_Union] at hp1 hp2,
  cases hp1 with p1a hp1,
  cases hp2 with p2a hp2,
  rw set.mem_Union at hp1 hp2,
  cases hp1 with hp1a hp1b,
  cases hp2 with hp2a hp2b,
  rw set.mem_image at hp1b hp2b,
  rcases hp1b with ⟨v1, ⟨hv1, hv1p⟩⟩,
  rcases hp2b with ⟨v2, ⟨hv2, hv2p⟩⟩,
  rw [←hv1p, ←hv2p, vsub_vadd_eq_vsub_sub k V (p1a +ᵥ v1), vadd_vsub_comm k V p1a,
      add_sub_assoc],
  have hv1v2 : v1 - v2 ∈ (vector_span k V s).carrier,
  { apply (vector_span k V s).add hv1,
    rw ←neg_one_smul k v2,
    exact (vector_span k V s).smul (-1 : k) hv2 },
  refine (vector_span k V s).add _ hv1v2,
  unfold vector_span,
  change p1a -ᵥ p2a ∈ submodule.span k (vsub_set k V s),
  have hp1p2 : p1a -ᵥ p2a ∈ vsub_set k V s,
  { unfold vsub_set,
    rw [set.sUnion_image, set.mem_Union],
    use p1a,
    rw set.mem_Union,
    use hp1a,
    rw set.mem_image,
    use p2a,
    use hp2a },
  have hp1p2s : vsub_set k V s ⊆ submodule.span k (vsub_set k V s) := submodule.subset_span,
  apply set.mem_of_mem_of_subset hp1p2 hp1p2s
end

end affine_space

open affine_space

/-- If the underlying vector space is a normed space, this defines a
metric space structure on the affine space. -/
instance affine_space_has_dist (k : Type*) (V : Type*) (P : Type*) [normed_field k]
    [normed_group V] [normed_space k V] [nonempty P] [has_vadd V P] [affine_space k V P] :
  has_dist P :=
{ dist := λ x y, ∥(x -ᵥ y : V)∥ }
instance affine_space_is_metric_space (k : Type*) (V : Type*) (P : Type*) [normed_field k]
    [normed_group V] [normed_space k V] [nonempty P] [has_vadd V P] [affine_space k V P] :
  metric_space P :=
{ dist_self := begin
    intro p,
    unfold dist,
    rw [vsub_self k V p, norm_zero]
  end,
  eq_of_dist_eq_zero := begin
    intros p1 p2 h,
    unfold dist at h,
    rw norm_eq_zero at h,
    exact eq_of_vsub_eq_zero k V h
  end,
  dist_comm := begin
    intros x y,
    unfold dist,
    convert norm_neg (y -ᵥ x),
    exact vsub_rev_eq_neg_vsub k V y x
  end,
  dist_triangle := begin
    intros x y z,
    unfold dist,
    rw ←vadd_vsub_vsub_cancel k V x y z,
    apply norm_add_le
  end }

/-- An `affine_subspace k V P` is a subset of an `affine_space k V P`
which has an affine space structure induced by a corresponding
subspace of the `vector_space k V`. -/
structure affine_subspace (k : Type*) (V : Type*) (P : Type*) [field k] [add_comm_group V]
    [vector_space k V] [nonempty P] [has_vadd V P] [affine_space k V P] :=
(carrier : set P)
(direction : subspace k V)
(nonempty : carrier.nonempty)
(add : ∀ (p : P) (v : V), p ∈ carrier → v ∈ direction.carrier → p +ᵥ v ∈ carrier)
(sub : ∀ (p1 p2 : P), p1 ∈ carrier → p2 ∈ carrier → p1 -ᵥ p2 ∈ direction.carrier)

/-- The affine span of a nonempty set of points is the smallest affine
subspace containing those points. (Actually defined here in terms of
spans in vector spaces.) -/
def affine_span (k : Type*) (V : Type*) (P : Type*) [field k] [add_comm_group V]
    [vector_space k V] [nonempty P] [has_vadd V P] [affine_space k V P] (s : set P)
    (h : s.nonempty) : affine_subspace k V P :=
{ carrier := span_points k V s,
  direction := vector_span k V s,
  nonempty := span_points_nonempty_of_nonempty k V h,
  add := λ p v hp hv, vadd_mem_span_points_of_mem_span_points_of_mem_vector_span k V hp hv,
  sub := λ p1 p2 hp1 hp2, vsub_mem_vector_span_of_mem_span_points_of_mem_span_points k V hp1 hp2 }
