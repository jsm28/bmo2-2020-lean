-- Affine spaces, to the extent needed for some Euclidean geometry.

import linear_algebra.basis
import add_comm_torsor

noncomputable theory

/-!
# Affine spaces

This file defines affine spaces and subspaces and the affine span of a
set of points.

## Implementation notes

This file is very minimal and many things are surely omitted. Most
results can be deduced from corresponding results for vector spaces.
The variables `k` and `V` are explicit rather than implicit arguments
to lemmas because otherwise the elaborator has problems inferring
appropriate types and type class instances.  Definitions of affine
spaces vary as to whether a space with no points is permitted; here,
we require a nonempty type of points.

## References

* https://en.wikipedia.org/wiki/Affine_space
* https://en.wikipedia.org/wiki/Principal_homogeneous_space

-/

/-- `affine_space` is an abbreviation for `add_comm_torsor` in the
case where the group is a vector space. -/
abbreviation affine_space (k : Type*) (V : Type*) (P : Type*) [field k] [add_comm_group V]
    [vector_space k V] [nonempty P] :=
add_comm_torsor V P

namespace affine_space

open add_comm_torsor

variables (k : Type*) (V : Type*) {P : Type*} [field k] [add_comm_group V] [vector_space k V]
          [nonempty P] [S : affine_space k V P]
include S

/-- The vector subspace spanning the differences of a (possibly empty)
set of points. -/
def vector_span (s : set P) : subspace k V := submodule.span k (vsub_set V s)

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
  exact and.intro (submodule.zero _) (vadd_zero V p)
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
  rw [←hv2p, vadd_add_assoc V p2],
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
  rw [←hv1p, ←hv2p, vsub_vadd_eq_vsub_sub V (p1a +ᵥ v1), vadd_vsub_comm V p1a,
      add_sub_assoc],
  have hv1v2 : v1 - v2 ∈ (vector_span k V s).carrier,
  { apply (vector_span k V s).add hv1,
    rw ←neg_one_smul k v2,
    exact (vector_span k V s).smul (-1 : k) hv2 },
  refine (vector_span k V s).add _ hv1v2,
  unfold vector_span,
  change p1a -ᵥ p2a ∈ submodule.span k (vsub_set V s),
  have hp1p2 : p1a -ᵥ p2a ∈ vsub_set V s,
  { unfold vsub_set,
    rw [set.sUnion_image, set.mem_Union],
    use p1a,
    rw set.mem_Union,
    use hp1a,
    rw set.mem_image,
    use p2a,
    use hp2a },
  have hp1p2s : vsub_set V s ⊆ submodule.span k (vsub_set V s) := submodule.subset_span,
  apply set.mem_of_mem_of_subset hp1p2 hp1p2s
end

end affine_space

open add_comm_torsor affine_space

/-- An `affine_subspace k V P` is a subset of an `affine_space k V P`
which has an affine space structure induced by a corresponding
subspace of the `vector_space k V`. -/
structure affine_subspace (k : Type*) (V : Type*) (P : Type*) [field k] [add_comm_group V]
    [vector_space k V] [nonempty P] [affine_space k V P] :=
(carrier : set P)
(direction : subspace k V)
(nonempty : carrier.nonempty)
(add : ∀ (p : P) (v : V), p ∈ carrier → v ∈ direction.carrier → p +ᵥ v ∈ carrier)
(sub : ∀ (p1 p2 : P), p1 ∈ carrier → p2 ∈ carrier → p1 -ᵥ p2 ∈ direction.carrier)

/-- The affine span of a nonempty set of points is the smallest affine
subspace containing those points. (Actually defined here in terms of
spans in vector spaces.) -/
def affine_span (k : Type*) (V : Type*) (P : Type*) [field k] [add_comm_group V]
    [vector_space k V] [nonempty P] [affine_space k V P] (s : set P)
    (h : s.nonempty) : affine_subspace k V P :=
{ carrier := span_points k V s,
  direction := vector_span k V s,
  nonempty := span_points_nonempty_of_nonempty k V h,
  add := λ p v hp hv, vadd_mem_span_points_of_mem_span_points_of_mem_vector_span k V hp hv,
  sub := λ p1 p2 hp1 hp2, vsub_mem_vector_span_of_mem_span_points_of_mem_span_points k V hp1 hp2 }

section affine_map

variables  (k : Type*) (V1 : Type*) (P1 : Type*) (V2 : Type*) (P2 : Type*)
    (V3 : Type*) (P3 : Type*) [field k]
    [add_comm_group V1] [vector_space k V1] [nonempty P1] [affine_space k V1 P1]
    [add_comm_group V2] [vector_space k V2] [nonempty P2] [affine_space k V2 P2]
    [add_comm_group V3] [vector_space k V3] [nonempty P3] [affine_space k V3 P3]

/-- An `affine_map k V1 P1 V2 P2` is a map from `P1` to `P2` that
induces a corresponding linear map from `V1` to `V2`. -/
structure affine_map :=
(to_fun : P1 → P2)
(linear : linear_map k V1 V2)
(add : ∀ (p : P1) (v : V1), to_fun (p +ᵥ v) = to_fun p +ᵥ linear.to_fun v)

/-- Composition of affine maps. -/
def affine_map.comp (f : affine_map k V2 P2 V3 P3) (g : affine_map k V1 P1 V2 P2)
  : affine_map k V1 P1 V3 P3 :=
{ to_fun := f.to_fun ∘ g.to_fun,
  linear := f.linear.comp g.linear,
  add := begin
    intros p v,
    rw [function.comp_app, g.add, f.add],
    refl
  end
}

end affine_map
