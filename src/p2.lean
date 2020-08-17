-- BMO2 2020 problem 2.

-- Choices made for formalization: the original problem refers to
-- "collections", which we take as meaning sets.  We take "no three
-- points are collinear" as meaning "any three points are affinely
-- independent", in the absence of a specific definition of
-- "collinear" in mathlib (a possible such definition would be "affine
-- span has dimension at most 1", which would then need proving
-- equivalent to not being affinely independent; another possible
-- definition would be "there exists a subspace of dimension 1
-- containing those points", but that's more awkward in the case where
-- the affine space has dimension 0; a third possible definition,
-- covering the case of affine spaces over arbitrary modules, would be
-- that there exist a point and a vector such that all points in the
-- subspace are multiples of that vector added to that point).

import geometry.euclidean

import orthocenter

open affine finite_dimensional

variables {V : Type*} {P : Type*} [inner_product_space V] [metric_space P]
    [normed_add_torsor V P] [finite_dimensional ℝ V]

-- Properties of sets of points in the problem.

def at_least_four_points (s : set P) : Prop := 4 ≤ cardinal.mk s

include V

def no_three_points_collinear (s : set P) : Prop :=
∀ p : fin 3 → P, function.injective p → set.range p ⊆ s → affine_independent ℝ p

def same_circumradius (s : set P) : Prop :=
∃ r : ℝ, ∀ t : triangle ℝ P, set.range t.points ⊆ s → t.circumradius = r

-- The description given in the problem.
def p2_problem_desc (s : set P) : Prop :=
at_least_four_points s ∧ no_three_points_collinear s ∧ same_circumradius s

omit V

-- Properties of sets of points in the answer.

-- A set of points is concyclic.  Should probably go in mathlib in
-- some form, with relations between versions with or without centre
-- constrained to be in a given subspace containing the points, and
-- with versions with bundled spheres in nondegenerate cases.
def concyclic (s : set P) : Prop :=
∃ (centre : P) (radius : ℝ), ∀ p ∈ s, dist p centre = radius

include V

-- A set of points forms an orthocentric system.  This should go in
-- mathlib, along with various properties thereof.
def orthocentric_system (s : set P) : Prop :=
∃ t : triangle ℝ P,
  t.orthocenter ∉ set.range t.points ∧ s = insert t.orthocenter (set.range t.points)

-- The description given as an answer to the problem.
def p2_answer_desc (s : set P) : Prop :=
at_least_four_points s ∧ (concyclic s ∨ orthocentric_system s)

-- The result of the problem.
theorem p2_result (s : set P) (hd2 : findim ℝ V = 2) :
  p2_problem_desc s ↔ p2_answer_desc s :=
begin
  unfold p2_problem_desc p2_answer_desc,
  rw and.congr_right_iff,
  intro h4,
  sorry
end
