import analysis.normed_space.basic
import add_torsor

noncomputable theory

/-!
# Torsors of additive normed group actions.

This file defines torsors of additive normed group actions.  The
motivating case is Euclidean affine spaces.

-/

/-- A `normed_add_torsor V P` is a torsor of an additive normed group
action by a `normed_group V` on points `P`. We bundle the distance and
require it to be the same as results from the norm. -/
class normed_add_torsor (V : Type*) (P : Type*) [normed_group V] [has_dist P]
  extends add_torsor V P :=
(dist_eq_norm_vsub : ∀ (x y : P), dist x y = ∥(x -ᵥ y : V)∥)

/-- The distance equals the norm of subtracting two points. This lemma
is needed to make V an explicit rather than implicit argument. -/
lemma norm_dist (V : Type*) {P : Type*} [normed_group V] [has_dist P] [normed_add_torsor V P]
    (x y : P) :
  dist x y = ∥(x -ᵥ y : V)∥ :=
normed_add_torsor.dist_eq_norm_vsub x y

variables (V : Type*) {P : Type*} [normed_group V] [has_dist P] [normed_add_torsor V P]
include V

open add_torsor

/-- The distance defines a metric space structure on the affine
space. -/
instance normed_add_torsor_is_metric_space : metric_space P :=
{ dist_self := begin
    intro p,
    rw [norm_dist V p p, vsub_self, norm_zero]
  end,
  eq_of_dist_eq_zero := begin
    intros p1 p2 h,
    rw [norm_dist V p1 p2, norm_eq_zero] at h,
    exact eq_of_vsub_eq_zero V h
  end,
  dist_comm := begin
    intros x y,
    rw [norm_dist V x y, norm_dist V y x],
    convert norm_neg (y -ᵥ x),
    exact vsub_rev_eq_neg_vsub V y x
  end,
  dist_triangle := begin
    intros x y z,
    rw [norm_dist V x y, norm_dist V y z, norm_dist V x z, ←vsub_add_vsub_cancel],
    apply norm_add_le
  end }
