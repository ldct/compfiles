/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Convex.Hull

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2024, Problem 5

Let `n > d` be positive integers. Choose `n` independent, uniformly
distributed random points `x₁, …, xₙ` in the unit ball `B ⊂ ℝᵈ`
centered at the origin. For a point `p ∈ B` denote by `f(p)` the
probability that the convex hull of `x₁, …, xₙ` contains `p`. Prove
that if `p, q ∈ B` and `‖p‖ < ‖q‖`, then `f(p) ≥ f(q)`.

NOTE: We phrase `f(p)` as a normalized volume integral over the
product ball `Bⁿ`, avoiding an explicit probability-measure setup.
-/

namespace Imc2024P5

open MeasureTheory Set

/-- The closed unit ball in `ℝᵈ`. -/
noncomputable def unitBall (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  Metric.closedBall 0 1

/-- The function `f p` giving the "probability" (normalized volume) that
`p` lies in the convex hull of `n` uniform points `x₁, …, xₙ` in the
unit ball. The numerator is the volume of the set of `n`-tuples of
points each in the ball whose convex hull contains `p`; the denominator
normalizes by the `n`-th power of the ball volume. -/
noncomputable def f (d n : ℕ) (p : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (volume {x : Fin n → EuclideanSpace ℝ (Fin d) |
        (∀ i, x i ∈ unitBall d) ∧ p ∈ convexHull ℝ (Set.range x)}).toReal
    / ((volume (unitBall d)).toReal) ^ n

problem imc2024_p5 (d n : ℕ) (hd : 0 < d) (hdn : d < n)
    (p q : EuclideanSpace ℝ (Fin d))
    (hp : p ∈ unitBall d) (hq : q ∈ unitBall d) (hpq : ‖p‖ < ‖q‖) :
    f d n p ≥ f d n q := by
  -- TODO: Following the official solution.
  -- The proof uses a reflection/χ-function decomposition: for each
  -- hyperplane H through the origin, reflect the sample across H and
  -- use a "Radon-partition" style counting argument to show the indicator
  -- of "p in conv(x)" dominates that of "q in conv(x)" after a
  -- measure-preserving change of variables. Integrate to get f(p) ≥ f(q).
  sorry

end Imc2024P5
