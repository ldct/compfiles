/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Extreme

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2019, Problem 10
(IMC 2019, Day 2, Problem 10)

`2019` points are chosen uniformly and independently in the unit disc. Let
`C` be their convex hull. Which is larger: the probability that `C` is a
triangle, or the probability that `C` is a quadrilateral?

Answer: the probability that `C` is a quadrilateral is larger.

NOTE: Following the convention of `Imc2024P5`, we phrase probabilities as
normalized volume integrals over the product of unit discs, avoiding an
explicit probability-measure setup. "`C` is a triangle" is encoded as
"the set of extreme points of `convexHull ℝ (range x)` has cardinality 3",
and similarly for quadrilateral.
-/

namespace Imc2019P10

open MeasureTheory Set

/-- The closed unit disc in `ℝ²`. -/
noncomputable def unitDisc : Set (EuclideanSpace ℝ (Fin 2)) :=
  Metric.closedBall 0 1

/-- The set of `2019`-tuples of points in the unit disc whose convex hull
is a triangle (i.e. has exactly `3` extreme points). -/
noncomputable def triangleSet : Set (Fin 2019 → EuclideanSpace ℝ (Fin 2)) :=
  {x | (∀ i, x i ∈ unitDisc) ∧
       Set.ncard (Set.extremePoints ℝ (convexHull ℝ (Set.range x))) = 3}

/-- The set of `2019`-tuples of points in the unit disc whose convex hull
is a quadrilateral (i.e. has exactly `4` extreme points). -/
noncomputable def quadSet : Set (Fin 2019 → EuclideanSpace ℝ (Fin 2)) :=
  {x | (∀ i, x i ∈ unitDisc) ∧
       Set.ncard (Set.extremePoints ℝ (convexHull ℝ (Set.range x))) = 4}

/-- The probability that the convex hull of `2019` uniform i.i.d. points in
the unit disc is a triangle, expressed as a normalized volume. -/
noncomputable def probTriangle : ℝ :=
  (volume triangleSet).toReal / ((volume unitDisc).toReal) ^ (2019 : ℕ)

/-- The probability that the convex hull of `2019` uniform i.i.d. points in
the unit disc is a quadrilateral, expressed as a normalized volume. -/
noncomputable def probQuad : ℝ :=
  (volume quadSet).toReal / ((volume unitDisc).toReal) ^ (2019 : ℕ)

/-- Which is larger? `True` records the answer "the quadrilateral
probability is larger". -/
determine answer : Prop := probTriangle < probQuad

problem imc2019_p10 : answer := by
  -- TODO: Following the official solution.
  -- By symmetry, P(triangle) = C(2019,3) * p and P(quad) = C(2019,4) * q,
  -- where p = P(conv{X₁,X₂,X₃} = △) and q = P(conv{X₁,..,X₄} = quad). It
  -- suffices to show p < 504 q, equivalently
  --   area(△ X₁X₂X₃) ≤ 500 · area(Ω),
  -- where Ω = {Y : X₁X₂X₃Y is a convex quadrilateral}.
  --
  -- Suppose area(△) > 500 · area(Ω). Extending the lines X_iX_j to the
  -- boundary of the disc gives points A_i, B_i which split the disc into
  -- 7 regions D₀,…,D₆ (with Ω = D₄ ∪ D₅ ∪ D₆). The hypothesis forces each
  -- segment A_iX_j, B_iX_j < 1/250, so D₁,D₂,D₃ each fit in a disc of
  -- radius 1/250, and area(D₀) ≤ 3√3/4 (the largest inscribed triangle).
  -- Summing,
  --   π = area(disc) = Σ area(Dᵢ) < 3√3/4 + 3π/250² + π/500 < π,
  -- a contradiction.
  sorry

end Imc2019P10
