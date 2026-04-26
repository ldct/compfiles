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
  -- TODO: Following the official solution (Fedor Petrov).
  --
  -- Step 1 (radial symmetry). `f` depends only on `‖p‖`. Hence WLOG
  -- `p` lies on the segment from `0` to `q` (i.e. `p = t • q` with
  -- `0 ≤ t ≤ 1`). This requires a measure-preserving rotation acting on
  -- the product ball.
  --
  -- Step 2 (deterministic 2^n sign inequality). For a.e. `(x₁,…,xₙ)` in
  -- general position, let `χ_p(x) = 1` iff `p ∈ conv(x₁,…,xₙ)`. It
  -- suffices to show
  --     ∑_{ε ∈ {±1}^n} χ_p(ε₁ x₁,…,εₙ xₙ) ≥ ∑_{ε} χ_q(ε₁ x₁,…,εₙ xₙ).
  -- Integrating over the ball (which is symmetric under `xᵢ ↦ −xᵢ`) and
  -- dividing by `2ⁿ · vol(B)ⁿ` gives `f(p) ≥ f(q)`.
  --
  -- Step 3 (χ-function facet decomposition). For a simplicial convex
  -- polytope `P` with facets `P_1,…,P_k` and origin `0`, letting
  -- `Q_i = conv(0, P_i)`, one has
  --     χ_P = ∑_i σ_i · χ_{Q_i},  σ_i = ±1
  -- where `σ_i = +1` iff `0` and `P` lie on the same side of the affine
  -- hull of `P_i`. (This is a basic fact in combinatorial convex
  -- geometry; not yet in Mathlib.)
  --
  -- Step 4 (collapse). Apply Step 3 to each of the `2ⁿ` polytopes
  -- `conv(ε₁ x₁,…,εₙ xₙ)` and sum. After cancellations across sign
  -- changes, only simplices `S = conv(0, x_{i₁},…,x_{i_d})` with no
  -- `±`-pair survive. The total coefficient `α_S` counts, over the
  -- `n − d` indices `j ∉ {i₁,…,i_d}`, the parity contribution from
  -- whether `±x_j` lies on the same half-space as `0` w.r.t. the affine
  -- hull of `S`. Since each pair `{x_j, −x_j}` either has both on the
  -- `0`-side (contributing `+1`) or one on each side (contributing `0`),
  -- we get `α_S ≥ 0`.
  --
  -- Step 5 (monotonicity in `t`). The χ-function `χ_{tq}(S)` for the
  -- simplex `S = conv(0, x_{i₁},…,x_{i_d})` is the indicator of
  -- `t · q ∈ S`. Since `0 ∈ S`, the set of `t ≥ 0` with `tq ∈ S` is an
  -- interval `[0, t_max(S)]`. Hence `χ_{tq}(S)` is non-increasing in
  -- `t`. Combined with `α_S ≥ 0`, this yields the deterministic
  -- inequality of Step 2.
  --
  -- Each of these steps is substantial; Step 3 in particular requires
  -- a careful development of signed χ-function decompositions of
  -- simplicial polytopes that is not yet present in Mathlib.
  sorry

end Imc2024P5
