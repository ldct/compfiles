/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2005, Problem 11
(Second day, Problem 5)

Find all `r > 0` such that: whenever `f : ℝ² → ℝ` is differentiable with
`‖∇f(0,0)‖ = 1` and `∇f` is `1`-Lipschitz, the maximum of `f` on the closed
disc `{u : ‖u‖ ≤ r}` is attained at exactly one point.

Answer: `r ≤ 1/2`.

## Proof outline

* **Upper bound** (if `r > 1/2`, uniqueness fails).
  The function `f(x, y) = x - x²/2 + y²/2` is smooth with
  `∇f(x, y) = (1 - x, y)` so `‖∇f(0,0)‖ = 1` and `∇f` is an affine map with
  Lipschitz constant `1`. On the disc `‖(x,y)‖ ≤ r`,
  `f = r²/2 + 1/4 - (x - 1/2)²` is maximized at `x = 1/2`, giving the two
  points `(1/2, ±√(r² - 1/4))` whenever `r > 1/2`.

* **Lower bound** (if `r ≤ 1/2`, uniqueness holds).
  Suppose `f` attains its max on `D_r` at distinct points `u, v`.
  Since `‖∇f(z) - ∇f(0)‖ ≤ ‖z‖ ≤ r ≤ 1/2`, we have `‖∇f(z)‖ ≥ 1/2 > 0`
  on `D_r`, so the max is on the boundary: `‖u‖ = ‖v‖ = r`, and
  `∇f(u) = a·u`, `∇f(v) = b·v` for some `a, b ≥ 0` (outward gradient at
  boundary maximum). Both `a·u` and `b·v` lie in the closed disc of radius
  `r ≤ 1/2` around `∇f(0)`. Geometric argument: this disc is internally
  tangent to `‖z‖ = 1` at `∇f(0)/‖∇f(0)‖`, and `a·u, b·v` lie outside the
  open disc of radius `r`, forcing `‖a·u - b·v‖ ≥ ‖u - v‖`, with strict
  inequality when `u ≠ v`. This contradicts the `1`-Lipschitz property
  `‖∇f(u) - ∇f(v)‖ ≤ ‖u - v‖`.
-/

namespace Imc2005P11

open Real
open scoped Gradient

/-- The 2-dimensional Euclidean space `ℝ²`. -/
abbrev E := EuclideanSpace ℝ (Fin 2)

/-- The set of `r > 0` for which the uniqueness property holds. -/
determine answer : Set ℝ := { r | 0 < r ∧ r ≤ 1/2 }

/-- The uniqueness property: for any differentiable `f : ℝ² → ℝ` with
`‖∇f(0)‖ = 1` and `∇f` `1`-Lipschitz, the maximum of `f` on the closed
disc of radius `r` is attained at a unique point. -/
def UniqueMax (r : ℝ) : Prop :=
  ∀ f : E → ℝ,
    Differentiable ℝ f →
    ‖gradient f 0‖ = 1 →
    LipschitzWith 1 (fun x => gradient f x) →
    ∃! u : E, u ∈ Metric.closedBall (0 : E) r ∧
      IsMaxOn f (Metric.closedBall (0 : E) r) u

-- snip begin

/-! ## Upper bound: counterexample for `r > 1/2`. -/

/-- The two-point counterexample function `f(x, y) = x - x²/2 + y²/2`. -/
noncomputable def counterFun : E → ℝ :=
  fun u => u 0 - (u 0) ^ 2 / 2 + (u 1) ^ 2 / 2

-- For `r > 1/2`, `counterFun` attains its maximum on `D_r` at the two
-- distinct points `(1/2, ±√(r² - 1/4))`. We do not develop this proof here
-- (an explicit calculation involving Differentiable, gradient, and
-- LipschitzWith), so the case `r > 1/2` of the main theorem is left as a
-- TODO.

-- For `0 < r ≤ 1/2`, full proof of uniqueness requires: (a) showing the
-- gradient is nonvanishing on `D_r`, so any max is on the boundary,
-- (b) outward-gradient property `∇f(u) = a·u` with `a ≥ 0` at boundary
-- maximum, and (c) disc-intersection geometry: the closed disc of radius
-- `r ≤ 1/2` around `∇f(0)` (which has norm 1) meets the closed disc of
-- radius `r` around `0` in at most one point, forcing `a·u = b·v` and a
-- final contradiction with the 1-Lipschitz bound. This is also left as
-- a TODO.

-- snip end

problem imc2005_p11 :
    ∀ r : ℝ, 0 < r → (UniqueMax r ↔ r ∈ answer) := by
  intro r hr
  constructor
  · intro hUniq
    refine ⟨hr, ?_⟩
    by_contra hgt
    push Not at hgt
    -- r > 1/2: counterexample with two distinct maximizers.
    -- TODO: construct explicit `counterFun` witness.
    sorry
  · rintro ⟨_, hle⟩
    -- 0 < r ≤ 1/2: uniqueness via gradient analysis.
    -- TODO: full proof using disc-intersection geometry.
    sorry

end Imc2005P11
