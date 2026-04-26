/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Inequality] }

/-!
# International Mathematical Competition 1995, Problem 6 (Day 1)

Let `p > 1`. Show that there exists `K_p > 0` such that for all real `x, y`
satisfying `|x|^p + |y|^p = 2`, we have
  `(x - y)^2 ≤ K_p * (4 - (x + y)^2)`.

## Proof outline (official solution)

We seek `K_p` such that on the set
  `S = {(x, y) ∈ ℝ × ℝ | |x|^p + |y|^p = 2}`
the function `f(x, y) = (x - y)^2 / (4 - (x + y)^2)` is bounded above by
`K_p`. The proof uses compactness off a neighbourhood of the diagonal
`x = y = 1` (and symmetrically `x = y = -1`) and a local Taylor expansion
near that point.

Step 1. Strict convexity of `t ↦ |t|^p` for `p > 1` gives
  `|(x + y)/2|^p ≤ (|x|^p + |y|^p)/2 = 1`,
with equality iff `x = y`. Hence `(x + y)^2 ≤ 4` always, and `(x + y)^2 = 4`
iff `x = y` and `|x|^p = 1`, i.e. `x = y = ±1`. In particular if `x ≠ y`
then `4 - (x + y)^2 > 0`.

Step 2. (Compactness.) For any `δ ∈ (0, 1)`, the set
  `D_δ = {(x, y) ∈ S : |x - y| ≥ δ}`
is compact (closed in `S`, and `S` is bounded by `|x|, |y| ≤ 2^{1/p}`).
On `D_δ`, the denominator `4 - (x + y)^2` is continuous and strictly
positive (by Step 1), hence bounded below by some `c_δ > 0`. The numerator
`(x - y)^2` is bounded above by some `M_δ` (it is continuous on a compact
set). So `f ≤ M_δ / c_δ` on `D_δ`.

Step 3. (Local analysis near the diagonal.) WLOG `x, y` have the same sign
(if they have opposite signs then `|x - y| ≥ max(|x|, |y|) ≥ 1`, since
`|x|^p + |y|^p = 2` forces `max(|x|, |y|) ≥ 1`; choosing `δ = 1/2` puts
this in the compact case). By symmetry, take `x, y ≥ 0` with
`x^p + y^p = 2`. Setting `x = 1 + t` and computing `y` from
`y^p = 2 - (1 + t)^p`, the implicit function theorem (or direct Taylor
expansion) gives
  `y = 1 - t - (p - 1) t^2 + o(t^2)` as `t → 0`.
Therefore
  `(x - y)^2 = (2t + (p-1)t^2 + o(t^2))^2 = 4 t^2 + o(t^2)`,
  `(x + y)^2 = (2 - (p-1)t^2 + o(t^2))^2 = 4 - 4(p-1) t^2 + o(t^2)`,
so `4 - (x + y)^2 = 4(p-1) t^2 + o(t^2)`. Hence for some `δ_p > 0`, when
`|t| < δ_p` we have
  `(x - y)^2 < (1 / (p - 1) + 1) · (4 - (x + y)^2)`,
giving the inequality with `K_p` that constant near `(1, 1)`. The
neighbourhood near `(-1, -1)` is handled symmetrically.

Step 4. Combining: take `K_p` to be the maximum of the local constant from
Step 3 and `M_δ / c_δ` from Step 2 with a small enough `δ`.

## Implementation notes

A complete formalization in Lean 4 / Mathlib would require:

* `Real.rpow` machinery for `|x|^p` with real `p > 1`,
* strict convexity of `Real.rpow _ p` on `[0, ∞)`,
* compactness/extreme value arguments on the level set
  `{(x, y) : |x|^p + |y|^p = 2}`,
* a Taylor expansion / implicit function argument near `(1, 1)`.

These are all available in Mathlib but tying them together is sizeable.
The skeleton below records the statement and proof plan with `sorry`.
-/

namespace Imc1995P6

open Real

problem imc1995_p6 (p : ℝ) (hp : 1 < p) :
    ∃ K : ℝ, 0 < K ∧
      ∀ x y : ℝ, |x| ^ p + |y| ^ p = 2 →
        (x - y) ^ 2 ≤ K * (4 - (x + y) ^ 2) := by
  -- TODO: full proof.
  --
  -- Plan:
  --
  -- (1) [Bounded constraint set] Let `S := {(x, y) | |x|^p + |y|^p = 2}`.
  --     For `(x, y) ∈ S` we have `|x|^p ≤ 2` so `|x| ≤ 2^{1/p}`, similarly
  --     for `|y|`. Hence `S` is bounded; it is also closed (preimage of
  --     `{2}` under a continuous function), so `S` is compact in `ℝ²`.
  --
  -- (2) [Strict convexity] `t ↦ |t|^p` is strictly convex on `ℝ` for `p > 1`
  --     (use `strictConvexOn_rpow` on `[0, ∞)` plus the fact that
  --     `|·|^p = (|·|)^p`; even functions, strict convexity on each side
  --     plus a check at `0`). Therefore for `(x, y) ∈ S` with `x ≠ y`,
  --     `|(x + y)/2|^p < (|x|^p + |y|^p)/2 = 1`, giving `|x + y| < 2` and
  --     `4 - (x + y)^2 > 0`.
  --
  -- (3) [Sign reduction] If `x ≥ 0, y ≤ 0` (or vice versa) and `x^p + |y|^p
  --     = 2`, then since `max(x, -y) ≥ 1` we get `|x - y| = x + |y| ≥ 1`.
  --     Hence on the "opposite-sign" part of `S`, `|x - y| ≥ 1`.
  --
  -- (4) [Compactness bound for `δ = 1/2`] Let
  --       `D := {(x, y) ∈ S : |x - y| ≥ 1/2}`.
  --     `D` is compact and on `D`, `4 - (x + y)^2` is continuous and (by
  --     (2)) strictly positive, hence bounded below by some `c > 0`. Also
  --     `(x - y)^2` is bounded above by some `M`. So
  --       `(x - y)^2 ≤ (M / c) * (4 - (x + y)^2)` on `D`.
  --     Set `K_1 := M / c` (positive since `M > 0` once `D` is nonempty, e.g.
  --     `(2^{1/p}, -(2^{1/p}))` has the right `p`-norm only if … — instead
  --     take `K_1 := max (M / c) 1`).
  --
  -- (5) [Local bound near `(1,1)`] On the same-sign branch `x, y ≥ 0` with
  --     `x^p + y^p = 2` near `(1, 1)`, parametrize `x = 1 + t`. Then
  --     `y(t) = (2 - (1 + t)^p)^{1/p}`. Taylor expand at `t = 0`:
  --       `(1 + t)^p = 1 + p t + p(p-1)/2 · t^2 + O(t^3)`,
  --       `2 - (1 + t)^p = 1 - p t - p(p-1)/2 · t^2 + O(t^3)`,
  --       `y(t) = 1 - t - (p - 1) t^2 + O(t^3)`.
  --     Hence
  --       `(x - y)^2 = 4 t^2 + O(t^3)`,
  --       `4 - (x + y)^2 = 4(p - 1) t^2 + O(t^3)`.
  --     So there exists `δ_p > 0` and `K_2 := 2 / (p - 1)` (any constant
  --     greater than `1 / (p - 1)`) with `(x - y)^2 ≤ K_2 (4 - (x+y)^2)`
  --     whenever `|x - 1| < δ_p`.
  --     A symmetric argument handles the neighbourhood of `(-1, -1)`.
  --
  -- (6) [Combine] Choose `δ := min(δ_p, 1/2)`. The set `S \ D_δ` (in the
  --     same-sign branch) is contained in a small neighbourhood of `(1,1)`
  --     or `(-1,-1)` (since `|x - y| < δ` together with `x^p + y^p = 2` on
  --     the positive branch forces `(x, y)` to be close to some point on
  --     the diagonal; and on `S`, the only diagonal points are `(±1, ±1)`).
  --     Bound `f` by `K_2` there. On `D_δ`, bound `f` by `K_1` from (4).
  --     Take `K_p := max(K_1, K_2) + 1`.
  sorry

end Imc1995P6
