/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2024, Problem 2

For `n = 1, 2, ...` let
`S_n = log (n^2-th root of (1^1 * 2^2 * ... * n^n)) - log (sqrt n)`.
Find `lim_{n → ∞} S_n`.

Answer: `-1/4`.

## Solution sketch

We rewrite
`S_n = (1/n^2) * Σ_{k=1}^n k * log k - (1/2) log n`
`    = (1/n) * Σ_{k=1}^n (k/n) * log(k/n) + (log n)/(2n)`.

The second term tends to `0`, and the first is a Riemann sum for
`∫_0^1 x log x dx = -1/4`.
-/

namespace Imc2024P2

open Filter Topology MeasureTheory intervalIntegral Set Real

/-- The sequence `S_n` in the problem.
We state it as `(1/n²) Σ k log k - (log n)/2` for `n ≥ 1`.
For `n = 0`, the expression evaluates to `0` (all terms in the sum are zero). -/
noncomputable def S (n : ℕ) : ℝ :=
  (1 / (n : ℝ)^2) * ∑ k ∈ Finset.range (n + 1), (k : ℝ) * Real.log k
    - (1 / 2) * Real.log n

/-- The limit of `S_n` as `n → ∞`. -/
noncomputable determine answer : ℝ := -(1 / 4)

problem imc2024_p2 :
    Tendsto S atTop (𝓝 answer) := by
  -- TODO: Full proof requires converting the sum to a Riemann sum
  -- for `∫_0^1 x log x dx = -1/4`. The necessary Mathlib lemma
  -- (tendsto_sum_riemann_to_integral or similar) does not exist directly;
  -- it would need to be derived via `AntitoneOn.sum_le_integral`-style
  -- sandwich bounds, splitting the interval at `1/e` where `x log x` changes monotonicity.
  sorry

end Imc2024P2
