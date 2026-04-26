/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .NumberTheory] }

/-!
# International Mathematical Competition 2018, Problem 10

For `R > 1`, let `D_R = {(a,b) ∈ ℤ² : 0 < a² + b² < R}`. Compute
`lim_{R → ∞} ∑_{(a,b) ∈ D_R} (-1)^{a+b} / (a² + b²)`.

Answer: `-π · log 2`.

## Proof outline

Let `E_R = {(a,b) ∈ ℤ² ∖ {0} : a² + b² < R, a + b even}`. Splitting the
target sum by parity of `a + b`,
```
∑_{D_R} (-1)^{a+b}/(a²+b²) = 2 ∑_{E_R} 1/(a²+b²) - ∑_{D_R} 1/(a²+b²).
```
Substitute `(a,b) = (m-n, m+n)`: then `a² + b² = 2(m² + n²)` and the
condition `a² + b² < R, a + b even` becomes `m² + n² < R/2`. Hence
`2 ∑_{E_R} 1/(a²+b²) = ∑_{D_{R/2}} 1/(m²+n²)`, and the original sum
equals `- ∑_{R/2 ≤ a²+b² < R} 1/(a²+b²)`.

Using the Gauss-circle estimate `N(r) = π r² + O(r)` for the number of
nonzero lattice points with `a² + b² < r²`, Abel summation / Stieltjes
integration gives
```
∑_{R/2 ≤ a²+b² < R} 1/(a²+b²) = π log 2 + o(1) as R → ∞.
```
Therefore the limit equals `-π log 2`.
-/

namespace Imc2018P10

open scoped Real

/-- The disc set `D_R = {(a,b) ∈ ℤ² : 0 < a² + b² < R}` as a `Finset`. -/
noncomputable def DR (R : ℝ) : Finset (ℤ × ℤ) :=
  ((Finset.Ioo (-(⌈Real.sqrt R⌉ + 1)) (⌈Real.sqrt R⌉ + 1)) ×ˢ
   (Finset.Ioo (-(⌈Real.sqrt R⌉ + 1)) (⌈Real.sqrt R⌉ + 1))).filter
    (fun p => 0 < p.1^2 + p.2^2 ∧ ((p.1^2 + p.2^2 : ℤ) : ℝ) < R)

/-- The partial sum `∑_{D_R} (-1)^{a+b} / (a² + b²)`.

For integer `k`, `(-1)^|k| = (-1)^k` since `(-1)^2 = 1`, so we use
`(-1)^(|a + b|)` as the sign. -/
noncomputable def sumDR (R : ℝ) : ℝ :=
  ∑ p ∈ DR R, ((-1 : ℝ) ^ (p.1 + p.2).natAbs) / (((p.1^2 + p.2^2 : ℤ) : ℝ))

/-- The IMC 2018 Problem 10 answer. -/
noncomputable determine answer : ℝ := -Real.pi * Real.log 2

problem imc2018_p10 :
    Filter.Tendsto sumDR Filter.atTop (nhds answer) := by
  -- The proof requires:
  -- (1) Splitting the sum by parity of `a + b` and the substitution
  --     `(a,b) = (m - n, m + n)`, which is a bijection
  --     `ℤ² → {(a,b) : a + b even}` with `a² + b² = 2(m² + n²)`.
  -- (2) Gauss circle theorem: `#{(a,b) ∈ ℤ² : a² + b² < r²} = π r² + O(r)`.
  -- (3) Abel summation / Stieltjes integration to evaluate
  --     `∑_{R/2 ≤ a²+b² < R} 1/(a²+b²) → π log 2`.
  -- These ingredients are not yet in Mathlib in a directly applicable form.
  sorry

end Imc2018P10
