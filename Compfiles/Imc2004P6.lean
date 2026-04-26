/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2004, Problem 6

For any complex number `z ≠ 0, 1`, define
  `f(z) = ∑ (log z)⁻⁴`,
where the sum runs over all branches of the complex logarithm. Show that
(a) the function `f` is rational, and
(b) `f(z) = z(z² + 4z + 1) / (6(z - 1)⁴)`.

## Branches of the logarithm

The branches of `log z` are exactly `Complex.log z + 2πi k` for `k ∈ ℤ`, where
`Complex.log` is the principal branch. So the sum equals
  `∑_{k ∈ ℤ} 1 / (Complex.log z + 2πi k)⁴`.

## Solution outline

The standard proof uses the Mittag–Leffler expansion of the cotangent:
  `∑_{k ∈ ℤ} 1/(w + 2πi k) = (1/2) + 1/(e^w - 1)`.
Setting `w = log z` and applying `-z d/dz` repeatedly,
  `∑ 1/(log z)² = z/(z-1)²`,
  `∑ 1/(log z)³ = z(z+1)/(2(z-1)³)`,
  `∑ 1/(log z)⁴ = z(z² + 4z + 1)/(6(z-1)⁴)`.

This requires a fair amount of complex analysis (uniform convergence of the
Mittag–Leffler expansion, term-by-term differentiation, etc.) which has not
yet been formalized here; the statement below is left with `sorry`.
-/

namespace Imc2004P6

open Complex

/-- The closed-form rational function. -/
noncomputable def F (z : ℂ) : ℂ := z * (z ^ 2 + 4 * z + 1) / (6 * (z - 1) ^ 4)

/-- The sum of `(log z)⁻⁴` over all branches of the logarithm. -/
noncomputable def branchSum (z : ℂ) : ℂ :=
  ∑' k : ℤ, 1 / (Complex.log z + 2 * Real.pi * I * k) ^ 4

problem imc2004_p6 (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    Summable (fun k : ℤ => 1 / (Complex.log z + 2 * Real.pi * I * k) ^ 4) ∧
    branchSum z = F z := by
  -- TODO: prove the Mittag–Leffler expansion for ∑ 1/(w + 2πik)⁴ and identify
  -- it with the rational function `F z` after substituting `w = log z`.
  sorry

end Imc2004P6
