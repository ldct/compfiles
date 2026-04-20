/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2025, Problem 2

Let `f : ℝ → ℝ` be a twice continuously differentiable function, and suppose
that `∫_{-1}^{1} f(x) dx = 0` and `f(1) = f(-1) = 1`. Prove that

  `∫_{-1}^{1} (f''(x))² dx ≥ 15`,

and find all such functions for which equality holds.

The answer: equality holds iff `f(x) = (-5x⁴ + 30x² - 9) / 16` on `[-1, 1]`.
-/

namespace Imc2025P2

open scoped MeasureTheory
open intervalIntegral Set

/-- The extremal function: `f(x) = (-5x⁴ + 30x² - 9) / 16`. -/
noncomputable def extremal : ℝ → ℝ := fun x => (-5 * x^4 + 30 * x^2 - 9) / 16

/-- The set of functions achieving equality in Problem 2: those that agree with
`extremal` on `[-1, 1]`. -/
determine equalitySet : Set (ℝ → ℝ) :=
  { f | ∀ x ∈ Set.Icc (-1 : ℝ) 1, f x = extremal x }

problem imc2025_p2 (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hint : ∫ x in (-1 : ℝ)..1, f x = 0)
    (hf1 : f 1 = 1) (hfm1 : f (-1) = 1) :
    15 ≤ ∫ x in (-1 : ℝ)..1, (iteratedDeriv 2 f x) ^ 2 ∧
    (f ∈ equalitySet ↔ ∫ x in (-1 : ℝ)..1, (iteratedDeriv 2 f x) ^ 2 = 15) := by
  -- TODO: Proof uses Cauchy–Schwarz for integrals with test function
  -- g(x) = 1 - x² and integration by parts twice, yielding
  --   √(∫ (f'')² · ∫ g²) ≥ ∫ f'' g = 4,
  -- so ∫ (f'')² ≥ 16 / (16/15) = 15. Equality in C-S means f'' = λ g, and
  -- solving the boundary/integral conditions gives λ = 15/4, a = 0, b = -9/16,
  -- yielding f(x) = (-5x⁴ + 30x² - 9)/16.
  sorry

end Imc2025P2
