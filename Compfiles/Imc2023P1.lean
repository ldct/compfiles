/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2023, Problem 1

Find all functions `f : ℝ → ℝ` that have a continuous second derivative and
for which `f(7x + 1) = 49 f(x)` holds for all `x ∈ ℝ`.

Answer: `f(x) = c (6x + 1)²` for some `c ∈ ℝ`.
-/

namespace Imc2023P1

/-- The set of solutions. -/
determine answer : Set (ℝ → ℝ) :=
  { f | ∃ c : ℝ, ∀ x, f x = c * (6 * x + 1) ^ 2 }

problem imc2023_p1 (f : ℝ → ℝ) (hf_cont_deriv : ContDiff ℝ 2 f) :
    f ∈ answer ↔ ∀ x : ℝ, f (7 * x + 1) = 49 * f x := by
  -- TODO: The proof uses that f'' is fixed under the contraction x ↦ (x-1)/7,
  -- hence constant. Then f = ax^2 + bx + c and coefficient matching gives the
  -- answer.
  sorry

end Imc2023P1
