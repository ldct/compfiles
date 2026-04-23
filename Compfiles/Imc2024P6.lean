/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2024, Problem 6

Prove that for any function `f : ℚ → ℤ`, there exist `a, b, c ∈ ℚ` such that
`a < b < c`, `f(b) ≥ f(a)`, and `f(b) ≥ f(c)`.
-/

namespace Imc2024P6

problem imc2024_p6 (f : ℚ → ℤ) :
    ∃ a b c : ℚ, a < b ∧ b < c ∧ f a ≤ f b ∧ f c ≤ f b := by
  -- TODO: full proof. Following the solution:
  -- Either f takes only finitely many values on some rational interval,
  -- giving 3 equal values a < b < c with f(a)=f(b)=f(c); or f(I(x,y)) is
  -- unbounded below. In the unbounded case, pick b and use density to find
  -- a < b < c with f(a), f(c) < f(b).
  sorry

end Imc2024P6
