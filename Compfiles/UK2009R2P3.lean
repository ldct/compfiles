/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2009, Round 2, Problem 3

Find all functions f from the real numbers to the real numbers which satisfy
f(x³) + f(y³) = (x + y)(f(x²) + f(y²) − f(xy)) for all real numbers x and y.
-/

namespace UK2009R2P3

determine solution_set : Set (ℝ → ℝ) :=
  { f | ∃ k : ℝ, ∀ x, f x = k * x }

problem uk2009_r2_p3 :
    { f : ℝ → ℝ | ∀ x y, f (x^3) + f (y^3) = (x + y) * (f (x^2) + f (y^2) - f (x*y)) } =
    solution_set := by
  sorry

end UK2009R2P3
