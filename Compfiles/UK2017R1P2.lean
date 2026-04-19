/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2017, Round 1, Problem 2

For each positive real number x, we define {x} to be the greater of x
and 1/x, with {1} = 1. Find, with proof, all positive real numbers y
such that 5y{8y}{25y} = 1.
-/

namespace UK2017R1P2

/-- The operation {x} = max(x, 1/x) for positive reals. -/
noncomputable def curly (x : ℝ) : ℝ := max x (1 / x)

determine solution_set : Set ℝ :=
  { y | y = 1 / 5 ∨ y = Real.sqrt 10 / 25 }

problem uk2017_r1_p2 (y : ℝ) (hy : 0 < y) :
    y ∈ solution_set ↔ 5 * y * curly (8 * y) * curly (25 * y) = 1 := by
  sorry

end UK2017R1P2
