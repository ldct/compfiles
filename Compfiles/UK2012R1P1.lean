/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2012, Round 1, Problem 1

Find all (positive or negative) integers n for which n² + 20n + 11 is a perfect
square. Remember that you must justify that you have found them all.
-/

namespace UK2012R1P1

/-- Completing the square: n² + 20n + 11 = (n + 10)² − 89. If this equals k²,
    then (n + 10 − k)(n + 10 + k) = 89 (prime), so the solutions come from
    the factorisations of 89. This gives n = 35 or n = −55. -/
determine solution_set : Set ℤ := { 35, -55 }

problem uk2012_r1_p1 :
    { n : ℤ | ∃ k : ℤ, n^2 + 20*n + 11 = k^2 } = solution_set := by
  sorry

end UK2012R1P1
