/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2009, Round 1, Problem 5

Determine the sequences a₀, a₁, a₂, ... which satisfy all of the following
conditions:
a) a_{n+1} = 2 a_n² − 1 for every integer n ≥ 0,
b) a₀ is a rational number and
c) a_i = a_j for some i, j with i ≠ j.

We characterize the set of valid starting values a₀ ∈ ℚ.
-/

namespace UK2009R1P5

/-- The set of rational starting values a₀ for which the sequence defined by
a_{n+1} = 2 a_n² − 1 has a repeated term. -/
def valid_starts : Set ℚ :=
  { a0 | ∃ a : ℕ → ℚ, a 0 = a0 ∧
          (∀ n, a (n + 1) = 2 * (a n)^2 - 1) ∧
          (∃ i j, i ≠ j ∧ a i = a j) }

determine answer : Set ℚ := { a0 | a0 = -1 ∨ a0 = 0 ∨ a0 = 1 ∨ a0 = 1/2 ∨ a0 = -1/2 }

problem uk2009_r1_p5 : valid_starts = answer := by
  sorry

end UK2009R1P5
