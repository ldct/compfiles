/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2013, Round 1, Problem 4

Find all positive integers n such that 12n − 119 and 75n − 539 are both
perfect squares.
-/

namespace UK2013R1P4

determine solution_set : Set ℕ := { 12, 20 }

problem uk2013_r1_p4 :
    { n : ℕ | 0 < n ∧ (∃ a : ℕ, 12 * n = a^2 + 119) ∧
                     (∃ b : ℕ, 75 * n = b^2 + 539) } = solution_set := by
  sorry

end UK2013R1P4
