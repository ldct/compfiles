/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2009, Round 1, Problem 4

Find all positive integers n such that both n + 2008 divides n² + 2008
and n + 2009 divides n² + 2009.
-/

namespace UK2009R1P4

determine solution_set : Set ℕ := {1}

problem uk2009_r1_p4 :
    { n : ℕ | 0 < n ∧ (n + 2008) ∣ (n^2 + 2008) ∧
              (n + 2009) ∣ (n^2 + 2009) } = solution_set := by
  sorry

end UK2009R1P4
