/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2007, Round 1, Problem 6

Let n be an integer. Show that, if 2 + 2·√(1 + 12n²) is an integer, then
it is a perfect square.
-/

namespace UK2007R1P6

problem uk2007_r1_p6 :
    ∀ n : ℤ, ∀ m : ℤ, (m : ℝ) = 2 + 2 * Real.sqrt (1 + 12 * (n : ℝ)^2) →
      ∃ s : ℤ, m = s^2 := by
  sorry

end UK2007R1P6
