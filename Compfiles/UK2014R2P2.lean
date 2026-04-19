/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2014, Round 2, Problem 2

Prove that it is impossible to have a cuboid for which the volume, the
surface area and the perimeter are numerically equal. The perimeter of a
cuboid is the sum of the lengths of all its twelve edges.
-/

namespace UK2014R2P2

problem uk2014_r2_p2 :
    ¬ ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      a * b * c = 2 * (a * b + b * c + c * a) ∧
      a * b * c = 4 * (a + b + c) := by
  sorry

end UK2014R2P2
