/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2010, Round 1, Problem 1

Find all positive integer solutions to x² + y² + z² = 2(yz + 1)
and x + y + z = 4018.
-/

namespace UK2010R1P1

/-- Rewriting: x² = 2 − (y − z)², so x² + (y − z)² = 2, forcing
    x = 1 and |y − z| = 1. Combined with x + y + z = 4018, we get
    (y, z) ∈ {(2008, 2009), (2009, 2008)}. -/
determine solution_set : Set (ℕ × ℕ × ℕ) :=
  { (1, 2008, 2009), (1, 2009, 2008) }

problem uk2010_r1_p1 :
    { xyz : ℕ × ℕ × ℕ | 0 < xyz.1 ∧ 0 < xyz.2.1 ∧ 0 < xyz.2.2 ∧
      (xyz.1 : ℤ)^2 + (xyz.2.1 : ℤ)^2 + (xyz.2.2 : ℤ)^2 =
        2 * ((xyz.2.1 : ℤ) * xyz.2.2 + 1) ∧
      xyz.1 + xyz.2.1 + xyz.2.2 = 4018 } = solution_set := by
  sorry

end UK2010R1P1
