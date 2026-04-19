/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2012, Round 1, Problem 5

Prove that the product of four consecutive positive integers cannot be equal to
the product of two consecutive positive integers.
-/

namespace UK2012R1P5

problem uk2012_r1_p5 :
    ∀ n m : ℕ, 0 < n → 0 < m →
      n * (n + 1) * (n + 2) * (n + 3) ≠ m * (m + 1) := by
  sorry

end UK2012R1P5
