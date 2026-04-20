/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2015, Round 1, Problem 6

Determine all functions f(n) from the positive integers to the positive integers
which satisfy the following condition: whenever a, b and c are positive integers
such that 1/a + 1/b = 1/c, then 1/f(a) + 1/f(b) = 1/f(c).
-/

namespace UK2015R1P6

determine solution_set : Set (ℕ+ → ℕ+) :=
  { f | ∃ k : ℕ+, ∀ n, f n = k * n }

problem uk2015_r1_p6 :
    { f : ℕ+ → ℕ+ |
        ∀ a b c : ℕ+,
          (1 : ℚ) / a + (1 : ℚ) / b = (1 : ℚ) / c →
          (1 : ℚ) / (f a) + (1 : ℚ) / (f b) = (1 : ℚ) / (f c) } =
    solution_set := by
  sorry

end UK2015R1P6
