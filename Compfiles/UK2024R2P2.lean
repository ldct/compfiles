/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2024, Round 2, Problem 2

Find all functions f from the integers to the integers such that for all
integers n: 2f(f(n)) = 5f(n) − 2n.
-/

namespace UK2024R2P2

determine solution_set : Set (ℤ → ℤ) :=
  { fun n => 2 * n }

problem uk2024_r2_p2 :
    { f : ℤ → ℤ | ∀ n, 2 * f (f n) = 5 * f n - 2 * n } =
    solution_set := by
  sorry

end UK2024R2P2
