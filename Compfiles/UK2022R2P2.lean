/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2022, Round 2, Problem 2

Find all functions f from the positive integers to the positive integers
such that for all x, y we have: 2y f(f(x²) + x) = f(x + 1) f(2xy).
-/

namespace UK2022R2P2

determine solution_set : Set (ℕ+ → ℕ+) :=
  { fun n => n }

problem uk2022_r2_p2 :
    { f : ℕ+ → ℕ+ |
        ∀ x y : ℕ+,
          2 * y * f (f (x^2) + x) = f (x + 1) * f (2 * x * y) } =
    solution_set := by
  sorry

end UK2022R2P2
