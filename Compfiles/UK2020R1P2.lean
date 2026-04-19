/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2020, Round 1, Problem 2

A sequence of integers a₁, a₂, a₃, … satisfies the relation
4 a_{n+1}² − 4 aₙ a_{n+1} + aₙ² − 1 = 0 for all positive integers n.
What are the possible values of a₁?
-/

namespace UK2020R1P2

/-- The relation rewrites as (2 a_{n+1} − aₙ)² = 1, i.e.
    2 a_{n+1} = aₙ ± 1. For a_{n+1} to be an integer, aₙ must be odd.
    Hence every aₙ is odd, and in particular a₁ can be any odd integer. -/
determine solution_set : Set ℤ := { a | Odd a }

problem uk2020_r1_p2 :
    { a₁ : ℤ | ∃ a : ℕ → ℤ, a 1 = a₁ ∧
      ∀ n ≥ 1, 4 * (a (n + 1))^2 - 4 * a n * a (n + 1) + (a n)^2 - 1 = 0 }
    = solution_set := by
  sorry

end UK2020R1P2
