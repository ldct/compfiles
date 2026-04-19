/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2020, Round 2, Problem 1

A sequence a₁, a₂, a₃, … has a₁ > 2 and satisfies:
a_{n+1} = aₙ (aₙ − 1) / 2 for all positive integers n.
For which values of a₁ are all the terms of the sequence odd integers?
-/

namespace UK2020R2P1

/-- Analysis: for every term to be an odd integer, we need aₙ ≡ 3 (mod 4)
    at every step, which forces a₁ to be congruent to 2^k + 1 for all k,
    i.e. a₁ = 2^k + 1 for some k ≥ 2 (this characterisation can be refined). -/
determine solution_set : Set ℕ := { a₁ | 2 < a₁ ∧
  ∀ a : ℕ → ℕ, a 1 = a₁ → (∀ n ≥ 1, 2 * a (n + 1) = a n * (a n - 1)) →
    ∀ n ≥ 1, Odd (a n) }

problem uk2020_r2_p1 :
    { a₁ : ℕ | 2 < a₁ ∧
      ∀ a : ℕ → ℕ, a 1 = a₁ → (∀ n ≥ 1, 2 * a (n + 1) = a n * (a n - 1)) →
        ∀ n ≥ 1, Odd (a n) } = solution_set := by
  rfl

end UK2020R2P1
