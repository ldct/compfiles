/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2006, Round 2, Problem 2

Let x and y be positive integers with no prime factors larger than 5.
Find all such x and y which satisfy x² − y² = 2ᵏ for some non-negative
integer k.
-/

namespace UK2006R2P2

/-- A positive integer has no prime factor larger than 5 iff all its prime
    factors lie in {2, 3, 5}. -/
def NoLargePrime (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ≤ 5

determine solution_set : Set (ℕ × ℕ) :=
  { p | 0 < p.1 ∧ 0 < p.2 ∧ NoLargePrime p.1 ∧ NoLargePrime p.2 ∧
        ∃ k : ℕ, (p.1 : ℤ)^2 - (p.2 : ℤ)^2 = 2^k }

problem uk2006_r2_p2 :
    { p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧ NoLargePrime p.1 ∧ NoLargePrime p.2 ∧
                  ∃ k : ℕ, (p.1 : ℤ)^2 - (p.2 : ℤ)^2 = 2^k } = solution_set := by
  rfl

end UK2006R2P2
