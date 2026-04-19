/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2015, Round 1, Problem 4

Let x be a real number such that t = x + x⁻¹ is an integer greater than 2.
Prove that tₙ = xⁿ + x⁻ⁿ is an integer for all positive integers n.
Determine the values of n for which t divides tₙ.

Using the recurrence t_{n+1} = t · t_n − t_{n−1}, all tₙ are integers.
Moreover t | tₙ if and only if n is odd.
-/

namespace UK2015R1P4

problem uk2015_r1_p4 (x : ℝ) (hx : x ≠ 0) (t : ℤ) (ht : (2 : ℤ) < t)
    (hxt : x + x⁻¹ = t) :
    (∀ n : ℕ, ∃ k : ℤ, x^n + (x^n)⁻¹ = k) ∧
    (∀ n : ℕ, 0 < n →
      ((∃ k : ℤ, x^n + (x^n)⁻¹ = k ∧ t ∣ k) ↔ Odd n)) := by
  sorry

end UK2015R1P4
