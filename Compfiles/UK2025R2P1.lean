/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2025, Round 2, Problem 1

Prove that if n is a positive integer, then 1/n can be written as a
finite sum of reciprocals of different triangular numbers.
(A triangular number is one of the form k(k+1)/2 for some positive
integer k.)
-/

namespace UK2025R2P1

/-- The k-th triangular number. -/
def tri (k : ℕ) : ℕ := k * (k + 1) / 2

problem uk2025_r2_p1 (n : ℕ) (hn : 0 < n) :
    ∃ S : Finset ℕ, (∀ k ∈ S, 0 < k) ∧
      (∑ k ∈ S, (1 : ℚ) / tri k) = 1 / n := by
  sorry

end UK2025R2P1
