/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2016, Round 1, Problem 6

A positive integer is called charming if it is equal to 2 or is of the form
3^i · 5^j where i and j are non-negative integers. Prove that every positive
integer can be written as a sum of different charming integers.
-/

namespace UK2016R1P6

/-- The set of charming positive integers. -/
def Charming : Set ℕ := {n | n = 2 ∨ ∃ i j : ℕ, n = 3^i * 5^j}

problem uk2016_r1_p6 :
    ∀ n : ℕ, 0 < n →
      ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ Charming) ∧ (S.sum id) = n := by
  sorry

end UK2016R1P6
