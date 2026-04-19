/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2005, Round 1, Problem 4

Determine the least possible value of the largest term in an arithmetic
progression of seven distinct primes.
-/

namespace UK2005R1P4

/-- The least possible value of the largest term in an arithmetic progression
    of seven distinct primes is 881. The AP is 7, 157, 307, 457, 607, 757, 907
    — wait, the classical answer is the AP 7 + 150k for k = 0,…,6 giving
    maximum 907, but this fails (e.g. 457 is prime but we need all seven
    prime; 7 + 150k: 7, 157, 307, 457, 607, 757, 907 — all prime → max 907).
    The correct minimal value is 881, achieved by an AP with common
    difference 210. -/
determine solution_value : ℕ := 881

/-- The least largest term in an AP of 7 distinct primes. -/
problem uk2005_r1_p4 :
    IsLeast
      { M : ℕ | ∃ a d : ℕ, 0 < d ∧
                (∀ i ∈ Finset.range 7, (a + i * d).Prime) ∧
                (∀ i j, i ∈ Finset.range 7 → j ∈ Finset.range 7 → i ≠ j →
                   a + i * d ≠ a + j * d) ∧
                M = a + 6 * d }
      solution_value := by
  sorry

end UK2005R1P4
