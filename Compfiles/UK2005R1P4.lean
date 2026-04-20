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
    of seven distinct primes is 907, achieved by the AP
    `7, 157, 307, 457, 607, 757, 907` (common difference 150). -/
determine solution_value : ℕ := 907

/-- The least largest term in an AP of 7 distinct primes. -/
problem uk2005_r1_p4 :
    IsLeast
      { M : ℕ | ∃ a d : ℕ, 0 < d ∧
                (∀ i ∈ Finset.range 7, (a + i * d).Prime) ∧
                (∀ i j, i ∈ Finset.range 7 → j ∈ Finset.range 7 → i ≠ j →
                   a + i * d ≠ a + j * d) ∧
                M = a + 6 * d }
      solution_value := by
  constructor
  · -- Witness AP: 7 + 150*i for i = 0..6
    refine ⟨7, 150, by decide, ?_, ?_, by decide⟩
    · intro i hi
      fin_cases hi <;> native_decide
    · intro i j hi hj hij
      fin_cases hi <;> fin_cases hj <;> first | (exact absurd rfl hij) | decide
  · -- Lower bound: any such M must be ≥ 907. (Classical result.)
    rintro M ⟨a, d, hd, hprime, _hdist, hM⟩
    sorry

end UK2005R1P4
