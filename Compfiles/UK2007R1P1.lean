/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2007, Round 1, Problem 1

Find four prime numbers less than 100 which are factors of 3^32 − 2^32.

The answer is {5, 13, 17, 97}.
-/

namespace UK2007R1P1

determine solution_set : Finset ℕ := {5, 13, 17, 97}

problem uk2007_r1_p1 :
    solution_set.card = 4 ∧
    ∀ p ∈ solution_set, p.Prime ∧ p < 100 ∧ p ∣ (3^32 - 2^32 : ℕ) := by
  refine ⟨by decide, ?_⟩
  intro p hp
  fin_cases hp <;> refine ⟨by decide, by decide, by decide⟩

end UK2007R1P1
