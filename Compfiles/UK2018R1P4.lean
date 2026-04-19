/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2018, Round 1, Problem 4

Consider sequences a₁, a₂, a₃, . . . of positive real numbers with
a₁ = 1 and such that a_{n+1} + aₙ = (a_{n+1} − aₙ)² for each positive
integer n. How many possible values can a_{2017} take?
-/

namespace UK2018R1P4

/-- The set of possible values of a_{2017}. -/
def valueSet : Set ℝ :=
  { v | ∃ a : ℕ → ℝ,
          (∀ n, 0 < a n) ∧
          a 1 = 1 ∧
          (∀ n, 1 ≤ n → a (n + 1) + a n = (a (n + 1) - a n)^2) ∧
          a 2017 = v }

determine num_values : ℕ := 2^2016

problem uk2018_r1_p4 :
    ∃ S : Finset ℝ, (↑S : Set ℝ) = valueSet ∧ S.card = num_values := by
  sorry

end UK2018R1P4
