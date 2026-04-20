/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2014, Round 2, Problem 3

Let a₀ = 4 and define a sequence of terms using the formula aₙ = a_{n−1}² − a_{n−1}
for each positive integer n. Prove that there are infinitely many prime numbers
which are factors of at least one term in the sequence.
-/

namespace UK2014R2P3

/-- The BMO sequence. -/
def a : ℕ → ℤ
  | 0 => 4
  | n + 1 => (a n)^2 - a n

problem uk2014_r2_p3 :
    ∃ g : ℕ → ℕ, StrictMono g ∧
      ∀ k, (g k).Prime ∧ ∃ n, (g k : ℤ) ∣ a n := by
  sorry

end UK2014R2P3
