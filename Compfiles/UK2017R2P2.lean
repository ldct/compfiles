/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2017, Round 2, Problem 2

Let ⌊x⌋ denote the greatest integer less than or equal to the real
number x. Consider the sequence a₁, a₂, . . . defined by
aₙ = (1/n)(⌊n/1⌋ + ⌊n/2⌋ + · · · + ⌊n/n⌋) for integers n ≥ 1.
Prove that a_{n+1} > aₙ for infinitely many n, and determine whether
a_{n+1} < aₙ for infinitely many n.
-/

namespace UK2017R2P2

noncomputable def a (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc 1 n, ((n / i : ℕ) : ℝ)

/-- The answer is "yes": a_{n+1} < aₙ also holds infinitely often. -/
determine decreasing_infinitely_often : Prop := True

problem uk2017_r2_p2 :
    (∀ N : ℕ, ∃ n, N ≤ n ∧ a n < a (n + 1)) ∧
    (decreasing_infinitely_often ↔ ∀ N : ℕ, ∃ n, N ≤ n ∧ a (n + 1) < a n) := by
  sorry

end UK2017R2P2
