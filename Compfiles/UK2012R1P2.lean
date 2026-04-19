/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# British Mathematical Olympiad 2012, Round 1, Problem 2

Consider the numbers 1, 2, . . . , n. Find, in terms of n, the largest integer
t such that these numbers can be arranged in a row so that all consecutive
terms differ by at least t.
-/

namespace UK2012R1P2

/-- The set of integers t ≥ 0 such that 1, …, n can be arranged in a row
(as a permutation of `Fin n`) with every pair of consecutive terms differing
by at least t in absolute value. Here we use `Fin n → Fin n` permutations and
interpret the value at position i as (σ i).val + 1. -/
def Achievable (n t : ℕ) : Prop :=
  ∃ σ : Equiv.Perm (Fin n),
    ∀ i : Fin n, ∀ h : i.val + 1 < n,
      t ≤ (Int.natAbs ((σ ⟨i.val + 1, h⟩).val - (σ i).val))

determine solution_value (n : ℕ) : ℕ := n / 2

problem uk2012_r1_p2 (n : ℕ) (hn : 2 ≤ n) :
    Achievable n (solution_value n) ∧
    ∀ t, Achievable n t → t ≤ solution_value n := by
  sorry

end UK2012R1P2
