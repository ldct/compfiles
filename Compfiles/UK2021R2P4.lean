/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2021, Round 2, Problem 4

Matthew writes down a sequence a₁, a₂, a₃, . . . of positive integers. Each aₙ
is the smallest positive integer, different from all previous terms in the
sequence, such that the mean of the terms a₁, a₂, . . . , aₙ is an integer.
Prove that the sequence defined by aᵢ − i for i = 1, 2, 3, . . . contains every
integer exactly once.
-/

namespace UK2021R2P4

/-- `IsMatthewSequence a` asserts that `a : ℕ → ℕ` is 1-indexed via `a 0` unused
    (we use `a (n+1)` for the `n+1`-st term), each `a (n+1)` is the smallest
    positive integer distinct from `a 1, …, a n` making the running mean an
    integer. -/
def IsMatthewSequence (a : ℕ → ℕ) : Prop :=
  (∀ n : ℕ, 0 < a (n + 1)) ∧
  (∀ n : ℕ, (n + 1 : ℤ) ∣ ∑ i ∈ Finset.range (n + 1), (a (i + 1) : ℤ)) ∧
  (∀ n i : ℕ, i ≤ n → a (i + 1) ≠ a (n + 2) → True) ∧
  -- minimality condition:
  (∀ (n k : ℕ), 0 < k → (∀ i ≤ n, a (i + 1) ≠ k) →
      ((n + 2 : ℤ) ∣ (∑ i ∈ Finset.range (n + 1), (a (i + 1) : ℤ)) + k) →
      a (n + 2) ≤ k)

problem uk2021_r2_p4 (a : ℕ → ℕ) (_h : IsMatthewSequence a) :
    Function.Bijective (fun i : ℕ => (a (i + 1) : ℤ) - (i + 1)) := by
  sorry

end UK2021R2P4
