/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2022, Round 1, Problem 1

Find three even numbers less than 400, each of which can be expressed as a
sum of consecutive positive odd numbers in at least six different ways.
(Two expressions are considered to be different if they contain different
numbers. The order of the numbers forming a sum is irrelevant.)

A sum of k ≥ 1 consecutive positive odd numbers starting at 2a+1 (with a ≥ 0)
equals k·(2a+k). So we count pairs (k, a) with k ≥ 1, a ≥ 0 and N = k·(2a+k).

We exhibit the three numbers 240, 288 and 336.
-/

namespace UK2022R1P1

/-- Count the number of ways `N` is a sum of consecutive positive odd
integers, parameterised by (k, a) ∈ [1, N] × [0, N] with N = k(2a+k). -/
def repCount (N : ℕ) : ℕ :=
  (((Finset.Ico 1 (N + 1)) ×ˢ (Finset.range (N + 1))).filter
    (fun p => N = p.1 * (2 * p.2 + p.1))).card

determine solution_set : Finset ℕ := {240, 288, 336}

problem uk2022_r1_p1 :
    solution_set.card = 3 ∧
    ∀ N ∈ solution_set, Even N ∧ N < 400 ∧ 6 ≤ repCount N := by
  refine ⟨by decide, ?_⟩
  intro N hN
  fin_cases hN <;> refine ⟨by decide, by decide, ?_⟩ <;> native_decide

end UK2022R1P1
