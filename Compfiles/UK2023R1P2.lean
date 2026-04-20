/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2023, Round 1, Problem 2

A sequence of positive integers aₙ begins with a₁ = a and a₂ = b for positive
integers a and b. Subsequent terms in the sequence satisfy the following two
rules for all positive integers n:
  a_{2n+1} = a_{2n} · a_{2n−1},
  a_{2n+2} = a_{2n+1} + 4.
Exactly m of the numbers a₁, a₂, a₃, . . . , a_{2022} are square numbers.
What is the maximum possible value of m?
-/

namespace UK2023R1P2

/-- Build the sequence from the first two terms `a` and `b`. We use a 0-indexed
    sequence `s` so that `s 0 = a`, `s 1 = b`, and for `n ≥ 0`:
    `s (2n+2) = s (2n+1) * s (2n)` and `s (2n+3) = s (2n+2) + 4`. -/
def seq (a b : ℕ) : ℕ → ℕ
  | 0 => a
  | 1 => b
  | (n + 2) =>
      if n % 2 = 0
      then seq a b (n + 1) * seq a b n      -- a_{2k+1} = a_{2k} * a_{2k-1}
      else seq a b (n + 1) + 4              -- a_{2k+2} = a_{2k+1} + 4

/-- The number of square values among `s 0, s 1, …, s 2021` (i.e. the first
    2022 terms). -/
def numSquares (a b : ℕ) : ℕ :=
  ((Finset.range 2022).filter (fun i => IsSquare (seq a b i))).card

determine solution_value : ℕ := 1349 -- known answer (to be verified)

problem uk2023_r1_p2 :
    IsGreatest
      { m : ℕ | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ numSquares a b = m }
      solution_value := by
  sorry

end UK2023R1P2
