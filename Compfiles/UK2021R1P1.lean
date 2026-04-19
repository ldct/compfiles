/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2021, Round 1, Problem 1

Alice and Bob take it in turns to write numbers on a blackboard.
Alice starts by writing an integer a between −100 and 100 inclusive.
On each of Bob's turns he writes twice the number Alice wrote last.
On each of Alice's subsequent turns she writes the number 45 less
than the number Bob wrote last. At some point, the number a is
written on the board for a second time. Find the possible values of a.
-/

namespace UK2021R1P1

/-- The sequence of values on the board is
    s₀ = a, s₁ = 2a, s₂ = 2a − 45, s₃ = 4a − 90, s₄ = 4a − 135, …
    In general s_{2k} = 2^k · a − 45·(2^k − 1) (for k ≥ 1) and
    s_{2k+1} = 2 · s_{2k}. The value a reappears precisely when
    (2^k − 1)·a = 45·(2^k − 1)·something equal to 0 or when the
    first equation 2^k · a − 45 · (2^k − 1) = a has a solution, i.e.
    (2^k − 1)(a − 45 · (…)) = 0. Working through the bounds gives
    a ∈ {−90, −42, −30, 30, 42, 45, 90}. -/
determine solution_set : Set ℤ := { 0, 30, 42, 45 }

/-- The sequence of numbers on the board: position 0 is Alice's initial
    value a, odd positions are Bob's (twice the previous), and even
    positions after 0 are Alice's (45 less than the previous). -/
def seqValue (a : ℤ) : ℕ → ℤ
  | 0 => a
  | n + 1 => if (n + 1) % 2 = 1 then 2 * seqValue a n else seqValue a n - 45

problem uk2021_r1_p1 :
    { a : ℤ | -100 ≤ a ∧ a ≤ 100 ∧
      ∃ n, 0 < n ∧ seqValue a n = a } = solution_set := by
  sorry

end UK2021R1P1
