/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2019, Round 1, Problem 2

For each positive integer n ≥ 3, we define an n-ring to be a circular
arrangement of n (not necessarily different) positive integers such that the
product of every three neighbouring integers is n. Determine the number of
integers n in the range 3 ≤ n ≤ 2018 for which it is possible to form an
n-ring.
-/

namespace UK2019R1P2

/-- `HasNRing n` holds iff there is a function `a : ℕ → ℕ+` that is periodic
    with period `n` and such that for every `i`, the product of three
    consecutive values `a i * a (i+1) * a (i+2)` equals `n`. -/
def HasNRing (n : ℕ) : Prop :=
  ∃ a : ℕ → ℕ+,
    (∀ i, a (i + n) = a i) ∧
    (∀ i, ((a i : ℕ) * a (i + 1) * a (i + 2) : ℕ) = n)

/-- The answer is the number of such n in [3, 2018]. An n-ring exists iff
    either 3 | n or n is a perfect cube: in the first case, the constant
    period-3 pattern (1, 1, n) (and cyclic rotations) works; in the second,
    the constant pattern (∛n, ∛n, ∛n) works. Counting in [3, 2018]:
      · multiples of 3: ⌊2018/3⌋ = 672 (namely 3, 6, …, 2016)
      · cubes 2³,…,12³ = 8, 27, …, 1728: 11 values
      · cubes divisible by 3: 3³, 6³, 9³, 12³: 4 values
    Total: 672 + 11 − 4 = 679. -/
determine solution_value : ℕ := 679

open scoped Classical in
problem uk2019_r1_p2 :
    ((Finset.Icc 3 2018).filter HasNRing).card = solution_value := by
  sorry

end UK2019R1P2
