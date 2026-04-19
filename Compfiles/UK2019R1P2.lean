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

/-- The answer is the number of such n in [3, 2018]. -/
determine solution_value : ℕ := 0 -- placeholder for the true count

open scoped Classical in
problem uk2019_r1_p2 :
    ((Finset.Icc 3 2018).filter HasNRing).card = solution_value := by
  sorry

end UK2019R1P2
