/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# British Mathematical Olympiad 2017, Round 1, Problem 1

The integers 1, 2, 3, . . . , 2016 are written down in base 10, each appearing
exactly once. Each of the digits from 0 to 9 appears many times in the list.
How many of the digits in the list are odd? For example, 8 odd digits appear
in the list 1, 2, 3, . . . , 11.
-/

namespace UK2017R1P1

/-- The number of odd digits among the decimal digits of `k`. -/
def oddDigitsOf (k : ℕ) : ℕ :=
  ((Nat.digits 10 k).filter (fun d => d % 2 = 1)).length

/-- Total number of odd digits appearing in the base-10 representations
of 1, 2, …, 2016. -/
def totalOddDigits : ℕ :=
  ∑ k ∈ Finset.Icc 1 2016, oddDigitsOf k

determine solution_value : ℕ := 4015

problem uk2017_r1_p1 : totalOddDigits = solution_value := by
  unfold totalOddDigits oddDigitsOf
  native_decide

end UK2017R1P1
