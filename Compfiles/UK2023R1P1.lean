/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2023, Round 1, Problem 1

A road has houses numbered from 1 to n, where n is a three-digit number.
Exactly 1/k of the numbers start with the digit 2, where k is a positive
integer. Find the possible values of n.
-/

namespace UK2023R1P1

/-- `startsWithTwo m` is true iff the base-10 representation of `m` starts
with the digit 2. -/
def startsWithTwo (m : ℕ) : Bool := (Nat.toDigits 10 m).head? = some '2'

/-- The number of integers in `[1, n]` whose base-10 representation starts
with the digit 2. -/
def countTwo (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter (fun m => startsWithTwo m)).card

determine solution_set : Finset ℕ :=
  {110, 121, 132, 143, 154, 165, 176, 187, 198, 235, 282, 333, 444, 555, 666, 777, 888, 999}

problem uk2023_r1_p1 :
    (Finset.Icc 100 999).filter
      (fun n => 0 < countTwo n ∧ n % countTwo n = 0) = solution_set := by
  native_decide

end UK2023R1P1
