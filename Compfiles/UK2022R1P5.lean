/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2022, Round 1, Problem 5

An N-set is a set of different positive integers including a given positive
integer N. Let m(N) be the smallest possible mean of any N-set. For how many
values of N less than 2021 is m(N) an integer?
-/

namespace UK2022R1P5

/-- An N-set: a finite set `S` of positive integers containing `N`. The mean is
    `S.sum id / S.card`. We ask for which `N` the minimum (rational) mean over
    all N-sets is an integer. -/
def Mean (S : Finset ℕ) : ℚ := ((S.sum id : ℕ) : ℚ) / S.card

/-- `MNIsInteger N` says the infimum of means of N-sets is attained at an
    integer value. -/
def MNIsInteger (N : ℕ) : Prop :=
  ∃ q : ℤ, IsGLB
    ((fun S : Finset ℕ => Mean S) ''
       { S | (∀ x ∈ S, 0 < x) ∧ N ∈ S }) (q : ℚ)

determine solution_value : ℕ := 0 -- placeholder for the true count

open scoped Classical in
problem uk2022_r1_p5 :
    ((Finset.Ico 1 2021).filter MNIsInteger).card = solution_value := by
  sorry

end UK2022R1P5
