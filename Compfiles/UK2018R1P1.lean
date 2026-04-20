/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2018, Round 1, Problem 1

Helen divides 365 by each of 1, 2, 3, …, 365 in turn, writing down a list of
the 365 remainders. Then Phil divides 366 by each of 1, 2, 3, …, 366 in turn,
writing down a list of the 366 remainders. Whose list of remainders has the
greater sum and by how much?

The answer is: Helen's list has the greater sum, by 13.
-/

namespace UK2018R1P1

/-- The difference (Helen's sum) − (Phil's sum). A positive value means
Helen's sum is greater by that amount. -/
determine solution_value : ℤ := 13

problem uk2018_r1_p1 :
    (∑ k ∈ Finset.range 365, ((365 : ℤ) % (k + 1))) -
      (∑ k ∈ Finset.range 366, ((366 : ℤ) % (k + 1))) = solution_value := by
  native_decide

end UK2018R1P1
