/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2008, Round 1, Problem 2

Find all solutions in positive integers x, y, z to the simultaneous equations
x + y − z = 12
x² + y² − z² = 12.
-/

namespace UK2008R1P2

determine solution_set : Set (ℕ × ℕ × ℕ) :=
  { (13, 78, 79), (78, 13, 79),
    (14, 45, 47), (45, 14, 47),
    (15, 34, 37), (34, 15, 37),
    (18, 23, 29), (23, 18, 29) }

problem uk2008_r1_p2 :
    { xyz : ℕ × ℕ × ℕ | 0 < xyz.1 ∧ 0 < xyz.2.1 ∧ 0 < xyz.2.2 ∧
        (xyz.1 : ℤ) + xyz.2.1 - xyz.2.2 = 12 ∧
        (xyz.1 : ℤ)^2 + (xyz.2.1 : ℤ)^2 - (xyz.2.2 : ℤ)^2 = 12 } = solution_set := by
  sorry

end UK2008R1P2
