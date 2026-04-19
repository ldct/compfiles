/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2017, Round 1, Problem 3

Determine all pairs (m, n) of positive integers which satisfy the equation
n² − 6n = m² + m − 10.
-/

namespace UK2017R1P3

/-- Rewriting: (n − 3)² − 9 = m² + m − 10, so (n − 3)² = m² + m − 1,
    giving 4(n − 3)² = (2m + 1)² − 5. Equivalently
    (2m + 1 − 2(n − 3))(2m + 1 + 2(n − 3)) = 5. Case analysis on the
    factorisation of 5 yields (m, n) = (1, 2) and (m, n) = (1, 4). -/
determine solution_set : Set (ℕ × ℕ) := { (1, 2), (1, 4) }

problem uk2017_r1_p3 :
    { mn : ℕ × ℕ | 0 < mn.1 ∧ 0 < mn.2 ∧
        (mn.2 : ℤ)^2 - 6 * mn.2 = (mn.1 : ℤ)^2 + mn.1 - 10 } = solution_set := by
  sorry

end UK2017R1P3
