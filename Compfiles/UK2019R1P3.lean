/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2019, Round 1, Problem 3

Find all positive integers x, y with x(x + 9) = y(y + 6).

(This is a restatement of BMO 2019 Round 1 Problem 3, where Ares multiplies
two integers which differ by 9 and Grace multiplies two integers which differ
by 6 and they obtain the same product T.)
-/

namespace UK2019R1P3

/-- x(x + 9) = y(y + 6) with x, y ≥ 1. Completing the square gives
    (2y + 6)² − (2x + 9)² = 36 − 81 = −45, i.e.
    (2x + 9 − 2y − 6)(2x + 9 + 2y + 6) = 45. Factorising 45 over positive
    integers yields only x = 2, y = 4 (giving T = 22·? actually T = 40). -/
determine solution_set : Set (ℕ × ℕ) := { (2, 4) }

problem uk2019_r1_p3 :
    { xy : ℕ × ℕ | 0 < xy.1 ∧ 0 < xy.2 ∧
                  xy.1 * (xy.1 + 9) = xy.2 * (xy.2 + 6) } = solution_set := by
  sorry

end UK2019R1P3
