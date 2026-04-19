/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2014, Round 1, Problem 1

Calculate the value of
(2014⁴ + 4 × 2013⁴)/(2013² + 4027²) − (2012⁴ + 4 × 2013⁴)/(2013² + 4025²).
-/

namespace UK2014R1P1

determine solution_value : ℤ := 0

problem uk2014_r1_p1 :
    (2014^4 + 4 * 2013^4) / (2013^2 + 4027^2)
      - (2012^4 + 4 * 2013^4) / (2013^2 + 4025^2) = solution_value := by
  decide

end UK2014R1P1
