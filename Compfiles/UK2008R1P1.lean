/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2008, Round 1, Problem 1

Find the value of (1⁴ + 2007⁴ + 2008⁴) / (1² + 2007² + 2008²).
-/

namespace UK2008R1P1

determine solution_value : ℕ := 4030057

problem uk2008_r1_p1 :
    (1^4 + 2007^4 + 2008^4) / (1^2 + 2007^2 + 2008^2) = solution_value := by
  decide

end UK2008R1P1
