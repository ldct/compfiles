/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Inequality] }

/-!
# British Mathematical Olympiad 2007, Round 1, Problem 5

For positive real numbers a, b, c, prove that
(a² + b²)² ≥ (a + b + c)(a + b − c)(b + c − a)(c + a − b).
-/

namespace UK2007R1P5

problem uk2007_r1_p5 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 2 + b ^ 2) ^ 2 ≥ (a + b + c) * (a + b - c) * (b + c - a) * (c + a - b) := by
  nlinarith [sq_nonneg ((a^2 + b^2) - c^2), sq_nonneg (a^2 - b^2),
             sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a + b - c),
             sq_nonneg (a*b), mul_pos ha hb, mul_pos hb hc, mul_pos hc ha,
             sq_nonneg a, sq_nonneg b, sq_nonneg c, ha.le, hb.le, hc.le]

end UK2007R1P5
