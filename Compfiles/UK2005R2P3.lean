/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Inequality] }

/-!
# British Mathematical Olympiad 2005, Round 2, Problem 3

Let a, b, c be positive real numbers. Prove that
(a/b + b/c + c/a)² ≥ (a + b + c)(1/a + 1/b + 1/c).
-/

namespace UK2005R2P3

problem uk2005_r2_p3 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a / b + b / c + c / a) ^ 2 ≥ (a + b + c) * (1 / a + 1 / b + 1 / c) := by
  have hab : 0 < a * b := mul_pos ha hb
  have hbc : 0 < b * c := mul_pos hb hc
  have hca : 0 < c * a := mul_pos hc ha
  have habc : 0 < a * b * c := mul_pos hab hc
  have habc2 : 0 < (a * b * c) ^ 2 := by positivity
  rw [ge_iff_le, ← sub_nonneg]
  have key : ((a / b + b / c + c / a) ^ 2 - (a + b + c) * (1 / a + 1 / b + 1 / c))
      * (a * b * c) ^ 2 =
      a^2 * (a*c - b*c)^2 + b^2 * (a*b - a*c)^2 + c^2 * (b*c - a*b)^2
      + (a*b*c) * ((a - b)^2 * c + (b - c)^2 * a + (c - a)^2 * b) := by
    field_simp
    ring
  nlinarith [sq_nonneg (a*c - b*c), sq_nonneg (a*b - a*c), sq_nonneg (b*c - a*b),
             sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
             mul_pos ha hb, mul_pos hb hc, mul_pos hc ha, mul_pos habc habc,
             sq_nonneg a, sq_nonneg b, sq_nonneg c, key, habc2, habc]

end UK2005R2P3
