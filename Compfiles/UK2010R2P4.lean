/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Inequality] }

/-!
# British Mathematical Olympiad 2010, Round 2, Problem 4

Prove that, for all positive real numbers x, y and z,
4(x + y + z)³ > 27(x²y + y²z + z²x).
-/

namespace UK2010R2P4

problem uk2010_r2_p4 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    4 * (x + y + z) ^ 3 > 27 * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) := by
  have h1 : 0 ≤ (x - 2*y)^2 * (4*x + y) := by positivity
  have h2 : 0 ≤ (y - 2*z)^2 * (4*y + z) := by positivity
  have h3 : 0 ≤ (z - 2*x)^2 * (4*z + x) := by positivity
  -- We need strict inequality. Use that xyz > 0.
  nlinarith [h1, h2, h3, mul_pos (mul_pos hx hy) hz,
             sq_nonneg (x - 2*y), sq_nonneg (y - 2*z), sq_nonneg (z - 2*x),
             hx, hy, hz, mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]

end UK2010R2P4
