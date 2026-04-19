/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2013, Round 1, Problem 3

Find all real numbers x, y and z which satisfy the simultaneous equations
x² − 4y + 7 = 0, y² − 6z + 14 = 0 and z² − 2x − 7 = 0.
-/

namespace UK2013R1P3

problem uk2013_r1_p3 (x y z : ℝ) :
    (x^2 - 4*y + 7 = 0 ∧ y^2 - 6*z + 14 = 0 ∧ z^2 - 2*x - 7 = 0) ↔
      (x = 1 ∧ y = 2 ∧ z = 3) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    -- Adding: (x-1)² + (y-2)² + (z-3)² = 0.
    have hkey : (x - 1)^2 + (y - 2)^2 + (z - 3)^2 = 0 := by linarith
    have hx : (x - 1)^2 = 0 := by nlinarith [sq_nonneg (x-1), sq_nonneg (y-2), sq_nonneg (z-3)]
    have hy : (y - 2)^2 = 0 := by nlinarith [sq_nonneg (x-1), sq_nonneg (y-2), sq_nonneg (z-3)]
    have hz : (z - 3)^2 = 0 := by nlinarith [sq_nonneg (x-1), sq_nonneg (y-2), sq_nonneg (z-3)]
    refine ⟨?_, ?_, ?_⟩
    · have := sq_eq_zero_iff.mp hx; linarith
    · have := sq_eq_zero_iff.mp hy; linarith
    · have := sq_eq_zero_iff.mp hz; linarith
  · rintro ⟨hx, hy, hz⟩
    subst hx; subst hy; subst hz
    refine ⟨?_, ?_, ?_⟩ <;> norm_num

end UK2013R1P3
