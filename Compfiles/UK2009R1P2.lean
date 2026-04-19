/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2009, Round 1, Problem 2

Find all real values of x, y and z such that
(x + 1) y z = 12, (y + 1) z x = 4 and (z + 1) x y = 4.
-/

namespace UK2009R1P2

determine solution_set : Set (ℝ × ℝ × ℝ) :=
  {(2, -2, -2), (1/3, 3, 3)}

problem uk2009_r1_p2 (x y z : ℝ) :
    ((x + 1) * y * z = 12 ∧ (y + 1) * z * x = 4 ∧ (z + 1) * x * y = 4) ↔
      (x, y, z) ∈ solution_set := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    -- Subtract h2 and h3: (y+1)zx - (z+1)xy = x(z-y) = 0.
    have hx_or : x = 0 ∨ y = z := by
      have : x * (z - y) = 0 := by linarith
      rcases mul_eq_zero.mp this with hx | hyz
      · left; exact hx
      · right; linarith
    rcases hx_or with hx | hyz
    · exfalso; rw [hx] at h2; linarith
    · -- y = z.
      rw [← hyz] at h1 h2
      -- Now h1: (x+1) y² = 12, h2: (y+1) y x = 4.
      -- So (x+1)y² - x(y+1)y = 12 - 4 = 8, i.e., y² - xy = 8, i.e., xy = y² - 8.
      have hy_ne : y ≠ 0 := by
        intro hy0
        rw [hy0] at h1
        linarith
      have hcubic : y^3 + y^2 - 8 * y - 12 = 0 := by
        -- From h1: x y² + y² = 12. From h2: x y² + x y = 4.
        -- Subtract: y² - x y = 8, so x y = y² - 8.
        -- Substitute into h1: x y² = y(xy) = y(y²-8) = y³ - 8y.
        -- So y³ - 8y + y² = 12.
        have hxy : x * y = y^2 - 8 := by
          have e1 : (x + 1) * y * y = 12 := h1
          have e2 : (y + 1) * y * x = 4 := h2
          nlinarith [e1, e2, sq_nonneg y, hy_ne]
        -- From h1: (x+1) * y^2 = 12, i.e., x*y^2 + y^2 = 12.
        -- x*y^2 = y * (x*y) = y * (y^2 - 8) = y^3 - 8*y.
        have : x * y^2 + y^2 = 12 := by linarith [h1]
        have hxy2 : x * y^2 = y^3 - 8 * y := by
          have : x * y^2 = y * (x * y) := by ring
          rw [this, hxy]; ring
        linarith
      -- y^3 + y^2 - 8y - 12 = (y + 2)^2 * (y - 3).
      have hfactor : (y + 2)^2 * (y - 3) = 0 := by
        have : (y + 2)^2 * (y - 3) = y^3 + y^2 - 8 * y - 12 := by ring
        rw [this]; exact hcubic
      rcases mul_eq_zero.mp hfactor with hsq | h3
      · -- y = -2.
        have hy : y = -2 := by
          have := sq_eq_zero_iff.mp hsq
          linarith
        rw [hy] at h1
        have hx : x = 2 := by linarith
        have hz : z = -2 := by rw [← hyz]; exact hy
        left
        simp [hx, hy, hz]
      · -- y = 3.
        have hy : y = 3 := by linarith
        rw [hy] at h1
        have hx : x = 1/3 := by linarith
        have hz : z = 3 := by rw [← hyz]; exact hy
        right
        simp [hx, hy, hz]
  · intro h
    simp only [solution_set, Set.mem_insert_iff, Set.mem_singleton_iff,
               Prod.mk.injEq] at h
    rcases h with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ <;>
      · subst hx; subst hy; subst hz
        refine ⟨?_, ?_, ?_⟩ <;> norm_num

end UK2009R1P2
