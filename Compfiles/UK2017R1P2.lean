/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2017, Round 1, Problem 2

For each positive real number x, we define {x} to be the greater of x
and 1/x, with {1} = 1. Find, with proof, all positive real numbers y
such that 5y{8y}{25y} = 1.
-/

namespace UK2017R1P2

/-- The operation {x} = max(x, 1/x) for positive reals. -/
noncomputable def curly (x : ℝ) : ℝ := max x (1 / x)

determine solution_set : Set ℝ :=
  { y | y = 1 / 40 ∨ y = 8 / 125 }

problem uk2017_r1_p2 (y : ℝ) (hy : 0 < y) :
    y ∈ solution_set ↔ 5 * y * curly (8 * y) * curly (25 * y) = 1 := by
  simp only [solution_set, Set.mem_setOf_eq]
  constructor
  · rintro (rfl | rfl)
    · -- y = 1/40: 8y = 1/5 < 1, curly(1/5) = 5. 25y = 25/40 = 5/8 < 1, curly = 8/5.
      -- 5 · (1/40) · 5 · (8/5) = 1.
      unfold curly
      have h1 : (8 : ℝ) * (1 / 40) = 1/5 := by ring
      have h2 : (25 : ℝ) * (1 / 40) = 5/8 := by ring
      rw [h1, h2]
      have hm1 : max (1/5 : ℝ) (1 / (1/5)) = 5 := by
        rw [max_eq_right (by norm_num : (1/5 : ℝ) ≤ 1 / (1/5))]; norm_num
      have hm2 : max (5/8 : ℝ) (1 / (5/8)) = 8/5 := by
        rw [max_eq_right (by norm_num : (5/8 : ℝ) ≤ 1 / (5/8))]; norm_num
      rw [hm1, hm2]; ring
    · -- y = 8/125: 8y = 64/125 < 1, curly = 125/64. 25y = 200/125 = 8/5 ≥ 1, curly = 8/5.
      unfold curly
      have h1 : (8 : ℝ) * (8 / 125) = 64/125 := by ring
      have h2 : (25 : ℝ) * (8 / 125) = 8/5 := by ring
      rw [h1, h2]
      have hm1 : max (64/125 : ℝ) (1 / (64/125)) = 125/64 := by
        rw [max_eq_right (by norm_num : (64/125 : ℝ) ≤ 1 / (64/125))]; norm_num
      have hm2 : max (8/5 : ℝ) (1 / (8/5)) = 8/5 := by
        rw [max_eq_left (by norm_num : 1 / (8/5 : ℝ) ≤ 8/5)]
      rw [hm1, hm2]; ring
  · intro heq
    -- Case split on whether 8y ≥ 1 and whether 25y ≥ 1.
    unfold curly at heq
    have h8y_pos : (0 : ℝ) < 8 * y := by linarith
    have h25y_pos : (0 : ℝ) < 25 * y := by linarith
    by_cases hc1 : 1 ≤ 8 * y
    · -- curly(8y) = 8y
      have hcurly8 : max (8 * y) (1 / (8 * y)) = 8 * y := by
        apply max_eq_left
        have hinv : 1 / (8 * y) ≤ 1 := by
          rw [div_le_one h8y_pos]; exact hc1
        linarith
      rw [hcurly8] at heq
      -- Since 8y ≥ 1, y ≥ 1/8, so 25y ≥ 25/8 > 1. So curly(25y) = 25y.
      have hc2 : 1 ≤ 25 * y := by linarith
      have hcurly25 : max (25 * y) (1 / (25 * y)) = 25 * y := by
        apply max_eq_left
        have hinv : 1 / (25 * y) ≤ 1 := by
          rw [div_le_one h25y_pos]; exact hc2
        linarith
      rw [hcurly25] at heq
      -- 5y·8y·25y = 1000 y³ = 1 ⇒ y = 1/10. But y ≥ 1/8, contradiction.
      exfalso
      have hy3 : 1000 * y^3 = 1 := by nlinarith [heq]
      -- But y ≥ 1/8, so y³ ≥ 1/512, so 1000 y³ ≥ 1000/512 > 1. Contradiction.
      have hyl : 1/8 ≤ y := by linarith
      nlinarith [hy3, sq_nonneg y, sq_nonneg (y - 1/8), hyl, hy]
    · -- 8y < 1, so curly(8y) = 1/(8y).
      rw [not_le] at hc1
      have hcurly8 : max (8 * y) (1 / (8 * y)) = 1 / (8 * y) := by
        apply max_eq_right
        rw [le_div_iff₀ h8y_pos]
        nlinarith
      rw [hcurly8] at heq
      by_cases hc2 : 1 ≤ 25 * y
      · -- 25y ≥ 1: curly(25y) = 25y.
        have hcurly25 : max (25 * y) (1 / (25 * y)) = 25 * y := by
          apply max_eq_left
          have hinv : 1 / (25 * y) ≤ 1 := by
            rw [div_le_one h25y_pos]; exact hc2
          linarith
        rw [hcurly25] at heq
        -- 5y · 1/(8y) · 25y = 125y / 8 = 1 ⇒ y = 8/125.
        right
        have : 125 * y = 8 := by
          have := heq
          field_simp at this
          linarith
        linarith
      · -- 25y < 1: curly(25y) = 1/(25y).
        rw [not_le] at hc2
        have hcurly25 : max (25 * y) (1 / (25 * y)) = 1 / (25 * y) := by
          apply max_eq_right
          rw [le_div_iff₀ h25y_pos]
          nlinarith
        rw [hcurly25] at heq
        -- 5y · 1/(8y) · 1/(25y) = 5/(8·25·y) = 1/(40y) = 1 ⇒ y = 1/40.
        left
        have : 40 * y = 1 := by
          have := heq
          field_simp at this
          linarith
        linarith

end UK2017R1P2
