/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2010, Round 1, Problem 5

Find all functions f, defined on the real numbers and taking real values, which
satisfy the equation f(x)f(y) = f(x + y) + xy for all real numbers x and y.
-/

namespace UK2010R1P5

determine solution_set : Set (ℝ → ℝ) :=
  { (fun x => x + 1), (fun x => 1 - x) }

problem uk2010_r1_p5 :
    { f : ℝ → ℝ | ∀ x y, f x * f y = f (x + y) + x * y } =
    solution_set := by
  ext f
  simp only [Set.mem_setOf_eq, solution_set, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    -- f(0)^2 = f(0) + 0, so f(0) = 0 or 1
    have h00 := h 0 0
    simp at h00
    have hf0 : f 0 = 0 ∨ f 0 = 1 := by
      have : f 0 * (f 0 - 1) = 0 := by ring_nf; linarith [h00]
      rcases mul_eq_zero.mp this with h1 | h1
      · left; exact h1
      · right; linarith
    -- If f(0) = 0, then f(x)*0 = f(x) + 0 leads to f(x) = 0, contradicting FE with x=y=1
    have hf0_eq_one : f 0 = 1 := by
      rcases hf0 with h1 | h1
      · exfalso
        have hx0 := fun x => h x 0
        simp [h1] at hx0
        -- hx0 : ∀ x, 0 = f x
        have h11 := h 1 1
        rw [← hx0 1, ← hx0 (1+1)] at h11
        linarith
      · exact h1
    -- f(1)f(-1) = f(0) + 1*(-1) = 0
    have h1m1 := h 1 (-1)
    rw [show (1 : ℝ) + (-1) = 0 by ring, hf0_eq_one] at h1m1
    have hor : f 1 = 0 ∨ f (-1) = 0 := by
      have : f 1 * f (-1) = 0 := by linarith
      exact mul_eq_zero.mp this
    rcases hor with h1 | h1
    · -- Case f(1) = 0: f(x+1) = f(x)*0 - x = -x, so f(y) = 1 - y
      right
      funext x
      have hx := h (x - 1) 1
      rw [show (x - 1) + 1 = x by ring, h1] at hx
      linarith
    · -- Case f(-1) = 0: f(x-1) = f(x)*0 - x*(-1)... wait, let's redo
      -- h x (-1): f(x) f(-1) = f(x-1) + x*(-1), so 0 = f(x-1) - x, so f(x-1) = x, f(y) = y+1
      left
      funext x
      have hx := h (x + 1) (-1)
      rw [show (x + 1) + (-1) = x by ring, h1] at hx
      linarith
  · rintro (rfl | rfl)
    · intro x y; ring
    · intro x y; ring

end UK2010R1P5

