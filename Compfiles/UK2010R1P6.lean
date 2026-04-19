/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2010, Round 1, Problem 6

Long John Silverman has captured a treasure map from Adam McBones. Adam has
buried the treasure at the point (x, y) with integer co-ordinates (not
necessarily positive). He has indicated on the map the values of x² + y and
x + y², and these numbers are distinct. Prove that Long John has to dig only
in one place to find the treasure.

That is: if (x, y) and (a, b) are pairs of integers with x² + y = a² + b,
x + y² = a + b² and x² + y ≠ x + y², then (x, y) = (a, b).
-/

namespace UK2010R1P6

problem uk2010_r1_p6 :
    ∀ x y a b : ℤ,
      x^2 + y = a^2 + b →
      x + y^2 = a + b^2 →
      x^2 + y ≠ x + y^2 →
      (x, y) = (a, b) := by
  intro x y a b h1 h2 hne
  -- From h1: x² - a² = b - y, i.e., (x-a)(x+a) = b - y
  -- From h2: y² - b² = a - x, i.e., (y-b)(y+b) = a - x = -(x-a)
  -- If x = a, then from h1: y = b. Done.
  -- Suppose x ≠ a. Then (x-a)(x+a) = b-y and (y-b)(y+b) = -(x-a).
  -- Multiply: (x-a)(x+a)(y-b)(y+b) = -(x-a)(b-y) = (x-a)(y-b)
  -- So (x-a)(y-b)[(x+a)(y+b) - 1] = 0... wait let me redo.
  -- (x-a)(x+a) = b-y = -(y-b), so if y ≠ b, (x-a)(x+a) = -(y-b).
  -- (y-b)(y+b) = -(x-a).
  -- Multiply: (x-a)(y-b)(x+a)(y+b) = (y-b)(x-a)  [using (b-y)(a-x)? let me recompute]
  --
  -- h1: (x-a)(x+a) = b-y
  -- h2: (y-b)(y+b) = a-x
  -- So (x-a)(x+a) = -(y-b)  and  (y-b)(y+b) = -(x-a)
  -- Multiply: (x-a)(y-b)(x+a)(y+b) = (y-b)(x-a)
  -- If (x-a)(y-b) ≠ 0, then (x+a)(y+b) = 1.
  -- Also, if x ≠ a then y ≠ b (from h1), and vice versa.
  by_contra hcontra
  have hxa : x ≠ a := by
    intro hxa
    apply hcontra
    have hyb : y = b := by rw [hxa] at h1; linarith
    rw [hxa, hyb]
  have hyb : y ≠ b := by
    intro hyb
    apply hxa
    have : x^2 = a^2 := by rw [hyb] at h1; linarith
    -- x = a or x = -a; combined with h2 which gives a - x = 0
    have hax : a = x := by rw [hyb] at h2; linarith
    exact hax.symm
  -- From h1: (x-a)(x+a) = b - y ≠ 0, so x ≠ -a too (else LHS = 0).
  -- Multiply derived equations
  have hmul : (x - a) * (y - b) * ((x + a) * (y + b) - 1) = 0 := by nlinarith [h1, h2]
  have hne1 : (x - a) ≠ 0 := sub_ne_zero.mpr hxa
  have hne2 : (y - b) ≠ 0 := sub_ne_zero.mpr hyb
  have hkey : (x + a) * (y + b) = 1 := by
    have := mul_eq_zero.mp hmul
    rcases this with h | h
    · exfalso
      rcases mul_eq_zero.mp h with h' | h'
      · exact hne1 h'
      · exact hne2 h'
    · linarith
  -- (x+a)(y+b) = 1 in ℤ means x+a = y+b = 1 or x+a = y+b = -1
  have hunits : (x + a = 1 ∧ y + b = 1) ∨ (x + a = -1 ∧ y + b = -1) := by
    have hu : IsUnit (x + a) := IsUnit.of_mul_eq_one (a := x + a) (y + b) hkey
    rcases Int.isUnit_iff.mp hu with h | h
    · left
      refine ⟨h, ?_⟩
      rw [h] at hkey; linarith
    · right
      refine ⟨h, ?_⟩
      rw [h] at hkey; linarith
  -- Now derive contradiction from hne
  apply hne
  rcases hunits with ⟨hxa1, hyb1⟩ | ⟨hxa1, hyb1⟩
  · -- x + a = 1 and y + b = 1, so a = 1-x, b = 1-y
    have ha : a = 1 - x := by linarith
    have hb : b = 1 - y := by linarith
    -- h1: x² + y = (1-x)² + (1-y) = 1 - 2x + x² + 1 - y; so y = 2 - 2x - y; 2y = 2 - 2x; y = 1-x
    have hx_val : x = 1 - y := by rw [ha, hb] at h1; nlinarith [h1]
    show x^2 + y = x + y^2
    rw [hx_val]; ring
  · -- x + a = -1, y + b = -1
    have ha : a = -1 - x := by linarith
    have hb : b = -1 - y := by linarith
    have hx_val : x = y := by rw [ha, hb] at h1; nlinarith [h1]
    show x^2 + y = x + y^2
    rw [hx_val]; ring

end UK2010R1P6
