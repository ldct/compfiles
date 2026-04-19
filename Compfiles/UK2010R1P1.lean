/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2010, Round 1, Problem 1

Find all positive integer solutions to x² + y² + z² = 2(yz + 1)
and x + y + z = 4018.
-/

namespace UK2010R1P1

/-- Rewriting: x² = 2 − (y − z)², so x² + (y − z)² = 2, forcing
    x = 1 and |y − z| = 1. Combined with x + y + z = 4018, we get
    (y, z) ∈ {(2008, 2009), (2009, 2008)}. -/
determine solution_set : Set (ℕ × ℕ × ℕ) :=
  { (1, 2008, 2009), (1, 2009, 2008) }

problem uk2010_r1_p1 :
    { xyz : ℕ × ℕ × ℕ | 0 < xyz.1 ∧ 0 < xyz.2.1 ∧ 0 < xyz.2.2 ∧
      (xyz.1 : ℤ)^2 + (xyz.2.1 : ℤ)^2 + (xyz.2.2 : ℤ)^2 =
        2 * ((xyz.2.1 : ℤ) * xyz.2.2 + 1) ∧
      xyz.1 + xyz.2.1 + xyz.2.2 = 4018 } = solution_set := by
  ext ⟨x, y, z⟩
  simp only [Set.mem_setOf_eq, solution_set, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx, hy, hz, heq, hsum⟩
    -- x² + (y - z)² = 2, over integers, so x = 1 and (y-z)² = 1
    have hsq : (x : ℤ)^2 + ((y : ℤ) - (z : ℤ))^2 = 2 := by ring_nf; linarith
    have hxsq_le : (x : ℤ)^2 ≤ 2 := by nlinarith [sq_nonneg ((y : ℤ) - (z : ℤ))]
    have hxpos : (1 : ℤ) ≤ x := by exact_mod_cast hx
    have hx1 : (x : ℤ) = 1 := by nlinarith [sq_nonneg ((x : ℤ) - 1), sq_nonneg ((x : ℤ) - 2)]
    have hx1' : x = 1 := by exact_mod_cast hx1
    have hyz_sq : ((y : ℤ) - (z : ℤ))^2 = 1 := by rw [hx1] at hsq; linarith
    have hyz_abs : (y : ℤ) - (z : ℤ) = 1 ∨ (y : ℤ) - (z : ℤ) = -1 := by
      have hfac : ((y : ℤ) - (z : ℤ) - 1) * ((y : ℤ) - (z : ℤ) + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hfac with h | h
      · left; linarith
      · right; linarith
    -- x + y + z = 4018 with x = 1 gives y + z = 4017
    rw [hx1'] at hsum
    rcases hyz_abs with h | h
    · -- y - z = 1, so y = z + 1, y + z = 4017 ⇒ z = 2008, y = 2009
      have hy : (y : ℤ) = (z : ℤ) + 1 := by linarith
      have hsumZ : (y : ℤ) + (z : ℤ) = 4017 := by exact_mod_cast (show y + z = 4017 by omega)
      have : (z : ℤ) = 2008 := by linarith
      have hz_eq : z = 2008 := by exact_mod_cast this
      have hy_eq : y = 2009 := by omega
      right; ext <;> simp [hx1', hy_eq, hz_eq]
    · -- y - z = -1, so z = y + 1, y + z = 4017 ⇒ y = 2008, z = 2009
      have hy : (z : ℤ) = (y : ℤ) + 1 := by linarith
      have hsumZ : (y : ℤ) + (z : ℤ) = 4017 := by exact_mod_cast (show y + z = 4017 by omega)
      have : (y : ℤ) = 2008 := by linarith
      have hy_eq : y = 2008 := by exact_mod_cast this
      have hz_eq : z = 2009 := by omega
      left; ext <;> simp [hx1', hy_eq, hz_eq]
  · rintro (h | h)
    · rw [Prod.mk.injEq, Prod.mk.injEq] at h
      obtain ⟨hx, hy, hz⟩ := h
      subst hx; subst hy; subst hz
      refine ⟨by decide, by decide, by decide, by norm_num, by decide⟩
    · rw [Prod.mk.injEq, Prod.mk.injEq] at h
      obtain ⟨hx, hy, hz⟩ := h
      subst hx; subst hy; subst hz
      refine ⟨by decide, by decide, by decide, by norm_num, by decide⟩

end UK2010R1P1
