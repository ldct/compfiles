/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2000, Problem 2

Let `p(x) = x^5 + x` and `q(x) = x^5 + x^2`. Find all complex pairs `(w, z)`
with `w ≠ z` such that `p(w) = p(z)` and `q(w) = q(z)`.

The answer is: `w + z = 1` and `w * z ∈ {1, 2}`.
-/

namespace Imc2000P2

/-- The set of pairs `(w, z)` of distinct complex numbers with `p(w)=p(z)`
and `q(w)=q(z)`, where `p(x)=x^5+x` and `q(x)=x^5+x^2`. -/
determine answer : Set (ℂ × ℂ) :=
  {wz | wz.1 + wz.2 = 1 ∧ (wz.1 * wz.2 = 1 ∨ wz.1 * wz.2 = 2) ∧ wz.1 ≠ wz.2}

problem imc2000_p2 (w z : ℂ) :
    ((w, z) ∈ answer) ↔
      (w ≠ z ∧ w^5 + w = z^5 + z ∧ w^5 + w^2 = z^5 + z^2) := by
  unfold answer
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hsum, hprod, hne⟩
    refine ⟨hne, ?_, ?_⟩
    · -- From w + z = 1 and wz ∈ {1, 2}, deduce w^5 + w = z^5 + z.
      -- We have w^5 - z^5 = (w - z)(w^4 + w^3 z + w^2 z^2 + w z^3 + z^4)
      -- and w^4 + w^3 z + w^2 z^2 + w z^3 + z^4 = 1 - 3c + c^2 where c = wz.
      -- When c = 1 or c = 2, this equals -1, so w^5 - z^5 = -(w - z), giving
      -- w^5 + w = z^5 + z.
      have hzeq : z = 1 - w := by linear_combination hsum
      rcases hprod with hc | hc
      · -- wz = 1: z = 1 - w, so w(1 - w) = 1, i.e., w^2 - w + 1 = 0.
        have hweq : w^2 - w + 1 = 0 := by
          have hh : w * (1 - w) = 1 := by rw [← hzeq]; exact hc
          linear_combination -hh
        -- Then w^3 = -1 (from w^2 = w - 1, so w^3 = w^2 - w = -1).
        have hw3 : w^3 = -1 := by linear_combination (w + 1) * hweq
        -- Similarly z^2 - z + 1 = 0, so z^3 = -1.
        have hzeq' : z^2 - z + 1 = 0 := by
          rw [hzeq]; linear_combination hweq
        have hz3 : z^3 = -1 := by linear_combination (z + 1) * hzeq'
        -- w^5 = w^3 * w^2 = -w^2 = -(w - 1) = 1 - w.
        have hw5 : w^5 = 1 - w := by linear_combination w^2 * hw3 - hweq
        have hz5 : z^5 = 1 - z := by linear_combination z^2 * hz3 - hzeq'
        linear_combination hw5 - hz5
      · -- wz = 2: then w^2 - w + 2 = 0, and z^2 - z + 2 = 0.
        have hweq : w^2 - w + 2 = 0 := by
          have hh : w * (1 - w) = 2 := by rw [← hzeq]; exact hc
          linear_combination -hh
        have hzeq' : z^2 - z + 2 = 0 := by
          rw [hzeq]; linear_combination hweq
        -- w^2 = w - 2, so w^3 = w^2 - 2w = -w - 2, w^4 = -w^2 - 2w = -3w + 2,
        -- w^5 = -3w^2 + 2w = -3(w-2) + 2w = -w + 6.
        have hw5 : w^5 = -w + 6 := by linear_combination (w^3 + w^2 - w - 3) * hweq
        have hz5 : z^5 = -z + 6 := by linear_combination (z^3 + z^2 - z - 3) * hzeq'
        linear_combination hw5 - hz5
    · -- Similarly for q: w^5 + w^2 = z^5 + z^2. Use w^5 relations + sum/prod.
      have hzeq : z = 1 - w := by linear_combination hsum
      rcases hprod with hc | hc
      · have hweq : w^2 - w + 1 = 0 := by
          have hh : w * (1 - w) = 1 := by rw [← hzeq]; exact hc
          linear_combination -hh
        have hzeq' : z^2 - z + 1 = 0 := by rw [hzeq]; linear_combination hweq
        have hw3 : w^3 = -1 := by linear_combination (w + 1) * hweq
        have hz3 : z^3 = -1 := by linear_combination (z + 1) * hzeq'
        have hw5 : w^5 = 1 - w := by linear_combination w^2 * hw3 - hweq
        have hz5 : z^5 = 1 - z := by linear_combination z^2 * hz3 - hzeq'
        -- w^5 + w^2 = (1 - w) + (w - 1) = 0; similarly z^5 + z^2 = 0.
        have hwsum : w^5 + w^2 = 0 := by linear_combination hw5 + hweq
        have hzsum : z^5 + z^2 = 0 := by linear_combination hz5 + hzeq'
        linear_combination hwsum - hzsum
      · have hweq : w^2 - w + 2 = 0 := by
          have hh : w * (1 - w) = 2 := by rw [← hzeq]; exact hc
          linear_combination -hh
        have hzeq' : z^2 - z + 2 = 0 := by rw [hzeq]; linear_combination hweq
        have hw5 : w^5 = -w + 6 := by linear_combination (w^3 + w^2 - w - 3) * hweq
        have hz5 : z^5 = -z + 6 := by linear_combination (z^3 + z^2 - z - 3) * hzeq'
        -- w^5 + w^2 = (-w + 6) + (w - 2) = 4; similarly z^5 + z^2 = 4.
        have hwsum : w^5 + w^2 = 4 := by linear_combination hw5 + hweq
        have hzsum : z^5 + z^2 = 4 := by linear_combination hz5 + hzeq'
        linear_combination hwsum - hzsum
  · rintro ⟨hne, hp, hq⟩
    -- From p(w) = p(z): w^5 - z^5 + (w - z) = 0, divide by (w - z):
    -- w^4 + w^3 z + w^2 z^2 + w z^3 + z^4 + 1 = 0.
    have hne' : w - z ≠ 0 := sub_ne_zero.mpr hne
    have hP : w^4 + w^3 * z + w^2 * z^2 + w * z^3 + z^4 + 1 = 0 := by
      have hfact : (w - z) * (w^4 + w^3 * z + w^2 * z^2 + w * z^3 + z^4 + 1)
          = (w^5 + w) - (z^5 + z) := by ring
      have hzero : (w^5 + w) - (z^5 + z) = 0 := by linear_combination hp
      rw [hzero] at hfact
      exact (mul_eq_zero.mp hfact).resolve_left hne'
    -- From q(w) = q(z): similarly
    -- w^4 + w^3 z + w^2 z^2 + w z^3 + z^4 + w + z = 0.
    have hQ : w^4 + w^3 * z + w^2 * z^2 + w * z^3 + z^4 + w + z = 0 := by
      have hfact : (w - z) * (w^4 + w^3 * z + w^2 * z^2 + w * z^3 + z^4 + w + z)
          = (w^5 + w^2) - (z^5 + z^2) := by ring
      have hzero : (w^5 + w^2) - (z^5 + z^2) = 0 := by linear_combination hq
      rw [hzero] at hfact
      exact (mul_eq_zero.mp hfact).resolve_left hne'
    -- Subtract: w + z - 1 = 0, so w + z = 1.
    have hsum : w + z = 1 := by linear_combination hQ - hP
    refine ⟨hsum, ?_, hne⟩
    -- Substitute w + z = 1 into hP.
    -- hP: w^4 + w^3 z + w^2 z^2 + w z^3 + z^4 = -1
    -- w^4 + z^4 = (w^2+z^2)^2 - 2(wz)^2 = ((w+z)^2 - 2wz)^2 - 2(wz)^2
    --           = (1 - 2c)^2 - 2c^2 = 1 - 4c + 2c^2
    -- w^3 z + w z^3 = wz((w+z)^2 - 2wz) = c(1 - 2c) = c - 2c^2
    -- w^2 z^2 = c^2
    -- Sum = 1 - 3c + c^2. So c^2 - 3c + 2 = 0, i.e., (c - 1)(c - 2) = 0.
    set c := w * z with hcdef
    have hkey : c^2 - 3 * c + 2 = 0 := by
      have hzeq : z = 1 - w := by linear_combination hsum
      rw [hzeq] at hP
      rw [hcdef, hzeq]
      linear_combination hP
    have hfact2 : (c - 1) * (c - 2) = 0 := by linear_combination hkey
    rcases mul_eq_zero.mp hfact2 with h1 | h2
    · left; linear_combination h1
    · right; linear_combination h2

end Imc2000P2
