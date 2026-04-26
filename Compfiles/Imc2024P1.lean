/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2024, Problem 1

Determine all pairs `(a, b) ∈ ℂ × ℂ` satisfying `|a| = |b| = 1` and
`a + b + a * conj b ∈ ℝ`.

Answer: `(1, b)` with `|b| = 1`, `(a, -1)` with `|a| = 1`,
or `(a, -a)` with `|a| = 1`.
-/

namespace Imc2024P1

open Complex

/-- The set of pairs `(a, b)` satisfying the answer condition:
`|a| = |b| = 1` and at least one of `a = 1`, `b = -1`, `a + b = 0`. -/
determine answer : Set (ℂ × ℂ) :=
  {p | ‖p.1‖ = 1 ∧ ‖p.2‖ = 1 ∧ (p.1 = 1 ∨ p.2 = -1 ∨ p.1 + p.2 = 0)}

snip begin

/-- For complex numbers with `|a| = 1`, we have `a * conj a = 1`. -/
lemma mul_conj_of_norm_one {a : ℂ} (ha : ‖a‖ = 1) : a * (starRingEnd ℂ) a = 1 := by
  have hnm : a * (starRingEnd ℂ) a = ((Complex.normSq a : ℝ) : ℂ) := Complex.mul_conj a
  rw [hnm, Complex.normSq_eq_norm_sq, ha]
  push_cast; ring

/-- `z.im = 0` iff `z = conj z`. -/
lemma im_eq_zero_iff_eq_conj (z : ℂ) : z.im = 0 ↔ z = (starRingEnd ℂ) z := by
  constructor
  · intro h
    apply Complex.ext
    · simp
    · simp [h]
  · intro h
    have : z.im = -z.im := by
      have := congrArg Complex.im h
      simpa using this
    linarith

/-- The key algebraic fact: if `|a| = |b| = 1`, then the imaginary part of
`a + b + a * conj b` vanishes iff `(a - 1) * (b + 1) * (a + b) = 0`. -/
lemma reality_iff_factor (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    (a + b + a * (starRingEnd ℂ) b).im = 0 ↔
      (a - 1) * (b + 1) * (a + b) = 0 := by
  have haa : a * (starRingEnd ℂ) a = 1 := mul_conj_of_norm_one ha
  have hbb : b * (starRingEnd ℂ) b = 1 := mul_conj_of_norm_one hb
  have ha_ne : a ≠ 0 := by
    intro h; rw [h, norm_zero] at ha; norm_num at ha
  have hb_ne : b ≠ 0 := by
    intro h; rw [h, norm_zero] at hb; norm_num at hb
  have hab_ne : a * b ≠ 0 := mul_ne_zero ha_ne hb_ne
  -- Step 1: reduce reality condition to a polynomial equation.
  -- `z.im = 0 ↔ z = conj z`, and with `conj (a+b+a*conj b) = conj a + conj b + conj a * b`,
  -- multiplying both sides by `a*b` gives a polynomial equation.
  rw [im_eq_zero_iff_eq_conj]
  constructor
  · intro h
    -- h: a + b + a * conj b = conj a + conj b + conj a * b (after simp)
    -- Multiply by a*b and use |a|=|b|=1 to clear conjugates.
    have h' : (a * b) * (a + b + a * (starRingEnd ℂ) b) =
              (a * b) * ((starRingEnd ℂ) a + (starRingEnd ℂ) b + (starRingEnd ℂ) a * b) := by
      conv_lhs => rw [h]
      simp [map_add, map_mul]
    -- LHS = a^2*b + a*b^2 + a^2 * (b*conj b) = a^2*b + a*b^2 + a^2
    -- RHS = a*conj a * b + b*conj b * a + a * conj a * b^2 = b + a + b^2
    have hlhs : (a * b) * (a + b + a * (starRingEnd ℂ) b) = a^2 * b + a * b^2 + a^2 := by
      have eq1 : (a * b) * (a + b + a * (starRingEnd ℂ) b) =
             a^2 * b + a * b^2 + a^2 * (b * (starRingEnd ℂ) b) := by ring
      rw [eq1, hbb]; ring
    have hrhs : (a * b) * ((starRingEnd ℂ) a + (starRingEnd ℂ) b + (starRingEnd ℂ) a * b) =
                  b + a + b^2 := by
      have eq2 : (a * b) * ((starRingEnd ℂ) a + (starRingEnd ℂ) b + (starRingEnd ℂ) a * b) =
             (a * (starRingEnd ℂ) a) * b + (b * (starRingEnd ℂ) b) * a
               + (a * (starRingEnd ℂ) a) * b^2 := by ring
      rw [eq2, haa, hbb]; ring
    rw [hlhs, hrhs] at h'
    linear_combination h'
  · intro h
    -- h: (a - 1) * (b + 1) * (a + b) = 0
    -- Want: a + b + a * conj b = conj (a + b + a * conj b)
    -- Equivalently: (a*b) * LHS = (a*b) * RHS.
    apply mul_left_cancel₀ hab_ne
    simp only [map_add, map_mul, Complex.conj_conj]
    have hlhs : (a * b) * (a + b + a * (starRingEnd ℂ) b) = a^2 * b + a * b^2 + a^2 := by
      have eq1 : (a * b) * (a + b + a * (starRingEnd ℂ) b) =
             a^2 * b + a * b^2 + a^2 * (b * (starRingEnd ℂ) b) := by ring
      rw [eq1, hbb]; ring
    have hrhs : (a * b) * ((starRingEnd ℂ) a + (starRingEnd ℂ) b + (starRingEnd ℂ) a * b) =
                  b + a + b^2 := by
      have eq2 : (a * b) * ((starRingEnd ℂ) a + (starRingEnd ℂ) b + (starRingEnd ℂ) a * b) =
             (a * (starRingEnd ℂ) a) * b + (b * (starRingEnd ℂ) b) * a
               + (a * (starRingEnd ℂ) a) * b^2 := by ring
      rw [eq2, haa, hbb]; ring
    rw [hlhs, hrhs]
    linear_combination h

snip end

problem imc2024_p1 (a b : ℂ) :
    (a, b) ∈ answer ↔
      ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ (a + b + a * (starRingEnd ℂ) b).im = 0 := by
  show (‖a‖ = 1 ∧ ‖b‖ = 1 ∧ (a = 1 ∨ b = -1 ∨ a + b = 0)) ↔ _
  constructor
  · rintro ⟨ha, hb, hcases⟩
    refine ⟨ha, hb, ?_⟩
    rw [reality_iff_factor a b ha hb]
    rcases hcases with h1 | h1 | h1
    · rw [h1]; ring
    · rw [h1]; ring
    · rw [show (a - 1) * (b + 1) * (a + b) = (a - 1) * (b + 1) * (a + b) from rfl, h1,
          mul_zero]
  · rintro ⟨ha, hb, him⟩
    refine ⟨ha, hb, ?_⟩
    rw [reality_iff_factor a b ha hb] at him
    rcases mul_eq_zero.mp him with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · left; linear_combination h'
      · right; left; linear_combination h'
    · right; right; exact h

end Imc2024P1
