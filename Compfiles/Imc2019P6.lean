/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2019, Problem 6

Let `f, g : ℝ → ℝ` be continuous functions with `g` differentiable.
Assume that `(f(0) - g'(0)) * (g'(1) - f(1)) > 0`. Show that there exists
`c ∈ (0, 1)` with `f(c) = g'(c)`.
-/

namespace Imc2019P6

open Set Filter MeasureTheory intervalIntegral

problem imc2019_p6 (f g : ℝ → ℝ) (hf : Continuous f) (hg : Differentiable ℝ g)
    (hsign : (f 0 - deriv g 0) * (deriv g 1 - f 1) > 0) :
    ∃ c ∈ Ioo (0 : ℝ) 1, f c = deriv g c := by
  -- Let F x = ∫ t in 0..x, f t. Then F'(x) = f(x) by FTC since f is continuous.
  -- Let h x = F x - g x. Then h'(x) = f(x) - g'(x).
  -- The hypothesis is h'(0) * (-h'(1)) > 0, so h'(0) and h'(1) have opposite signs.
  -- Apply Darboux's theorem to get c ∈ (0,1) with h'(c) = 0.
  set F : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, f t with hF_def
  set h : ℝ → ℝ := fun x => F x - g x with hh_def
  -- d x = f x - deriv g x is the derivative of h at x.
  set d : ℝ → ℝ := fun x => f x - deriv g x with hd_def
  have hh_deriv : ∀ x, HasDerivAt h (d x) x := by
    intro x
    have hF : HasDerivAt F (f x) x :=
      (hf.integral_hasStrictDerivAt 0 x).hasDerivAt
    have hG : HasDerivAt g (deriv g x) x := (hg x).hasDerivAt
    exact hF.sub hG
  have hh_deriv_within : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt h (d x) (Icc 0 1) x := by
    intro x _
    exact (hh_deriv x).hasDerivWithinAt
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  -- The hypothesis says f(0) - g'(0) ≠ 0.
  have hd0_ne : d 0 ≠ 0 := by
    intro h0
    simp only [d] at h0
    rw [h0, zero_mul] at hsign
    exact lt_irrefl 0 hsign
  rcases lt_or_gt_of_ne hd0_ne with hneg | hpos
  · -- d 0 < 0, so from hsign the other factor must be negative too, hence d 1 > 0.
    have h1pos : 0 < d 1 := by
      show 0 < f 1 - deriv g 1
      have : deriv g 1 - f 1 < 0 := by
        by_contra h
        have h' : 0 ≤ deriv g 1 - f 1 := not_lt.mp h
        have : (f 0 - deriv g 0) * (deriv g 1 - f 1) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hneg.le h'
        linarith
      linarith
    -- d 0 < 0 < d 1. Apply Darboux: exists_hasDerivWithinAt_eq_of_gt_of_lt.
    obtain ⟨c, hc_mem, hc⟩ :=
      exists_hasDerivWithinAt_eq_of_gt_of_lt h01 hh_deriv_within (m := 0) hneg h1pos
    refine ⟨c, hc_mem, ?_⟩
    have : d c = 0 := hc
    simp only [d] at this
    linarith
  · -- d 0 > 0, so d 1 < 0.
    have h1neg : d 1 < 0 := by
      show f 1 - deriv g 1 < 0
      have : 0 < deriv g 1 - f 1 := by
        by_contra h
        have h' : deriv g 1 - f 1 ≤ 0 := not_lt.mp h
        have : (f 0 - deriv g 0) * (deriv g 1 - f 1) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hpos.le h'
        linarith
      linarith
    -- d 1 < 0 < d 0. Apply Darboux: exists_hasDerivWithinAt_eq_of_lt_of_gt.
    obtain ⟨c, hc_mem, hc⟩ :=
      exists_hasDerivWithinAt_eq_of_lt_of_gt h01 hh_deriv_within (m := 0) hpos h1neg
    refine ⟨c, hc_mem, ?_⟩
    have : d c = 0 := hc
    simp only [d] at this
    linarith

end Imc2019P6
