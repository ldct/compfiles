/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2010, Problem 1

Let `0 < a < b`. Prove that
  `∫_a^b (x^2 + 1) e^{-x^2} dx ≥ e^{-a^2} - e^{-b^2}`.
-/

namespace Imc2010P1

open intervalIntegral Set

snip begin

/-- The antiderivative of `2 x e^{-x^2}` is `-e^{-x^2}`. -/
lemma hasDerivAt_neg_exp_neg_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ => -Real.exp (-y^2)) (2 * x * Real.exp (-x^2)) x := by
  -- d/dx (-e^{-x^2}) = -e^{-x^2} * (-2x) = 2x * e^{-x^2}.
  have h1 : HasDerivAt (fun y : ℝ => -y^2) (-(2 * x)) x := by
    have : HasDerivAt (fun y : ℝ => y^2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x)
    exact this.neg
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y^2))
      (Real.exp (-x^2) * -(2 * x)) x :=
    HasDerivAt.exp h1
  have h3 : HasDerivAt (fun y : ℝ => -Real.exp (-y^2))
      (-(Real.exp (-x^2) * -(2 * x))) x := h2.neg
  convert h3 using 1
  ring

snip end

problem imc2010_p1 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Real.exp (-a^2) - Real.exp (-b^2) ≤
      ∫ x in a..b, (x^2 + 1) * Real.exp (-x^2) := by
  have hle : a ≤ b := hab.le
  -- Step 1: Compute ∫_a^b 2x e^{-x^2} dx = e^{-a^2} - e^{-b^2}.
  have hderiv : ∀ x ∈ uIcc a b,
      HasDerivAt (fun y : ℝ => -Real.exp (-y^2)) (2 * x * Real.exp (-x^2)) x :=
    fun x _ => hasDerivAt_neg_exp_neg_sq x
  have hcont : ContinuousOn (fun x : ℝ => 2 * x * Real.exp (-x^2)) (uIcc a b) :=
    (continuous_const.mul continuous_id).mul
      (Real.continuous_exp.comp (continuous_id.pow 2).neg) |>.continuousOn
  have hFTC : (∫ x in a..b, 2 * x * Real.exp (-x^2)) =
      (-Real.exp (-b^2)) - (-Real.exp (-a^2)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  -- Step 2: The bigger integrand dominates the smaller.
  -- x^2 + 1 - 2x = (x - 1)^2 ≥ 0, so x^2 + 1 ≥ 2x (for all real x).
  have hpoint : ∀ x ∈ Icc a b,
      2 * x * Real.exp (-x^2) ≤ (x^2 + 1) * Real.exp (-x^2) := by
    intro x _
    have hexp_pos : 0 < Real.exp (-x^2) := Real.exp_pos _
    have h_ineq : 2 * x ≤ x^2 + 1 := by nlinarith [sq_nonneg (x - 1)]
    exact mul_le_mul_of_nonneg_right h_ineq hexp_pos.le
  -- Step 3: Integral monotonicity.
  have hint_small : IntervalIntegrable (fun x : ℝ => 2 * x * Real.exp (-x^2))
      MeasureTheory.volume a b := hcont.intervalIntegrable
  have hcont_big : ContinuousOn (fun x : ℝ => (x^2 + 1) * Real.exp (-x^2)) (uIcc a b) :=
    ((continuous_id.pow 2).add continuous_const).mul
      (Real.continuous_exp.comp (continuous_id.pow 2).neg) |>.continuousOn
  have hint_big : IntervalIntegrable (fun x : ℝ => (x^2 + 1) * Real.exp (-x^2))
      MeasureTheory.volume a b := hcont_big.intervalIntegrable
  have hmono : (∫ x in a..b, 2 * x * Real.exp (-x^2)) ≤
      ∫ x in a..b, (x^2 + 1) * Real.exp (-x^2) :=
    intervalIntegral.integral_mono_on hle hint_small hint_big hpoint
  -- Combine.
  have : Real.exp (-a^2) - Real.exp (-b^2) = ∫ x in a..b, 2 * x * Real.exp (-x^2) := by
    rw [hFTC]; ring
  linarith

end Imc2010P1
