/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2017, Problem 2

Let `f : ℝ → (0, ∞)` be a differentiable function, and suppose that there exists
a constant `L > 0` such that `|f'(x) - f'(y)| ≤ L * |x - y|` for all `x, y`.
Prove that `(f'(x))^2 < 2 * L * f(x)` for all `x`.
-/

namespace Imc2017P2

open MeasureTheory intervalIntegral Set

snip begin

/-- The integral of `d - L*(x - y)` over `y ∈ [x - d/L, x]` equals `d^2 / (2 * L)`.
Proof by FTC: a primitive of `y ↦ d - L*(x - y)` is `y ↦ d*y + L*(x - y)^2 / (-2)`,
equivalently `F(y) = (d - L*x)*y + L*y^2/2`. -/
lemma integral_linear_eq {x d L : ℝ} (hL : 0 < L) :
    ∫ y in (x - d / L)..x, (d - L * (x - y)) = d ^ 2 / (2 * L) := by
  have hLne : L ≠ 0 := hL.ne'
  -- Primitive: F(y) = d*y + L*(y - x)^2/2 = d*y + L*(y^2 - 2*x*y + x^2)/2.
  -- F'(y) = d + L*(y - x) = d - L*(x - y).
  set F : ℝ → ℝ := fun y => d * y + L * (y - x) ^ 2 / 2 with hF_def
  have hF_deriv : ∀ y, HasDerivAt F (d - L * (x - y)) y := by
    intro y
    have h1 : HasDerivAt (fun y => d * y) d y := by
      simpa using (hasDerivAt_id y).const_mul d
    have h2 : HasDerivAt (fun y => (y - x) ^ 2) (2 * (y - x)) y := by
      have := ((hasDerivAt_id y).sub_const x).pow 2
      simpa using this
    have h3 : HasDerivAt (fun y => L * (y - x) ^ 2 / 2) (L * (y - x)) y := by
      have := (h2.const_mul L).div_const 2
      convert this using 1
      ring
    have h4 : HasDerivAt F (d + L * (y - x)) y := h1.add h3
    convert h4 using 1
    ring
  have hint : ∫ y in (x - d / L)..x, (d - L * (x - y)) = F x - F (x - d / L) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro y _; exact hF_deriv y
    · exact (Continuous.intervalIntegrable (by continuity) _ _)
  rw [hint]
  simp only [F]
  field_simp
  ring

snip end

problem imc2017_p2 (f : ℝ → ℝ) (hfpos : ∀ x, 0 < f x)
    (hfdiff : Differentiable ℝ f) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ x y, |deriv f x - deriv f y| ≤ L * |x - y|) :
    ∀ x, (deriv f x) ^ 2 < 2 * L * f x := by
  intro x
  set d : ℝ := deriv f x with hd_def
  -- f' is continuous (since Lipschitz).
  have hderiv_cont : Continuous (deriv f) := by
    rw [Metric.continuous_iff]
    intro a ε hε
    refine ⟨ε / L, div_pos hε hL, ?_⟩
    intro b hb
    rw [Real.dist_eq] at hb ⊢
    have := hLip b a
    calc |deriv f b - deriv f a| ≤ L * |b - a| := this
      _ < L * (ε / L) := by
          exact (mul_lt_mul_of_pos_left hb hL)
      _ = ε := by field_simp
  rcases lt_trichotomy d 0 with hneg | hzero | hpos
  · -- Case d < 0. Integrate on [x, x - d/L].
    set a : ℝ := x with ha_def
    set b : ℝ := x - d / L with hb_def
    have hab : a < b := by
      rw [ha_def, hb_def]
      have : -(d / L) > 0 := neg_pos.mpr (div_neg_of_neg_of_pos hneg hL)
      linarith
    have hab_le : a ≤ b := hab.le
    -- For y ∈ [a, b]: f'(y) ≤ d + L * (y - x)
    have hbound : ∀ y ∈ uIcc a b, deriv f y ≤ d + L * (y - x) := by
      intro y hy
      rw [uIcc_of_le hab_le] at hy
      have hay : a ≤ y := hy.1
      have hyb : y ≤ b := hy.2
      have hyx : x ≤ y := by rw [ha_def] at hay; exact hay
      have hLip_yx := hLip y x
      have habs : |y - x| = y - x := abs_of_nonneg (by linarith)
      rw [habs] at hLip_yx
      have h := abs_le.mp hLip_yx
      linarith [h.2, hd_def]
    have hftc : ∫ y in a..b, deriv f y = f b - f a := by
      apply integral_deriv_eq_sub
      · intro y _; exact hfdiff y
      · exact (hderiv_cont.continuousOn).intervalIntegrable
    have hcont_bound : Continuous (fun y => d + L * (y - x)) := by continuity
    have hineq : ∫ y in a..b, deriv f y ≤ ∫ y in a..b, (d + L * (y - x)) := by
      apply integral_mono_on hab_le
      · exact (hderiv_cont.continuousOn).intervalIntegrable
      · exact (hcont_bound.continuousOn).intervalIntegrable
      · intro y hy
        apply hbound
        rw [uIcc_of_le hab_le]
        exact hy
    -- Compute ∫_x^{x-d/L} (d + L*(y-x)) dy = -(d²/(2L)).
    have hcalc : ∫ y in a..b, (d + L * (y - x)) = -(d ^ 2 / (2 * L)) := by
      have heq : (fun y => d + L * (y - x)) = (fun y => d - L * (x - y)) := by
        funext y; ring
      rw [heq, ha_def, hb_def]
      have hrev := integral_linear_eq (x := x) (d := d) hL
      -- We want ∫_x^{x - d/L} while integral_linear_eq gives ∫_{x - d/L}^x.
      rw [show ∫ y in x..(x - d / L), (d - L * (x - y)) =
            -∫ y in (x - d / L)..x, (d - L * (x - y)) from
          intervalIntegral.integral_symm _ _]
      rw [hrev]
    rw [hcalc, hftc] at hineq
    have hfb_pos : 0 < f b := hfpos b
    have hfa_big : d ^ 2 / (2 * L) < f a := by
      have : f b ≤ f a - d ^ 2 / (2 * L) := by linarith
      linarith
    have h2L : 0 < 2 * L := by linarith
    rw [ha_def] at hfa_big
    rw [div_lt_iff₀ h2L] at hfa_big
    linarith
  · -- Case d = 0.
    rw [hzero]
    have := hfpos x
    have : (0 : ℝ) ^ 2 = 0 := by ring
    nlinarith [hfpos x, hL]
  · -- Case d > 0. Integrate on [x - d/L, x].
    set a : ℝ := x - d / L with ha_def
    set b : ℝ := x with hb_def
    have hab : a < b := by
      rw [ha_def, hb_def]
      have : d / L > 0 := div_pos hpos hL
      linarith
    have hab_le : a ≤ b := hab.le
    -- For y ∈ [a, b]: f'(y) ≥ d - L*(x - y)
    have hbound : ∀ y ∈ uIcc a b, d - L * (x - y) ≤ deriv f y := by
      intro y hy
      rw [uIcc_of_le hab_le] at hy
      have hay : a ≤ y := hy.1
      have hyb : y ≤ b := hy.2
      have hyx : y ≤ x := by rw [hb_def] at hyb; exact hyb
      have hLip_xy := hLip x y
      have habs : |x - y| = x - y := abs_of_nonneg (by linarith)
      rw [habs] at hLip_xy
      have h := abs_le.mp hLip_xy
      linarith [h.2, hd_def]
    have hftc : ∫ y in a..b, deriv f y = f b - f a := by
      apply integral_deriv_eq_sub
      · intro y _; exact hfdiff y
      · exact (hderiv_cont.continuousOn).intervalIntegrable
    have hcont_bound : Continuous (fun y => d - L * (x - y)) := by continuity
    have hineq : ∫ y in a..b, (d - L * (x - y)) ≤ ∫ y in a..b, deriv f y := by
      apply integral_mono_on hab_le
      · exact (hcont_bound.continuousOn).intervalIntegrable
      · exact (hderiv_cont.continuousOn).intervalIntegrable
      · intro y hy
        apply hbound
        rw [uIcc_of_le hab_le]
        exact hy
    have hcalc : ∫ y in a..b, (d - L * (x - y)) = d ^ 2 / (2 * L) := by
      rw [ha_def, hb_def]
      exact integral_linear_eq hL
    rw [hcalc, hftc] at hineq
    have hfa_pos : 0 < f a := hfpos a
    have hfb_big : d ^ 2 / (2 * L) < f b := by linarith
    rw [hb_def] at hfb_big
    have h2L : 0 < 2 * L := by linarith
    rw [div_lt_iff₀ h2L] at hfb_big
    linarith

end Imc2017P2
