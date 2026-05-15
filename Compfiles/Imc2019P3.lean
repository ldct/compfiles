/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2019, Problem 3

Let `f : ℝ → ℝ` be twice differentiable with `2 * f'(x) + x * f''(x) ≥ 1`
for `x ∈ (-1, 1)`. Prove that `∫ x in -1..1, x * f x ≥ 1/3`.
-/

namespace Imc2019P3

open Set MeasureTheory intervalIntegral

problem imc2019_p3 (f f' f'' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hineq : ∀ x ∈ Ioo (-1 : ℝ) 1, 1 ≤ 2 * f' x + x * f'' x) :
    1/3 ≤ ∫ x in (-1 : ℝ)..1, x * f x := by
  -- Let g(x) = x * f(x) - x^2/2. Then g''(x) = 2 f'(x) + x f''(x) - 1 ≥ 0
  -- on (-1, 1), so g is convex on [-1, 1]. Applied at 0, g(x) ≥ g(0) + G(0) * x
  -- where G(0) = g'(0) = f(0). Integrating, since ∫ x dx = 0 on [-1,1],
  -- ∫ g ≥ 0, i.e., ∫ x f(x) dx ≥ ∫ x^2/2 dx = 1/3.
  set g : ℝ → ℝ := fun x => x * f x - x^2 / 2 with hg_def
  set G : ℝ → ℝ := fun x => f x + x * f' x - x with hG_def
  set G' : ℝ → ℝ := fun x => 2 * f' x + x * f'' x - 1 with hG'_def
  -- Continuity of f (from differentiability).
  have hf_cont : Continuous f := by
    have : Differentiable ℝ f := fun x => (hf x).differentiableAt
    exact this.continuous
  -- g'(x) = G x.
  have hg_deriv : ∀ x, HasDerivAt g (G x) x := by
    intro x
    have h1 : HasDerivAt (fun y => y * f y) (1 * f x + x * f' x) x :=
      (hasDerivAt_id x).mul (hf x)
    have h2 : HasDerivAt (fun y : ℝ => y^2 / 2) x x := by
      have hp : HasDerivAt (fun y : ℝ => y^2) (2 * x) x := by
        have := (hasDerivAt_id x).pow 2
        simpa using this
      have := hp.div_const 2
      convert this using 1
      ring
    have h3 : HasDerivAt (fun y => y * f y - y^2/2) ((1 * f x + x * f' x) - x) x :=
      h1.sub h2
    convert h3 using 1
    simp only [G]; ring
  -- G'(x) = G' x.
  have hG_deriv : ∀ x, HasDerivAt G (G' x) x := by
    intro x
    have h1 : HasDerivAt (fun y => y * f' y) (1 * f' x + x * f'' x) x :=
      (hasDerivAt_id x).mul (hf' x)
    have h2 : HasDerivAt (fun y => f y + y * f' y) (f' x + (1 * f' x + x * f'' x)) x :=
      (hf x).add h1
    have h3 : HasDerivAt (fun y => (f y + y * f' y) - y)
        ((f' x + (1 * f' x + x * f'' x)) - 1) x :=
      h2.sub (hasDerivAt_id x)
    convert h3 using 1
    simp [G']; ring
  -- G' ≥ 0 on (-1, 1).
  have hG'_nonneg : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 ≤ G' x := by
    intro x hx
    have := hineq x hx
    simp only [G']; linarith
  -- g is continuous everywhere.
  have hg_cont : Continuous g := by
    have : Differentiable ℝ g := fun x => (hg_deriv x).differentiableAt
    exact this.continuous
  -- g is convex on Icc (-1) 1.
  have h_interior : interior (Icc (-1 : ℝ) 1) = Ioo (-1 : ℝ) 1 := interior_Icc
  have hgc : ConvexOn ℝ (Icc (-1 : ℝ) 1) g := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _) hg_cont.continuousOn
      (f' := G) (f'' := G') ?_ ?_ ?_
    · intro x _
      exact (hg_deriv x).hasDerivWithinAt
    · intro x _
      exact (hG_deriv x).hasDerivWithinAt
    · intro x hx
      rw [h_interior] at hx
      exact hG'_nonneg x hx
  -- g(0) = 0.
  have hg0 : g 0 = 0 := by simp [g]
  -- For x in Icc (-1) 1: G 0 * x ≤ g x (tangent line at 0).
  have hg_lb : ∀ x ∈ Icc (-1 : ℝ) 1, G 0 * x ≤ g x := by
    intro x hx
    have h0_mem : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
    · -- x < 0: slope g x 0 ≤ G 0.
      have hs : slope g x 0 ≤ G 0 :=
        hgc.slope_le_of_hasDerivAt hx h0_mem hx_neg (hg_deriv 0)
      have hslope_eq : slope g x 0 = (g 0 - g x) / (0 - x) := by
        rw [slope_def_field]
      rw [hslope_eq, hg0] at hs
      have h0x_pos : (0 : ℝ) < 0 - x := by linarith
      have := (div_le_iff₀ h0x_pos).mp hs
      linarith
    · subst hx_zero; rw [hg0]; linarith
    · -- x > 0: G 0 ≤ slope g 0 x.
      have hs : G 0 ≤ slope g 0 x :=
        hgc.le_slope_of_hasDerivAt h0_mem hx hx_pos (hg_deriv 0)
      have hslope_eq : slope g 0 x = (g x - g 0) / (x - 0) := by
        rw [slope_def_field]
      rw [hslope_eq, hg0] at hs
      have hx_pos' : (0 : ℝ) < x - 0 := by linarith
      have := (le_div_iff₀ hx_pos').mp hs
      linarith
  -- Integrability pieces.
  have h_neg1_le_1 : (-1 : ℝ) ≤ 1 := by norm_num
  have hg_int : IntervalIntegrable g volume (-1) 1 :=
    hg_cont.intervalIntegrable _ _
  have hG0x_int : IntervalIntegrable (fun x => G 0 * x) volume (-1) 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hxf_cont : Continuous (fun x : ℝ => x * f x) := continuous_id.mul hf_cont
  have hxf_int : IntervalIntegrable (fun x : ℝ => x * f x) volume (-1) 1 :=
    hxf_cont.intervalIntegrable _ _
  have hx2_int : IntervalIntegrable (fun x : ℝ => x^2 / 2) volume (-1) 1 :=
    (continuous_pow 2 |>.div_const 2).intervalIntegrable _ _
  -- Inequality on integrals: ∫ G 0 * x ≤ ∫ g.
  have h_mono : ∫ x in (-1 : ℝ)..1, G 0 * x ≤ ∫ x in (-1 : ℝ)..1, g x := by
    apply intervalIntegral.integral_mono_on h_neg1_le_1 hG0x_int hg_int
    intro x hx; exact hg_lb x hx
  -- ∫ G 0 * x = 0 on [-1, 1].
  have hG0_int_zero : ∫ x in (-1 : ℝ)..1, G 0 * x = 0 := by
    rw [intervalIntegral.integral_const_mul]
    have hx_int : ∫ x in (-1 : ℝ)..1, x = 0 := by
      rw [integral_id]; norm_num
    rw [hx_int]; ring
  -- ∫ g = ∫ x f(x) - ∫ x²/2.
  have hg_decomp : ∫ x in (-1 : ℝ)..1, g x =
      (∫ x in (-1 : ℝ)..1, x * f x) - (∫ x in (-1 : ℝ)..1, x^2 / 2) := by
    simp only [g]
    exact intervalIntegral.integral_sub hxf_int hx2_int
  -- ∫ x²/2 from -1 to 1 = 1/3.
  have hx2_val : ∫ x in (-1 : ℝ)..1, x^2 / 2 = 1/3 := by
    have h1 : ∫ x in (-1 : ℝ)..1, x^2 / 2 = (1/2) * ∫ x in (-1 : ℝ)..1, x^2 := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      ext x; ring
    rw [h1]
    have h2 : ∫ x in (-1 : ℝ)..1, x^2 = 2/3 := by
      rw [integral_pow]
      norm_num
    rw [h2]; ring
  -- Combine.
  linarith [h_mono, hG0_int_zero, hg_decomp, hx2_val]

end Imc2019P3
