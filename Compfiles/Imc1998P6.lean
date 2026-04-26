/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1998, Problem 6 (Day 1)

Let `f : [0, 1] → ℝ` be continuous, and assume that
`x · f y + y · f x ≤ 1` for all `x, y ∈ [0, 1]`.

(a) Show that `∫_0^1 f ≤ π/4`.

(b) Give a function with equality.

## Solution sketch

Substitute `x = sin θ` (and separately `x = cos θ`):

  `∫_0^1 f(x) dx = ∫_0^{π/2} f(sin θ) · cos θ dθ`,
  `∫_0^1 f(x) dx = ∫_0^{π/2} f(cos θ) · sin θ dθ`.

Adding the two expressions:

  `2 ∫_0^1 f = ∫_0^{π/2} (f(sin θ) cos θ + f(cos θ) sin θ) dθ
            ≤ ∫_0^{π/2} 1 dθ = π/2`.

Equality is achieved by `f(x) = √(1 - x²)`, since then
`x f(y) + y f(x) = sin(θ + φ)` with `x = sin θ`, `y = sin φ`, which is `≤ 1`,
and `∫_0^1 √(1 - x²) dx = π/4`.
-/

namespace Imc1998P6

open MeasureTheory intervalIntegral Set Real

snip begin

/-- The substitution `x = sin θ`: `∫_0^1 g(x) dx = ∫_0^{π/2} g(sin θ) cos θ dθ`. -/
lemma integral_sin_substitution (g : ℝ → ℝ) (hg : Continuous g) :
    ∫ x in (0:ℝ)..1, g x = ∫ θ in (0:ℝ)..(π/2), g (sin θ) * cos θ := by
  -- integral_comp_mul_deriv : ∫_a^b (g ∘ f) x * f' x = ∫_{f a}^{f b} g x.
  have hcomp : (∫ θ in (0:ℝ)..(π/2), (g ∘ Real.sin) θ * Real.cos θ) =
      ∫ x in Real.sin 0..Real.sin (π/2), g x :=
    intervalIntegral.integral_comp_mul_deriv
      (a := (0 : ℝ)) (b := π/2)
      (f := Real.sin) (f' := Real.cos) (g := g)
      (fun x _ => Real.hasDerivAt_sin x)
      Real.continuousOn_cos
      hg
  rw [Real.sin_zero, Real.sin_pi_div_two] at hcomp
  rw [← hcomp]
  rfl

/-- The substitution `x = cos θ`: `∫_0^1 g(x) dx = ∫_0^{π/2} g(cos θ) sin θ dθ`. -/
lemma integral_cos_substitution (g : ℝ → ℝ) (hg : Continuous g) :
    ∫ x in (0:ℝ)..1, g x = ∫ θ in (0:ℝ)..(π/2), g (cos θ) * sin θ := by
  -- We use the change of variables u = cos θ on [0, π/2].
  -- integral_comp_mul_deriv : ∫_a^b (g ∘ f) x * f' x dx = ∫_{f a}^{f b} g x dx.
  -- With f = cos, f' = -sin, a = π/2, b = 0:
  -- ∫_{π/2}^0 g(cos θ) * (-sin θ) dθ = ∫_{cos(π/2)}^{cos 0} g x dx = ∫_0^1 g x dx.
  have hcomp : (∫ θ in (π/2 : ℝ)..0, (g ∘ Real.cos) θ * (-Real.sin θ)) =
      ∫ x in Real.cos (π/2)..Real.cos 0, g x :=
    intervalIntegral.integral_comp_mul_deriv
      (a := π/2) (b := 0)
      (f := Real.cos) (f' := fun θ => -Real.sin θ) (g := g)
      (fun x _ => Real.hasDerivAt_cos x)
      Real.continuousOn_sin.neg
      hg
  rw [Real.cos_zero, Real.cos_pi_div_two] at hcomp
  -- hcomp : ∫_{π/2}^0 g(cos θ) * (-sin θ) dθ = ∫_0^1 g x dx
  rw [← hcomp]
  -- Goal: ∫_{π/2}^0 (g ∘ cos) θ * (-sin θ) dθ = ∫_0^{π/2} g(cos θ) * sin θ dθ
  rw [show (fun θ => (g ∘ Real.cos) θ * (-Real.sin θ)) =
        (fun θ => -(g (Real.cos θ) * Real.sin θ)) from by funext θ; simp [Function.comp, mul_neg]]
  rw [intervalIntegral.integral_neg]
  rw [intervalIntegral.integral_symm]
  ring

snip end

/-- Part (a): if `f : [0,1] → ℝ` extends to a continuous function on `ℝ`
satisfying `x f y + y f x ≤ 1` for all `x, y ∈ [0, 1]`, then
`∫_0^1 f ≤ π/4`. -/
problem imc1998_p6a
    (f : ℝ → ℝ) (hf : Continuous f)
    (hbound : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      x * f y + y * f x ≤ 1) :
    ∫ x in (0:ℝ)..1, f x ≤ π / 4 := by
  -- Two expressions for the integral.
  have hI_sin : ∫ x in (0:ℝ)..1, f x =
      ∫ θ in (0:ℝ)..(π/2), f (sin θ) * cos θ :=
    integral_sin_substitution f hf
  have hI_cos : ∫ x in (0:ℝ)..1, f x =
      ∫ θ in (0:ℝ)..(π/2), f (cos θ) * sin θ :=
    integral_cos_substitution f hf
  -- Sum them.
  have hpi_pos : (0 : ℝ) < π / 2 := by positivity
  have hpi_le : (0 : ℝ) ≤ π / 2 := hpi_pos.le
  have hsum : 2 * ∫ x in (0:ℝ)..1, f x =
      ∫ θ in (0:ℝ)..(π/2), (f (sin θ) * cos θ + f (cos θ) * sin θ) := by
    rw [two_mul]
    nth_rewrite 1 [hI_sin]
    nth_rewrite 1 [hI_cos]
    rw [← intervalIntegral.integral_add]
    · exact ((hf.comp continuous_sin).mul continuous_cos).intervalIntegrable _ _
    · exact ((hf.comp continuous_cos).mul continuous_sin).intervalIntegrable _ _
  -- Bound the integrand by 1 a.e. on [0, π/2].
  have hbound_pt : ∀ θ ∈ Set.Icc (0 : ℝ) (π/2),
      f (sin θ) * cos θ + f (cos θ) * sin θ ≤ 1 := by
    intro θ hθ
    have hsin_mem : Real.sin θ ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨Real.sin_nonneg_of_mem_Icc ⟨hθ.1, le_trans hθ.2 (by linarith [Real.pi_pos])⟩,
       Real.sin_le_one _⟩
    have hcos_mem : Real.cos θ ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], hθ.2⟩,
       Real.cos_le_one _⟩
    have h := hbound (Real.sin θ) hsin_mem (Real.cos θ) hcos_mem
    -- h : sin θ * f (cos θ) + cos θ * f (sin θ) ≤ 1
    -- Goal: f (sin θ) * cos θ + f (cos θ) * sin θ ≤ 1
    linarith
  -- Use this to bound the integral.
  have hint_le : ∫ θ in (0:ℝ)..(π/2), (f (sin θ) * cos θ + f (cos θ) * sin θ)
      ≤ ∫ θ in (0:ℝ)..(π/2), (1 : ℝ) := by
    apply intervalIntegral.integral_mono_on hpi_le
    · exact (((hf.comp continuous_sin).mul continuous_cos).add
        ((hf.comp continuous_cos).mul continuous_sin)).intervalIntegrable _ _
    · exact continuous_const.intervalIntegrable _ _
    · intro θ hθ
      exact hbound_pt θ hθ
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at hint_le
  -- 2 * ∫_0^1 f ≤ π/2, so ∫_0^1 f ≤ π/4.
  linarith

/-- Part (b): the function `f(x) = √(1 - x²)` satisfies the hypothesis and
achieves equality `∫_0^1 f = π/4`. -/
problem imc1998_p6b :
    ∃ f : ℝ → ℝ,
      Continuous f ∧
      (∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1, x * f y + y * f x ≤ 1) ∧
      ∫ x in (0:ℝ)..1, f x = π / 4 := by
  refine ⟨fun x => Real.sqrt (1 - x^2), ?_, ?_, ?_⟩
  · -- Continuity.
    exact Real.continuous_sqrt.comp (by fun_prop)
  · -- Bound: x √(1 - y²) + y √(1 - x²) ≤ 1 for x, y ∈ [0, 1].
    intro x hx y hy
    -- Strategy: prove (x √(1-y²) + y √(1-x²))² ≤ 1, using nonnegativity.
    have hx0 : 0 ≤ x := hx.1
    have hx1 : x ≤ 1 := hx.2
    have hy0 : 0 ≤ y := hy.1
    have hy1 : y ≤ 1 := hy.2
    have hxsq_le : x^2 ≤ 1 := by nlinarith
    have hysq_le : y^2 ≤ 1 := by nlinarith
    have hx2nn : (0 : ℝ) ≤ 1 - x^2 := by linarith
    have hy2nn : (0 : ℝ) ≤ 1 - y^2 := by linarith
    have hsx : Real.sqrt (1 - x^2) ≥ 0 := Real.sqrt_nonneg _
    have hsy : Real.sqrt (1 - y^2) ≥ 0 := Real.sqrt_nonneg _
    have hsx_sq : Real.sqrt (1 - x^2) ^ 2 = 1 - x^2 := Real.sq_sqrt hx2nn
    have hsy_sq : Real.sqrt (1 - y^2) ^ 2 = 1 - y^2 := Real.sq_sqrt hy2nn
    -- Want: x · √(1 - y²) + y · √(1 - x²) ≤ 1
    -- Square both sides (both nonneg). Suffices: (x √(1-y²) + y √(1-x²))² ≤ 1.
    have hLHSnn : 0 ≤ x * Real.sqrt (1 - y^2) + y * Real.sqrt (1 - x^2) :=
      add_nonneg (mul_nonneg hx0 hsy) (mul_nonneg hy0 hsx)
    -- (x √(1-y²) + y √(1-x²))² = x²(1-y²) + 2xy √((1-x²)(1-y²)) + y²(1-x²)
    --   = x² + y² - 2 x² y² + 2xy √((1-x²)(1-y²))
    -- ≤ 1 iff 2xy √((1-x²)(1-y²)) ≤ 1 - x² - y² + 2 x² y² = (1-x²)(1-y²) + x²y²... wait
    -- Actually 1 - x² - y² + 2 x² y² = (1-x²)(1-y²) + x²y² is not quite right.
    -- Let A = 1 - x², B = 1 - y². Then x² = 1 - A, y² = 1 - B,
    -- 1 - x² - y² + 2x²y² = 1 - (1-A) - (1-B) + 2(1-A)(1-B) = -1 + A + B + 2 - 2A - 2B + 2AB
    --   = 1 - A - B + 2AB. Hmm, AM-GM: 2xy√(AB) ≤ x²B + y²A = (1-A)B + (1-B)A = A + B - 2AB.
    -- So 2xy √(AB) ≤ A + B - 2AB, giving sum ≤ x² + y² - 2x²y² + A + B - 2AB
    --   = x² + y² - 2x²y² + (1-x²) + (1-y²) - 2(1-x²)(1-y²)
    --   = 2 - 2x²y² - 2(1 - x² - y² + x²y²) = 2 - 2x²y² - 2 + 2x² + 2y² - 2x²y²
    --   = 2x² + 2y² - 4x²y². That's not 1. Let me redo.
    -- Actually we want (x√B + y√A)² ≤ 1. Expand:
    --   x²B + y²A + 2xy√(AB) = x²(1-y²) + y²(1-x²) + 2xy√((1-x²)(1-y²))
    --   = x² + y² - 2x²y² + 2xy√((1-x²)(1-y²))
    -- AM-GM: 2xy√((1-x²)(1-y²)) ≤ x²(1-y²) + y²(1-x²) = x² + y² - 2x²y².
    -- Wait, AM-GM gives 2 ab ≤ a² + b² with a = x√(1-y²), b = y√(1-x²):
    --   2 · x · y · √((1-x²)(1-y²)) ≤ x²(1-y²) + y²(1-x²) = x² + y² - 2x²y².
    -- So total ≤ 2(x² + y² - 2x²y²) = 2x² + 2y² - 4x²y².
    -- We want this ≤ 1. Hmm, that's not always true (e.g., x = y = 1/√2 gives 2 - 1 = 1, ok;
    -- x = y = 0: 0 ≤ 1; x = 1, y = 0: 2 ≤ 1 fails!). So that bound is too weak.
    -- Actually x = 1, y = 0: original sum = 1·√1 + 0·0 = 1, so equals 1. Good.
    -- The square is 1, so we need a tighter bound for the square: ≤ 1.
    -- The slick approach: with x = sin α, y = sin β, expression = sin α cos β + sin β cos α = sin(α + β) ≤ 1.
    -- We do that via arcsin.
    -- Let α = arcsin x, β = arcsin y; then x = sin α, √(1-x²) = cos α, similarly for y.
    set α := Real.arcsin x with hα
    set β := Real.arcsin y with hβ
    have hα_range : α ∈ Set.Icc 0 (π/2) := by
      refine ⟨?_, ?_⟩
      · rw [hα]; exact Real.arcsin_nonneg.mpr hx0
      · rw [hα]
        have h1 : Real.arcsin x ≤ Real.arcsin 1 := Real.arcsin_le_arcsin hx1
        rw [Real.arcsin_one] at h1
        exact h1
    have hβ_range : β ∈ Set.Icc 0 (π/2) := by
      refine ⟨?_, ?_⟩
      · rw [hβ]; exact Real.arcsin_nonneg.mpr hy0
      · rw [hβ]
        have h1 : Real.arcsin y ≤ Real.arcsin 1 := Real.arcsin_le_arcsin hy1
        rw [Real.arcsin_one] at h1
        exact h1
    have hsin_α : Real.sin α = x := by
      rw [hα]
      apply Real.sin_arcsin
      · linarith
      · exact hx1
    have hsin_β : Real.sin β = y := by
      rw [hβ]
      apply Real.sin_arcsin
      · linarith
      · exact hy1
    have hcos_α : Real.cos α = Real.sqrt (1 - x^2) := by
      rw [← hsin_α]
      have hα_lower : -(π/2) ≤ α := by linarith [hα_range.1, Real.pi_pos]
      have hα_upper : α ≤ π/2 := hα_range.2
      rw [Real.cos_eq_sqrt_one_sub_sin_sq hα_lower hα_upper]
    have hcos_β : Real.cos β = Real.sqrt (1 - y^2) := by
      rw [← hsin_β]
      have hβ_lower : -(π/2) ≤ β := by linarith [hβ_range.1, Real.pi_pos]
      have hβ_upper : β ≤ π/2 := hβ_range.2
      rw [Real.cos_eq_sqrt_one_sub_sin_sq hβ_lower hβ_upper]
    -- Now: x · √(1-y²) + y · √(1-x²) = sin α cos β + sin β cos α = sin(α+β) ≤ 1.
    show x * Real.sqrt (1 - y^2) + y * Real.sqrt (1 - x^2) ≤ 1
    rw [← hcos_α, ← hcos_β, ← hsin_α, ← hsin_β]
    rw [show Real.sin α * Real.cos β + Real.sin β * Real.cos α = Real.sin (α + β) from
        by rw [Real.sin_add]; ring]
    exact Real.sin_le_one _
  · -- ∫_0^1 √(1 - x²) = π/4.
    -- We use that ∫_{-1}^1 √(1-x²) = π/2 and the integrand is even, so ∫_0^1 = π/4.
    have hcont : Continuous (fun x : ℝ => Real.sqrt (1 - x^2)) :=
      Real.continuous_sqrt.comp (by fun_prop)
    have heven : ∀ x : ℝ, Real.sqrt (1 - (-x)^2) = Real.sqrt (1 - x^2) := by
      intro x; congr 1; ring
    have hsplit : ∫ x in (-1 : ℝ)..1, Real.sqrt (1 - x^2) =
        (∫ x in (-1 : ℝ)..0, Real.sqrt (1 - x^2)) +
        ∫ x in (0:ℝ)..1, Real.sqrt (1 - x^2) := by
      rw [intervalIntegral.integral_add_adjacent_intervals]
      · exact hcont.intervalIntegrable _ _
      · exact hcont.intervalIntegrable _ _
    -- ∫_{-1}^0 √(1 - x²) = ∫_0^1 √(1 - x²) by substitution u = -x.
    have hflip : ∫ x in (-1:ℝ)..0, Real.sqrt (1 - x^2) =
        ∫ x in (0:ℝ)..1, Real.sqrt (1 - x^2) := by
      have hsub := intervalIntegral.integral_comp_neg
        (f := fun x : ℝ => Real.sqrt (1 - x^2)) (a := 0) (b := 1)
      -- integral_comp_neg : ∫_a^b f(-x) dx = ∫_{-b}^{-a} f(x) dx
      simp only [neg_zero] at hsub
      rw [show (fun x : ℝ => Real.sqrt (1 - (-x)^2)) =
          (fun x : ℝ => Real.sqrt (1 - x^2)) by funext x; ring_nf] at hsub
      linarith
    rw [hflip] at hsplit
    rw [_root_.integral_sqrt_one_sub_sq] at hsplit
    linarith

end Imc1998P6
