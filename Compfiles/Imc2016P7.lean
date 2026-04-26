/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2016, Problem 7

Today, Ivan the Confessor prefers continuous functions `f : [0, 1] → ℝ`
satisfying `f x + f y ≥ |x - y|` for all `x, y ∈ [0, 1]`.
Find the minimum of `∫_0^1 f` over all preferred functions.

Answer: `1/4`.
-/

namespace Imc2016P7

open Set MeasureTheory intervalIntegral

/-- The set of integrals achieved by "preferred" functions. -/
noncomputable def preferredIntegrals : Set ℝ :=
  { v | ∃ f : ℝ → ℝ,
      ContinuousOn f (Icc (0:ℝ) 1) ∧
      (∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, |x - y| ≤ f x + f y) ∧
      ∫ x in (0:ℝ)..1, f x = v }

noncomputable determine answer : ℝ := 1/4

snip begin

/-- The witness function: `f₀ x = |x - 1/2|`. -/
noncomputable def f0 : ℝ → ℝ := fun x => |x - 1/2|

lemma f0_continuous : Continuous f0 := by
  unfold f0
  exact (continuous_id.sub continuous_const).abs

lemma f0_bound (x y : ℝ) : |x - y| ≤ f0 x + f0 y := by
  unfold f0
  have : x - y = (x - 1/2) - (y - 1/2) := by ring
  rw [this]
  exact abs_sub _ _

/-- `∫_0^1 |x - 1/2| dx = 1/4`. -/
lemma integral_f0 : ∫ x in (0:ℝ)..1, f0 x = 1/4 := by
  have hsplit : ∫ x in (0:ℝ)..1, f0 x =
      (∫ x in (0:ℝ)..(1/2), f0 x) + ∫ x in (1/2:ℝ)..1, f0 x := by
    rw [intervalIntegral.integral_add_adjacent_intervals
          (a := (0:ℝ)) (b := (1/2:ℝ)) (c := (1:ℝ))]
    · exact f0_continuous.intervalIntegrable _ _
    · exact f0_continuous.intervalIntegrable _ _
  -- On [0, 1/2], f0 x = 1/2 - x.
  have h1 : ∫ x in (0:ℝ)..(1/2), f0 x = ∫ x in (0:ℝ)..(1/2), (1/2 - x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2)] at hx
    unfold f0
    rw [abs_of_nonpos (by linarith [hx.2] : x - 1/2 ≤ 0)]
    ring
  -- On [1/2, 1], f0 x = x - 1/2.
  have h2 : ∫ x in (1/2:ℝ)..1, f0 x = ∫ x in (1/2:ℝ)..1, (x - 1/2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1)] at hx
    unfold f0
    rw [abs_of_nonneg (by linarith [hx.1] : 0 ≤ x - 1/2)]
  -- Compute via FTC. Primitive of (1/2 - x) is x/2 - x^2/2. Primitive of (x - 1/2) is x^2/2 - x/2.
  have hint1 : ∫ x in (0:ℝ)..(1/2), (1/2 - x) = 1/8 := by
    have hF : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y/2 - y^2/2) (1/2 - x) x := by
      intro x
      have h1 : HasDerivAt (fun y : ℝ => y/2) (1/2) x := by
        simpa using (hasDerivAt_id x).div_const 2
      have h2 : HasDerivAt (fun y : ℝ => y^2/2) x x := by
        have h2a : HasDerivAt (fun y : ℝ => y^2) (2 * x) x := by
          have := (hasDerivAt_id x).pow 2
          simpa using this
        have := h2a.div_const 2
        convert this using 1
        ring
      have h3 := h1.sub h2
      convert h3 using 1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF x)
        ((continuous_const.sub continuous_id).intervalIntegrable _ _)]
    norm_num
  have hint2 : ∫ x in (1/2:ℝ)..1, (x - 1/2) = 1/8 := by
    have hF : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y^2/2 - y/2) (x - 1/2) x := by
      intro x
      have h1 : HasDerivAt (fun y : ℝ => y/2) (1/2) x := by
        simpa using (hasDerivAt_id x).div_const 2
      have h2 : HasDerivAt (fun y : ℝ => y^2/2) x x := by
        have h2a : HasDerivAt (fun y : ℝ => y^2) (2 * x) x := by
          have := (hasDerivAt_id x).pow 2
          simpa using this
        have := h2a.div_const 2
        convert this using 1
        ring
      have h3 := h2.sub h1
      convert h3 using 1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF x)
        ((continuous_id.sub continuous_const).intervalIntegrable _ _)]
    norm_num
  rw [hsplit, h1, h2, hint1, hint2]
  norm_num

snip end

problem imc2016_p7 : IsLeast preferredIntegrals answer := by
  refine ⟨?_, ?_⟩
  · -- f0 attains 1/4.
    refine ⟨f0, f0_continuous.continuousOn, ?_, integral_f0⟩
    intro x _ y _
    exact f0_bound x y
  · -- Every preferred integral is ≥ 1/4.
    rintro v ⟨f, hcont, hbound, hv⟩
    -- Show ∫_0^1 f = ∫_0^{1/2} (f x + f(x + 1/2)) dx ≥ ∫_0^{1/2} (1/2) = 1/4.
    have h_f_int : IntervalIntegrable f MeasureTheory.volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact hcont
    have h_f_int_left : IntervalIntegrable f MeasureTheory.volume 0 (1/2) := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2)]
      exact hcont.mono (Icc_subset_Icc le_rfl (by norm_num))
    have h_f_int_right : IntervalIntegrable f MeasureTheory.volume (1/2) 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1)]
      exact hcont.mono (Icc_subset_Icc (by norm_num) le_rfl)
    -- Substitute in the right integral.
    -- The function g(x) = f(x + 1/2) is continuous on [0, 1/2].
    have hg_cont : ContinuousOn (fun x => f (x + 1/2)) (Icc (0:ℝ) (1/2)) := by
      have hshift : ContinuousOn (fun x : ℝ => x + 1/2) (Icc (0:ℝ) (1/2)) :=
        (continuous_id.add continuous_const).continuousOn
      have hmaps : MapsTo (fun x : ℝ => x + 1/2) (Icc (0:ℝ) (1/2)) (Icc (0:ℝ) 1) := by
        intro x hx
        constructor
        · linarith [hx.1]
        · linarith [hx.2]
      exact hcont.comp hshift hmaps
    have h_g_int : IntervalIntegrable (fun x => f (x + 1/2)) MeasureTheory.volume 0 (1/2) := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2)]
      exact hg_cont
    -- Change of variables: ∫_0^{1/2} f(x + 1/2) dx = ∫_{1/2}^1 f(u) du.
    have hcov : ∫ x in (0:ℝ)..(1/2), f (x + 1/2) = ∫ x in (1/2:ℝ)..1, f x := by
      have h := intervalIntegral.integral_comp_add_right
        (f := f) (a := (0:ℝ)) (b := (1/2:ℝ)) (1/2:ℝ)
      simp only [zero_add] at h
      rw [h]
      norm_num
    -- Sum: ∫_0^1 f = ∫_0^{1/2} f + ∫_{1/2}^1 f = ∫_0^{1/2} (f x + f(x+1/2)) dx.
    have hsum : ∫ x in (0:ℝ)..1, f x =
        ∫ x in (0:ℝ)..(1/2), (f x + f (x + 1/2)) := by
      rw [intervalIntegral.integral_add h_f_int_left h_g_int, hcov,
          intervalIntegral.integral_add_adjacent_intervals h_f_int_left h_f_int_right]
    -- Bound: f x + f(x + 1/2) ≥ 1/2 on [0, 1/2].
    have hge : ∀ x ∈ uIcc (0:ℝ) (1/2), (1/2 : ℝ) ≤ f x + f (x + 1/2) := by
      intro x hx
      rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2)] at hx
      have hx_mem : x ∈ Icc (0:ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
      have hxp_mem : x + 1/2 ∈ Icc (0:ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have := hbound x hx_mem (x + 1/2) hxp_mem
      have habs : |x - (x + 1/2)| = 1/2 := by
        rw [show x - (x + 1/2) = -(1/2) from by ring]
        rw [abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
      linarith
    have hineq : ∫ x in (0:ℝ)..(1/2), (1/2 : ℝ) ≤
                 ∫ x in (0:ℝ)..(1/2), (f x + f (x + 1/2)) := by
      apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1/2)
      · exact intervalIntegral.intervalIntegrable_const
      · exact h_f_int_left.add h_g_int
      · intro x hx
        apply hge
        rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2)]
        exact hx
    have hconst : ∫ _ in (0:ℝ)..(1/2), (1/2 : ℝ) = 1/4 := by
      simp
      norm_num
    rw [hconst] at hineq
    rw [← hv, hsum]
    exact hineq

end Imc2016P7
