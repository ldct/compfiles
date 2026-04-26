/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Inequality] }

/-!
# International Mathematical Competition 1995, Problem 2 (Day 1)

Let `f` be continuous on `[0,1]` with `∫_x^1 f(t) dt ≥ (1 - x^2)/2` for every
`x ∈ [0,1]`. Show `∫₀¹ f(t)^2 dt ≥ 1/3`.

## Proof outline

From `0 ≤ ∫₀¹ (f x - x)^2 dx` we obtain
`∫₀¹ f^2 ≥ 2 ∫₀¹ x f(x) dx − 1/3`.

We claim `∫₀¹ x f(x) dx ≥ 1/3`. Using integration by parts with
`G(x) = ∫_x^1 f(t) dt` (so `G'(x) = -f(x)` and `G(1) = 0`), we have
`∫₀¹ x f(x) dx = ∫₀¹ G(x) dx ≥ ∫₀¹ (1-x^2)/2 dx = 1/3`.
-/

namespace Imc1995P2

open MeasureTheory intervalIntegral Set Filter Topology

snip begin

/-- Continuity of `x ↦ ∫_x^1 f(t) dt` on `[0,1]`. -/
lemma continuousOn_G (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (0:ℝ) 1)) :
    ContinuousOn (fun x => ∫ t in x..(1:ℝ), f t) (Icc (0:ℝ) 1) := by
  have h01 : (uIcc (0:ℝ) 1) = Icc 0 1 := uIcc_of_le (by norm_num)
  have hint : IntegrableOn f (uIcc (0:ℝ) 1) volume := by
    rw [h01]; exact (hf.integrableOn_Icc)
  have := continuousOn_primitive_interval_left (a := (0:ℝ)) (b := 1)
    (f := f) (μ := volume) hint
  rw [h01] at this
  exact this

/-- Interval integrability of `x ↦ ∫_x^1 f(t) dt` on `[0,1]`. -/
lemma intervalIntegrable_G (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (0:ℝ) 1)) :
    IntervalIntegrable (fun x => ∫ t in x..(1:ℝ), f t) volume (0:ℝ) 1 :=
  (continuousOn_G f hf).intervalIntegrable_of_Icc (by norm_num)

/-- Integration by parts identity: if `f` is continuous on `[0,1]`, then
`∫₀¹ x f(x) dx = ∫₀¹ ∫_x^1 f(t) dt dx`.
Uses IBP with `u(x) = -∫_x^1 f` (so `u' = f`) and `v(x) = x` (so `v' = 1`). -/
lemma integral_x_mul_f_eq_integral_G
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (0:ℝ) 1)) :
    ∫ x in (0:ℝ)..1, x * f x
      = ∫ x in (0:ℝ)..1, ∫ t in x..(1:ℝ), f t := by
  set u : ℝ → ℝ := fun x => -∫ t in x..(1:ℝ), f t with hu_def
  set v : ℝ → ℝ := fun x => x with hv_def
  set u' : ℝ → ℝ := f with hu'_def
  set v' : ℝ → ℝ := fun _ => (1:ℝ) with hv'_def
  have h01 : (uIcc (0:ℝ) 1) = Icc 0 1 := uIcc_of_le (by norm_num)
  have hmin : min (0:ℝ) 1 = 0 := by norm_num
  have hmax : max (0:ℝ) 1 = 1 := by norm_num
  have hf_int : IntervalIntegrable f volume (0:ℝ) 1 :=
    hf.intervalIntegrable_of_Icc (by norm_num)
  -- Continuity of u on uIcc 0 1 = Icc 0 1.
  have hu_cont : ContinuousOn u (uIcc (0:ℝ) 1) := by
    rw [h01]; exact (continuousOn_G f hf).neg
  have hv_cont : ContinuousOn v (uIcc (0:ℝ) 1) := continuousOn_id
  -- u has right-derivative f x at every x ∈ Ioo 0 1 (interior).
  -- For interior points, ContinuousAt f x holds, so we can use the strong FTC.
  have huu' : ∀ x ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1),
      HasDerivWithinAt u (u' x) (Ioi x) x := by
    intro x hx
    rw [hmin, hmax] at hx
    -- x ∈ (0,1): f is continuous at x (since Icc 0 1 is a nbhd of x).
    have hIcc_nhds : Icc (0:ℝ) 1 ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
    have hfx : ContinuousAt f x :=
      ((hf x ⟨hx.1.le, hx.2.le⟩).continuousAt hIcc_nhds)
    -- f is integrable on x..1 (since [x,1] ⊆ [0,1]).
    have hf_x1 : IntervalIntegrable f volume x 1 :=
      hf_int.mono_set (by
        rw [uIcc_of_le hx.2.le, uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
        exact Icc_subset_Icc hx.1.le le_rfl)
    have hmeas : StronglyMeasurableAtFilter f (𝓝 x) volume := by
      apply ContinuousOn.stronglyMeasurableAtFilter (s := Ioo (0:ℝ) 1) isOpen_Ioo
        (hf.mono Ioo_subset_Icc_self) x hx
    have hG : HasDerivAt (fun y => ∫ t in y..(1:ℝ), f t) (-f x) x :=
      intervalIntegral.integral_hasDerivAt_left hf_x1 hmeas hfx
    have huat : HasDerivAt u (f x) x := by simpa [hu_def] using hG.neg
    exact huat.hasDerivWithinAt
  -- v has right-derivative 1 at interior points.
  have hvv' : ∀ x ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1),
      HasDerivWithinAt v (v' x) (Ioi x) x := by
    intro x _
    simpa [hv_def, hv'_def] using (hasDerivAt_id x).hasDerivWithinAt
  have hu'_int : IntervalIntegrable u' volume (0:ℝ) 1 := hf_int
  have hv'_int : IntervalIntegrable v' volume (0:ℝ) 1 :=
    intervalIntegral.intervalIntegrable_const
  have key := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right
    (a := (0:ℝ)) (b := 1) (u := u) (v := v) (u' := u') (v' := v')
    hu_cont hv_cont huu' hvv' hu'_int hv'_int
  have hu1 : u 1 = 0 := by simp [hu_def]
  have hv0 : v 0 = 0 := by simp [hv_def]
  have hrhs : u 1 * v 1 - u 0 * v 0 = 0 := by rw [hu1, hv0]; ring
  rw [hrhs] at key
  have heq : ∀ x, u' x * v x + u x * v' x = x * f x - ∫ t in x..(1:ℝ), f t := by
    intro x
    show f x * x + (-∫ t in x..(1:ℝ), f t) * 1 = x * f x - ∫ t in x..(1:ℝ), f t
    ring
  simp_rw [heq] at key
  have hxf_int : IntervalIntegrable (fun x => x * f x) volume (0:ℝ) 1 :=
    (continuous_id.continuousOn.mul hf).intervalIntegrable_of_Icc (by norm_num)
  have hG_int := intervalIntegrable_G f hf
  rw [intervalIntegral.integral_sub hxf_int hG_int] at key
  linarith

snip end

problem imc1995_p2
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (0:ℝ) 1))
    (h : ∀ x ∈ Icc (0:ℝ) 1, ∫ t in x..(1:ℝ), f t ≥ (1 - x^2) / 2) :
    ∫ t in (0:ℝ)..1, (f t)^2 ≥ 1/3 := by
  -- Step 1: From 0 ≤ ∫₀¹ (f x - x)² dx, expand to get
  -- ∫ f² ≥ 2 ∫ x f - 1/3.
  have hf_int : IntervalIntegrable f volume (0:ℝ) 1 :=
    hf.intervalIntegrable_of_Icc (by norm_num)
  have hf2_int : IntervalIntegrable (fun x => (f x)^2) volume (0:ℝ) 1 :=
    (hf.pow 2).intervalIntegrable_of_Icc (by norm_num)
  have hxf_int : IntervalIntegrable (fun x => x * f x) volume (0:ℝ) 1 :=
    (continuous_id.continuousOn.mul hf).intervalIntegrable_of_Icc (by norm_num)
  have hx2_int : IntervalIntegrable (fun x : ℝ => x^2) volume (0:ℝ) 1 :=
    ((continuous_id.pow 2).continuousOn).intervalIntegrable_of_Icc (by norm_num)
  have h_sq_nonneg : ∫ x in (0:ℝ)..1, (f x - x)^2 ≥ 0 := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x _
    exact sq_nonneg _
  have hexpand : ∀ x, (f x - x)^2 = (f x)^2 - 2 * (x * f x) + x^2 := by
    intro x; ring
  have h1 : ∫ x in (0:ℝ)..1, (f x - x)^2
      = (∫ x in (0:ℝ)..1, (f x)^2)
        - 2 * (∫ x in (0:ℝ)..1, x * f x)
        + ∫ x in (0:ℝ)..1, x^2 := by
    simp_rw [hexpand]
    rw [intervalIntegral.integral_add (hf2_int.sub (hxf_int.const_mul 2)) hx2_int,
        intervalIntegral.integral_sub hf2_int (hxf_int.const_mul 2),
        intervalIntegral.integral_const_mul]
  have hx2_val : ∫ x in (0:ℝ)..1, x^2 = 1/3 := by
    rw [integral_pow]; norm_num
  -- Step 2: Show ∫₀¹ x f(x) dx ≥ 1/3.
  have h_xf_ge : ∫ x in (0:ℝ)..1, x * f x ≥ 1/3 := by
    have hkey : ∫ x in (0:ℝ)..1, x * f x
        = ∫ x in (0:ℝ)..1, ∫ t in x..(1:ℝ), f t :=
      integral_x_mul_f_eq_integral_G f hf
    rw [hkey]
    have hbound : ∫ x in (0:ℝ)..1, ((1 - x^2) / 2) = 1/3 := by
      rw [intervalIntegral.integral_div]
      have hsub : ∫ x in (0:ℝ)..1, (1 - x^2)
            = (∫ _ in (0:ℝ)..1, (1:ℝ)) - ∫ x in (0:ℝ)..1, x^2 :=
        intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_const hx2_int
      rw [hsub, hx2_val]
      simp; norm_num
    rw [ge_iff_le, show (1:ℝ)/3 = ∫ x in (0:ℝ)..1, ((1 - x^2) / 2) from hbound.symm]
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((continuousOn_const.sub ((continuous_id.pow 2).continuousOn)).div_const _
        |>.intervalIntegrable_of_Icc (by norm_num))
      (intervalIntegrable_G f hf)
    intro x hx
    exact h x hx
  -- Step 3: Combine.
  have : 0 ≤ (∫ x in (0:ℝ)..1, (f x)^2) - 2 * (∫ x in (0:ℝ)..1, x * f x) + 1/3 := by
    rw [← hx2_val, ← h1]; exact h_sq_nonneg
  linarith

end Imc1995P2
