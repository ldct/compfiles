/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2017, Problem 6

Let `f : [0, +∞) → ℝ` be a continuous function such that `lim_{x → +∞} f(x) = L`
exists (it may be finite or infinite). Prove that
  `lim_{n → ∞} ∫_0^1 f(nx) dx = L`.

We formalize the finite-limit case: assuming `f` is continuous on `ℝ` and
`Tendsto f atTop (𝓝 L)`, we prove `Tendsto (fun n => ∫ x in (0:ℝ)..1, f (n * x)) atTop (𝓝 L)`.
-/

namespace Imc2017P6

open Filter Topology MeasureTheory

snip begin

/-- Key reduction: for `n > 0`, `∫_0^1 f(nx) dx = (1/n) ∫_0^n f`. -/
lemma integral_comp_mul_eq (f : ℝ → ℝ) {n : ℝ} (hn : n ≠ 0) :
    ∫ x in (0:ℝ)..1, f (n * x) = n⁻¹ • ∫ x in (0:ℝ)..n, f x := by
  have := intervalIntegral.integral_comp_mul_left f hn (a := 0) (b := 1)
  simpa using this

/-- The "Cesaro-type" lemma for continuous functions:
if `f : ℝ → ℝ` is continuous and `Tendsto f atTop (𝓝 L)`, then
`Tendsto (fun t => (1/t) * ∫ x in 0..t, f x) atTop (𝓝 L)`. -/
lemma tendsto_average_of_tendsto {f : ℝ → ℝ} (hf : Continuous f) {L : ℝ}
    (hL : Tendsto f atTop (𝓝 L)) :
    Tendsto (fun t : ℝ => t⁻¹ * ∫ x in (0:ℝ)..t, f x) atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Choose K₁ such that for x ≥ K₁, |f x - L| < ε / 2.
  have hε2 : 0 < ε / 2 := by linarith
  rw [Metric.tendsto_atTop] at hL
  obtain ⟨K₁, hK₁⟩ := hL (ε / 2) hε2
  set K : ℝ := max K₁ 0 with hK_def
  have hK_nonneg : 0 ≤ K := le_max_right _ _
  have hK_geK1 : K₁ ≤ K := le_max_left _ _
  -- For x ≥ K, |f x - L| < ε/2.
  have hbound : ∀ x : ℝ, K ≤ x → |f x - L| < ε / 2 := by
    intro x hx
    have : K₁ ≤ x := le_trans hK_geK1 hx
    have := hK₁ x this
    rwa [Real.dist_eq] at this
  -- Continuous on [0, K], hence integrable. Let M = ∫_0^K |f x - L| dx.
  have hint_K : IntervalIntegrable (fun x => |f x - L|) volume 0 K :=
    (hf.sub continuous_const).abs.intervalIntegrable 0 K
  set M : ℝ := ∫ x in (0:ℝ)..K, |f x - L| with hM_def
  have hM_nonneg : 0 ≤ M := by
    rw [hM_def]
    exact intervalIntegral.integral_nonneg hK_nonneg (fun x _ => abs_nonneg _)
  -- Choose N large enough: N > K and N > 2 M / ε.
  set N : ℝ := max (K + 1) (2 * M / ε + 1) with hN_def
  have hN_gtK : K < N := by
    have : K < K + 1 := by linarith
    exact lt_of_lt_of_le this (le_max_left _ _)
  have hN_pos : 0 < N := lt_of_le_of_lt hK_nonneg hN_gtK
  have hN_gt_twoMoverε : 2 * M / ε < N := by
    have : 2 * M / ε < 2 * M / ε + 1 := by linarith
    exact lt_of_lt_of_le this (le_max_right _ _)
  refine ⟨N, ?_⟩
  intro t htN
  have ht_pos : 0 < t := lt_of_lt_of_le hN_pos htN
  have ht_gtK : K < t := lt_of_lt_of_le hN_gtK htN
  have ht_geK : K ≤ t := ht_gtK.le
  -- Now: t⁻¹ * ∫_0^t f - L = t⁻¹ * (∫_0^t f - t * L) = t⁻¹ * ∫_0^t (f - L).
  have hintf : IntervalIntegrable f volume 0 t := hf.intervalIntegrable 0 t
  have hintc : IntervalIntegrable (fun _ : ℝ => L) volume 0 t :=
    intervalIntegrable_const
  have h_integral_L : (∫ x in (0:ℝ)..t, (L : ℝ)) = t * L := by
    simp
  have h_rewrite : t⁻¹ * (∫ x in (0:ℝ)..t, f x) - L
      = t⁻¹ * ∫ x in (0:ℝ)..t, (f x - L) := by
    have hsub : (∫ x in (0:ℝ)..t, (f x - L))
        = (∫ x in (0:ℝ)..t, f x) - (∫ x in (0:ℝ)..t, (L : ℝ)) :=
      intervalIntegral.integral_sub hintf hintc
    rw [hsub, h_integral_L, mul_sub]
    have : t⁻¹ * (t * L) = L := by field_simp
    linarith
  rw [Real.dist_eq, h_rewrite, abs_mul, abs_inv, abs_of_pos ht_pos]
  -- Split ∫_0^t (f - L) = ∫_0^K (f - L) + ∫_K^t (f - L).
  have hintfL_0K : IntervalIntegrable (fun x => f x - L) volume 0 K :=
    (hf.sub continuous_const).intervalIntegrable 0 K
  have hintfL_Kt : IntervalIntegrable (fun x => f x - L) volume K t :=
    (hf.sub continuous_const).intervalIntegrable K t
  have hsplit : (∫ x in (0:ℝ)..t, (f x - L))
      = (∫ x in (0:ℝ)..K, (f x - L)) + (∫ x in K..t, (f x - L)) :=
    (intervalIntegral.integral_add_adjacent_intervals hintfL_0K hintfL_Kt).symm
  rw [hsplit]
  -- Bound the two integrals.
  have h_abs_first : |∫ x in (0:ℝ)..K, (f x - L)| ≤ M := by
    rw [hM_def]
    have := intervalIntegral.abs_integral_le_integral_abs hK_nonneg
      (f := fun x => f x - L) (μ := volume)
    exact this
  have h_abs_second : |∫ x in K..t, (f x - L)| ≤ (t - K) * (ε / 2) := by
    have hint_sec : IntervalIntegrable (fun x => |f x - L|) volume K t :=
      (hf.sub continuous_const).abs.intervalIntegrable K t
    have habs_bnd := intervalIntegral.abs_integral_le_integral_abs ht_geK
      (f := fun x => f x - L) (μ := volume)
    have hcompar : (∫ x in K..t, |f x - L|) ≤ ∫ x in K..t, (ε / 2) := by
      apply intervalIntegral.integral_mono_on ht_geK hint_sec intervalIntegrable_const
      intro x hx
      have hxK : K ≤ x := hx.1
      exact (hbound x hxK).le
    have hconst : (∫ x in K..t, (ε / 2 : ℝ)) = (t - K) * (ε / 2) := by
      simp; ring
    linarith
  -- Combine:
  -- |∫_0^t (f-L)| ≤ |∫_0^K| + |∫_K^t| ≤ M + (t - K) ε/2
  -- So t⁻¹ * |∫_0^t (f-L)| ≤ (M + (t-K) ε/2) / t ≤ M/t + ε/2 < ε/2 + ε/2 = ε
  have h_abs_total : |(∫ x in (0:ℝ)..K, (f x - L)) + ∫ x in K..t, (f x - L)|
      ≤ M + (t - K) * (ε / 2) := by
    calc |(∫ x in (0:ℝ)..K, (f x - L)) + ∫ x in K..t, (f x - L)|
        ≤ |∫ x in (0:ℝ)..K, (f x - L)| + |∫ x in K..t, (f x - L)| :=
          abs_add_le _ _
      _ ≤ M + (t - K) * (ε / 2) := by linarith
  have ht_inv_pos : 0 < t⁻¹ := inv_pos.mpr ht_pos
  calc t⁻¹ * |(∫ x in (0:ℝ)..K, (f x - L)) + ∫ x in K..t, (f x - L)|
      ≤ t⁻¹ * (M + (t - K) * (ε / 2)) :=
        mul_le_mul_of_nonneg_left h_abs_total ht_inv_pos.le
    _ = t⁻¹ * M + t⁻¹ * ((t - K) * (ε / 2)) := by ring
    _ ≤ t⁻¹ * M + t⁻¹ * (t * (ε / 2)) := by
        have h1 : (t - K) * (ε / 2) ≤ t * (ε / 2) :=
          mul_le_mul_of_nonneg_right (by linarith) hε2.le
        have h2 : t⁻¹ * ((t - K) * (ε / 2)) ≤ t⁻¹ * (t * (ε / 2)) :=
          mul_le_mul_of_nonneg_left h1 ht_inv_pos.le
        linarith
    _ = t⁻¹ * M + ε / 2 := by field_simp
    _ < ε / 2 + ε / 2 := by
        have hMt : t⁻¹ * M < ε / 2 := by
          -- Need M / t < ε / 2, i.e., 2M < ε t, i.e., 2M/ε < t (if ε > 0).
          -- We have t ≥ N > 2M/ε, so ε t > 2 M, so M/t < ε/2.
          by_cases hM_zero : M = 0
          · rw [hM_zero, mul_zero]; exact hε2
          · have hM_pos : 0 < M := lt_of_le_of_ne hM_nonneg (Ne.symm hM_zero)
            have ht_gt : 2 * M / ε < t := lt_of_lt_of_le hN_gt_twoMoverε htN
            rw [show t⁻¹ * M = M / t from by field_simp [ht_pos.ne']]
            rw [div_lt_iff₀ ht_pos]
            rw [div_lt_iff₀ hε] at ht_gt
            linarith
        linarith
    _ = ε := by ring

snip end

problem imc2017_p6 (f : ℝ → ℝ) (hf : Continuous f) (L : ℝ)
    (hL : Tendsto f atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => ∫ x in (0:ℝ)..1, f (n * x)) atTop (𝓝 L) := by
  -- First get the real-variable limit.
  have h_real : Tendsto (fun t : ℝ => t⁻¹ * ∫ x in (0:ℝ)..t, f x) atTop (𝓝 L) :=
    tendsto_average_of_tendsto hf hL
  -- Compose with the cast ℕ → ℝ.
  have h_nat : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∫ x in (0:ℝ)..(n : ℝ), f x) atTop (𝓝 L) :=
    h_real.comp tendsto_natCast_atTop_atTop
  -- Rewrite ∫_0^1 f(nx) dx = n⁻¹ * ∫_0^n f for n ≠ 0.
  refine Tendsto.congr' ?_ h_nat
  rw [EventuallyEq, Filter.eventually_atTop]
  refine ⟨1, fun n hn => ?_⟩
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  rw [integral_comp_mul_eq f hn_ne, smul_eq_mul]

end Imc2017P6
