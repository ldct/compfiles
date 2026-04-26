/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1995, Problem 12 (Day 2 Problem 6)

Suppose `{f_n}` is a sequence of continuous functions on `[0,1]` with
`∫₀¹ f_m f_n dx = δ_{m,n}` and `sup{|f_n(x)| : x ∈ [0,1], n ∈ ℕ} < ∞`.
Show that no subsequence `f_{n_k}` converges pointwise on `[0,1]`.

## Proof outline

Suppose for contradiction that `f_{φ k}(x) → g(x)` pointwise on `[0,1]` for
some strictly increasing `φ : ℕ → ℕ`. Let `M` be the uniform bound, so
`|f_n(x)| ≤ M` for all `n` and all `x ∈ [0,1]`. Then `|g(x)| ≤ M`.

By the dominated convergence theorem applied to `x ↦ f_{φ j}(x) f_{φ k}(x)`
(with fixed `j`, dominated by `M · |f_{φ j}|`) we have
  `∫ f_{φ j} f_{φ k} dx  →  ∫ f_{φ j} g dx` as `k → ∞`.
For `k > j` the LHS is `0` by orthogonality, so `∫ f_{φ j} g = 0` for every
`j`.

By dominated convergence applied to `x ↦ f_{φ k}(x) g(x)` (dominated by
`M · |g|`, integrable on `[0,1]`), we have
  `∫ f_{φ k} g dx  →  ∫ g² dx` as `k → ∞`.
But each integral on the LHS is `0`, so `∫ g² = 0`.

By dominated convergence applied to `x ↦ f_{φ k}(x)²` (dominated by `M²`),
  `∫ f_{φ k}² dx  →  ∫ g² dx` as `k → ∞`.
Each integral on the LHS is `1`, hence `∫ g² = 1`. Contradiction.
-/

namespace Imc1995P12

open MeasureTheory intervalIntegral Set Filter Topology

problem imc1995_p12
    (f : ℕ → ℝ → ℝ)
    (hcont : ∀ n, ContinuousOn (f n) (Icc (0:ℝ) 1))
    (horth : ∀ m n, ∫ x in (0:ℝ)..1, f m x * f n x = if m = n then 1 else 0)
    (hbound : ∃ M : ℝ, ∀ n x, x ∈ Icc (0:ℝ) 1 → |f n x| ≤ M) :
    ¬ ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∃ g : ℝ → ℝ,
      ∀ x ∈ Icc (0:ℝ) 1, Tendsto (fun k => f (φ k) x) atTop (𝓝 (g x)) := by
  rintro ⟨φ, hφ, g, hg⟩
  obtain ⟨M, hM⟩ := hbound
  -- M ≥ 0 since 0 ≤ |f 0 0| ≤ M and 0 ∈ Icc 0 1.
  have hM_nn : (0:ℝ) ≤ M := (abs_nonneg (f 0 0)).trans (hM 0 0 ⟨le_refl _, by norm_num⟩)
  -- Work with the restricted measure on Icc 0 1.
  set μ : Measure ℝ := volume.restrict (Icc (0:ℝ) 1) with hμ_def
  have hμ_finite : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [hμ_def, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        Real.volume_Icc]
    simp
  -- Each f n is integrable on the restricted measure.
  have hf_int_on : ∀ n, IntegrableOn (f n) (Icc (0:ℝ) 1) volume :=
    fun n => (hcont n).integrableOn_Icc
  have hf_int : ∀ n, Integrable (f n) μ := fun n => hf_int_on n
  have hf_meas : ∀ n, AEStronglyMeasurable (f n) μ :=
    fun n => (hf_int n).aestronglyMeasurable
  -- Bound on f n holds μ-a.e. (in fact on all of Icc 0 1).
  have hf_bound_ae : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ M := by
    intro n
    rw [hμ_def, ae_restrict_iff' measurableSet_Icc]
    exact ae_of_all _ (fun x hx => by rw [Real.norm_eq_abs]; exact hM n x hx)
  have hf_bound_abs_ae : ∀ n, ∀ᵐ x ∂μ, |f n x| ≤ M := by
    intro n; filter_upwards [hf_bound_ae n] with x hx using by
      rwa [Real.norm_eq_abs] at hx
  -- Pointwise convergence on [0,1] is μ-a.e. convergence.
  have hg_lim_ae : ∀ᵐ x ∂μ, Tendsto (fun k => f (φ k) x) atTop (𝓝 (g x)) := by
    rw [hμ_def, ae_restrict_iff' measurableSet_Icc]
    exact ae_of_all _ hg
  -- Bound on g.
  have hg_bound_ae : ∀ᵐ x ∂μ, |g x| ≤ M := by
    rw [hμ_def, ae_restrict_iff' measurableSet_Icc]
    refine ae_of_all _ (fun x hx => ?_)
    have htend := hg x hx
    have habs : Tendsto (fun k => |f (φ k) x|) atTop (𝓝 (|g x|)) := htend.abs
    have hbd : ∀ k, |f (φ k) x| ≤ M := fun k => hM (φ k) x hx
    exact le_of_tendsto' habs hbd
  have hg_bound_norm_ae : ∀ᵐ x ∂μ, ‖g x‖ ≤ M := by
    filter_upwards [hg_bound_ae] with x hx
    rwa [Real.norm_eq_abs]
  -- g is strongly measurable as a μ-a.e. limit of strongly measurable functions.
  have hg_meas : AEStronglyMeasurable g μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun k => hf_meas (φ k)) hg_lim_ae
  -- g integrable on the finite measure.
  have hg_int : Integrable g μ := by
    refine ⟨hg_meas, ?_⟩
    refine HasFiniteIntegral.mono' (g := fun _ : ℝ => M) (hasFiniteIntegral_const _) ?_
    exact hg_bound_norm_ae
  -- g² integrable.
  have hg2_int : Integrable (fun x => g x ^ 2) μ := by
    refine ⟨hg_meas.pow 2, ?_⟩
    refine HasFiniteIntegral.mono' (g := fun _ : ℝ => M ^ 2) (hasFiniteIntegral_const _) ?_
    filter_upwards [hg_bound_ae] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have : g x ^ 2 ≤ M ^ 2 := by nlinarith [abs_le.mp hx, sq_nonneg (g x)]
    exact this
  -- Step 1: ∫ f (φ j) * g dμ = 0 for every j.
  -- We'll prove ∫ f (φ j) f (φ k) dμ → ∫ f (φ j) g dμ as k → ∞, with LHS = 0
  -- for all sufficiently large k.
  have hf_g_int : ∀ j, Integrable (fun x => f (φ j) x * g x) μ := by
    intro j
    exact (hf_int (φ j)).mul_bdd hg_meas hg_bound_norm_ae
  have hf_f_int : ∀ j k, Integrable (fun x => f (φ j) x * f (φ k) x) μ := by
    intro j k
    exact (hf_int (φ j)).mul_bdd (hf_meas (φ k)) (hf_bound_ae (φ k))
  -- Convert interval integrals to set integrals over Icc 0 1.
  have hori : ∀ m n, ∫ x in (Icc (0:ℝ) 1), f m x * f n x ∂volume
      = if m = n then (1:ℝ) else 0 := by
    intro m n
    have h := horth m n
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)] at h
    rw [integral_Icc_eq_integral_Ioc]
    exact h
  have hori' : ∀ m n, ∫ x, f m x * f n x ∂μ = if m = n then (1:ℝ) else 0 := by
    intro m n
    show ∫ x in Icc (0:ℝ) 1, f m x * f n x ∂volume = _
    exact hori m n
  -- Apply DCT to the sequence k ↦ (x ↦ f (φ j) x * f (φ k) x), with j fixed.
  -- Bound: M * |f (φ j) x|.
  have hg_lim_j : ∀ j, Tendsto (fun k => ∫ x, f (φ j) x * f (φ k) x ∂μ) atTop
      (𝓝 (∫ x, f (φ j) x * g x ∂μ)) := by
    intro j
    -- bound function: x ↦ M * |f (φ j) x|.
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun x => M * |f (φ j) x|) ?_ ?_ ?_ ?_
    · -- AEStronglyMeasurable for each k
      exact Eventually.of_forall (fun k => (hf_meas (φ j)).mul (hf_meas (φ k)))
    · -- ∀ᵐ x, ‖f (φ j) x * f (φ k) x‖ ≤ M * |f (φ j) x|
      refine Eventually.of_forall (fun k => ?_)
      filter_upwards [hf_bound_abs_ae (φ k)] with x hx
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |f (φ j) x| * |f (φ k) x| ≤ |f (φ j) x| * M :=
        mul_le_mul_of_nonneg_left hx (abs_nonneg _)
      linarith [h1]
    · -- Bound integrable.
      exact ((hf_int (φ j)).abs).const_mul M
    · -- Pointwise convergence.
      filter_upwards [hg_lim_ae] with x hx
      have : Tendsto (fun k => f (φ j) x * f (φ k) x) atTop (𝓝 (f (φ j) x * g x)) :=
        hx.const_mul (f (φ j) x)
      exact this
  -- For k > j, ∫ f (φ j) f (φ k) dμ = 0.
  have hzero_j : ∀ j, ∫ x, f (φ j) x * g x ∂μ = 0 := by
    intro j
    have hlim := hg_lim_j j
    have hev : ∀ᶠ k in atTop, ∫ x, f (φ j) x * f (φ k) x ∂μ = 0 := by
      filter_upwards [eventually_gt_atTop j] with k hk
      have hne : φ j ≠ φ k := (hφ hk).ne
      rw [hori' (φ j) (φ k)]
      simp [hne]
    exact tendsto_nhds_unique (hlim.congr' hev) tendsto_const_nhds
  -- Step 2: ∫ g² dμ = 0.
  -- Apply DCT to k ↦ (x ↦ f (φ k) x * g x), bounded by M * |g x|.
  have hg2_lim : Tendsto (fun k => ∫ x, f (φ k) x * g x ∂μ) atTop
      (𝓝 (∫ x, g x ^ 2 ∂μ)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun x => M * |g x|) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall (fun k => (hf_meas (φ k)).mul hg_meas)
    · refine Eventually.of_forall (fun k => ?_)
      filter_upwards [hf_bound_abs_ae (φ k)] with x hx
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |f (φ k) x| * |g x| ≤ M * |g x| :=
        mul_le_mul_of_nonneg_right hx (abs_nonneg _)
      linarith [h1]
    · exact (hg_int.abs).const_mul M
    · filter_upwards [hg_lim_ae] with x hx
      have := hx.mul_const (g x)
      simpa [sq] using this
  have hg2_zero : ∫ x, g x ^ 2 ∂μ = 0 := by
    have hev : ∀ᶠ k in atTop, ∫ x, f (φ k) x * g x ∂μ = 0 :=
      Eventually.of_forall (fun k => hzero_j k)
    exact tendsto_nhds_unique (hg2_lim.congr' hev) tendsto_const_nhds
  -- Step 3: ∫ g² dμ = 1, contradiction.
  -- Apply DCT to k ↦ (x ↦ f (φ k) x ^ 2), bounded by M².
  have hg2_lim' : Tendsto (fun k => ∫ x, f (φ k) x * f (φ k) x ∂μ) atTop
      (𝓝 (∫ x, g x ^ 2 ∂μ)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ : ℝ => M ^ 2) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall (fun k => (hf_meas (φ k)).mul (hf_meas (φ k)))
    · refine Eventually.of_forall (fun k => ?_)
      filter_upwards [hf_bound_abs_ae (φ k)] with x hx
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |f (φ k) x| * |f (φ k) x| ≤ M * M :=
        mul_le_mul hx hx (abs_nonneg _) hM_nn
      have : |f (φ k) x| * |f (φ k) x| ≤ M ^ 2 := by rw [sq]; exact h1
      exact this
    · exact integrable_const _
    · filter_upwards [hg_lim_ae] with x hx
      have := hx.mul hx
      simpa [sq] using this
  have hg2_one : ∫ x, g x ^ 2 ∂μ = 1 := by
    have hev : ∀ᶠ k in atTop, ∫ x, f (φ k) x * f (φ k) x ∂μ = 1 := by
      refine Eventually.of_forall (fun k => ?_)
      rw [hori' (φ k) (φ k)]; simp
    exact tendsto_nhds_unique (hg2_lim'.congr' hev) tendsto_const_nhds
  -- Contradiction.
  have : (0:ℝ) = 1 := by rw [← hg2_zero, hg2_one]
  exact zero_ne_one this

end Imc1995P12
