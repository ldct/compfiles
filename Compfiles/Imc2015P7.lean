/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2015, Problem 7

Compute
\[ \lim_{A \to +\infty} \frac{1}{A} \int_1^A A^{1/x}\,dx. \]

The answer is `1`.
-/

namespace Imc2015P7

open Real Filter Topology MeasureTheory intervalIntegral

snip begin

/-- For `A ≥ 1` and `x ≥ 1`, we have `1 ≤ A ^ (1/x)`. -/
lemma one_le_rpow_inv {A : ℝ} (hA : 1 ≤ A) {x : ℝ} (hx : 0 < x) :
    1 ≤ A ^ (x⁻¹) := by
  have : (1 : ℝ) = (1 : ℝ) ^ (x⁻¹) := by
    rw [Real.one_rpow]
  rw [this]
  exact Real.rpow_le_rpow (by norm_num) hA (by positivity)

/-- The function `x ↦ A^(1/x)` is continuous on `(0, ∞)`. -/
lemma continuous_rpow_inv {A : ℝ} (hA : 0 < A) :
    ContinuousOn (fun x : ℝ => A ^ (x⁻¹)) (Set.Ioi 0) := by
  intro x hx
  have hx_pos : 0 < x := hx
  have hx_ne : x ≠ 0 := hx_pos.ne'
  apply ContinuousAt.continuousWithinAt
  have h1 : ContinuousAt (fun y : ℝ => y⁻¹) x := continuousAt_inv₀ hx_ne
  have h2 : ContinuousAt (fun y : ℝ => A ^ y) (x⁻¹) := by
    exact (Real.continuous_const_rpow (ne_of_gt hA)).continuousAt
  exact h2.comp h1

/-- On `[1, A]`, `x ↦ A^(1/x)` is continuous (hence integrable). -/
lemma intervalIntegrable_rpow_inv {A : ℝ} (hA : 0 < A) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ => A ^ (x⁻¹)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hsub : Set.uIcc a b ⊆ Set.Ioi 0 := by
    intro x hx
    rcases le_total a b with hab | hab
    · rw [Set.uIcc_of_le hab] at hx
      exact lt_of_lt_of_le ha hx.1
    · rw [Set.uIcc_of_ge hab] at hx
      exact lt_of_lt_of_le hb hx.1
  exact (continuous_rpow_inv hA).mono hsub

/-- For `A > 1` and `0 < x ≤ y`, `A^(1/y) ≤ A^(1/x)`. -/
lemma rpow_inv_antitone {A : ℝ} (hA : 1 ≤ A) {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) : A ^ (y⁻¹) ≤ A ^ (x⁻¹) := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hinv : y⁻¹ ≤ x⁻¹ := by
    rw [inv_le_inv₀ hy hx]; exact hxy
  exact Real.rpow_le_rpow_of_exponent_le hA hinv

/-- Lower bound: for `A > 1`, `(1/A) · ∫_1^A A^(1/x) dx ≥ 1 - 1/A`. -/
lemma lower_bound {A : ℝ} (hA : 1 < A) :
    1 - A⁻¹ ≤ A⁻¹ * ∫ x in (1 : ℝ)..A, A ^ (x⁻¹) := by
  have hA0 : 0 < A := lt_trans zero_lt_one hA
  have hA1 : (1 : ℝ) ≤ A := hA.le
  have hAle : (1 : ℝ) ≤ A := hA.le
  -- `∫_1^A A^(1/x) dx ≥ ∫_1^A 1 dx = A - 1`.
  have h1 : (∫ x in (1:ℝ)..A, (1 : ℝ)) ≤ ∫ x in (1:ℝ)..A, A ^ (x⁻¹) := by
    apply intervalIntegral.integral_mono_on hAle intervalIntegral.intervalIntegrable_const
    · exact intervalIntegrable_rpow_inv hA0 1 A zero_lt_one hA0
    · intro x hx
      have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
      exact one_le_rpow_inv hA1 hx_pos
  have h2 : (∫ x in (1:ℝ)..A, (1 : ℝ)) = A - 1 := by
    simp
  rw [h2] at h1
  have hAinv_pos : 0 < A⁻¹ := inv_pos.mpr hA0
  have := mul_le_mul_of_nonneg_left h1 hAinv_pos.le
  rw [show A⁻¹ * (A - 1) = 1 - A⁻¹ from by field_simp] at this
  exact this

/-- Upper bound on the integral split at `1+δ` and `K · log A`.
For `A` large enough (specifically `A > exp((1+δ)/δ · ???)`), we can split
`[1, A]` at `1+δ` and `K · log A`, giving
`(1/A) · ∫_1^A A^(1/x) dx ≤ δ + K · (log A) · A^(-δ/(1+δ)) + exp(1/K)`. -/
lemma upper_bound_split {A δ K : ℝ} (hA : 1 < A) (hδ : 0 < δ)
    (hK : 0 < K) (hsplit1 : 1 + δ ≤ K * Real.log A)
    (hsplit2 : K * Real.log A ≤ A) :
    A⁻¹ * (∫ x in (1 : ℝ)..A, A ^ (x⁻¹))
      ≤ δ + K * Real.log A * A ^ (-(δ / (1 + δ))) + Real.exp (1 / K) := by
  have hA0 : 0 < A := lt_trans zero_lt_one hA
  have hA1 : (1 : ℝ) ≤ A := hA.le
  have hA1_lt : (1 : ℝ) < A := hA
  have hlogA_pos : 0 < Real.log A := Real.log_pos hA1_lt
  have h1δ_pos : 0 < 1 + δ := by linarith
  have h1δ_le : 1 ≤ 1 + δ := by linarith
  have hKlog_pos : 0 < K * Real.log A := mul_pos hK hlogA_pos
  have h1_le_1δ : (1 : ℝ) ≤ 1 + δ := h1δ_le
  have h1δ_le_Klog : 1 + δ ≤ K * Real.log A := hsplit1
  have hKlog_le_A : K * Real.log A ≤ A := hsplit2
  have h1_le_Klog : (1 : ℝ) ≤ K * Real.log A := le_trans h1_le_1δ h1δ_le_Klog
  have h1_le_A : (1 : ℝ) ≤ A := hA1
  -- Integrability on sub-intervals.
  have hint_full : IntervalIntegrable (fun x : ℝ => A ^ (x⁻¹)) volume 1 A :=
    intervalIntegrable_rpow_inv hA0 1 A zero_lt_one hA0
  have hint1 : IntervalIntegrable (fun x : ℝ => A ^ (x⁻¹)) volume 1 (1 + δ) :=
    intervalIntegrable_rpow_inv hA0 1 (1 + δ) zero_lt_one h1δ_pos
  have hint2 : IntervalIntegrable (fun x : ℝ => A ^ (x⁻¹)) volume
                 (1 + δ) (K * Real.log A) :=
    intervalIntegrable_rpow_inv hA0 (1 + δ) (K * Real.log A) h1δ_pos hKlog_pos
  have hint3 : IntervalIntegrable (fun x : ℝ => A ^ (x⁻¹)) volume
                 (K * Real.log A) A :=
    intervalIntegrable_rpow_inv hA0 (K * Real.log A) A hKlog_pos hA0
  -- Split the integral.
  have hsplit_int : (∫ x in (1:ℝ)..A, A ^ (x⁻¹))
      = (∫ x in (1:ℝ)..(1 + δ), A ^ (x⁻¹))
        + (∫ x in (1 + δ)..(K * Real.log A), A ^ (x⁻¹))
        + (∫ x in (K * Real.log A)..A, A ^ (x⁻¹)) := by
    rw [intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hint1.trans hint2) hint3]
  -- Bound each piece.
  -- Piece 1: on [1, 1+δ], A^(1/x) ≤ A.
  have hpiece1 : (∫ x in (1:ℝ)..(1 + δ), A ^ (x⁻¹)) ≤ δ * A := by
    have hbound : ∀ x ∈ Set.Icc (1 : ℝ) (1 + δ), A ^ (x⁻¹) ≤ A := by
      intro x hx
      have hx1 : 1 ≤ x := hx.1
      have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
      have hinv_le : x⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]; exact Or.inr hx1
      calc A ^ (x⁻¹) ≤ A ^ (1 : ℝ) := by
            exact Real.rpow_le_rpow_of_exponent_le hA1 hinv_le
        _ = A := Real.rpow_one A
    have := intervalIntegral.integral_mono_on h1_le_1δ hint1
      intervalIntegral.intervalIntegrable_const hbound
    have hconst : (∫ _ in (1:ℝ)..(1 + δ), A) = δ * A := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    rw [hconst] at this
    exact this
  -- Piece 2: on [1+δ, K log A], A^(1/x) ≤ A^(1/(1+δ)).
  have hpiece2 : (∫ x in (1 + δ)..(K * Real.log A), A ^ (x⁻¹))
      ≤ (K * Real.log A - (1 + δ)) * A ^ ((1 + δ)⁻¹) := by
    have hbound : ∀ x ∈ Set.Icc (1 + δ) (K * Real.log A),
        A ^ (x⁻¹) ≤ A ^ ((1 + δ)⁻¹) := by
      intro x hx
      have hx1 : 1 + δ ≤ x := hx.1
      exact rpow_inv_antitone hA1 h1δ_pos hx1
    have := intervalIntegral.integral_mono_on h1δ_le_Klog hint2
      intervalIntegral.intervalIntegrable_const hbound
    have hconst : (∫ _ in (1 + δ)..(K * Real.log A), A ^ ((1 + δ)⁻¹))
        = (K * Real.log A - (1 + δ)) * A ^ ((1 + δ)⁻¹) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    rw [hconst] at this
    exact this
  -- Piece 3: on [K log A, A], A^(1/x) ≤ A^(1/(K log A)) = e^(1/K).
  have hpiece3 : (∫ x in (K * Real.log A)..A, A ^ (x⁻¹))
      ≤ (A - K * Real.log A) * Real.exp (1 / K) := by
    have hbound : ∀ x ∈ Set.Icc (K * Real.log A) A,
        A ^ (x⁻¹) ≤ Real.exp (1 / K) := by
      intro x hx
      have hx1 : K * Real.log A ≤ x := hx.1
      have hx_pos : 0 < x := lt_of_lt_of_le hKlog_pos hx1
      -- A^(1/x) ≤ A^(1/(K log A)) = exp((1/(K log A)) · log A) = exp(1/K).
      have step1 : A ^ (x⁻¹) ≤ A ^ ((K * Real.log A)⁻¹) :=
        rpow_inv_antitone hA1 hKlog_pos hx1
      have step2 : A ^ ((K * Real.log A)⁻¹) = Real.exp (1 / K) := by
        rw [Real.rpow_def_of_pos hA0]
        congr 1
        field_simp
      rw [step2] at step1
      exact step1
    have := intervalIntegral.integral_mono_on hKlog_le_A hint3
      intervalIntegral.intervalIntegrable_const hbound
    have hconst : (∫ _ in (K * Real.log A)..A, Real.exp (1 / K))
        = (A - K * Real.log A) * Real.exp (1 / K) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    rw [hconst] at this
    exact this
  -- Combine.
  have hAinv_pos : 0 < A⁻¹ := inv_pos.mpr hA0
  have hsum_bound : (∫ x in (1:ℝ)..A, A ^ (x⁻¹))
      ≤ δ * A + (K * Real.log A - (1 + δ)) * A ^ ((1 + δ)⁻¹)
        + (A - K * Real.log A) * Real.exp (1 / K) := by
    rw [hsplit_int]; linarith
  -- Divide by A.
  have hdiv := mul_le_mul_of_nonneg_left hsum_bound hAinv_pos.le
  -- Simplify: A⁻¹ * (δ * A) = δ.
  -- A⁻¹ * ((K log A - (1+δ)) * A^(1/(1+δ)))
  --   ≤ A⁻¹ * (K log A * A^(1/(1+δ))) [since (1+δ) > 0, K log A - (1+δ) ≤ K log A]
  --   = K log A * A^(1/(1+δ) - 1) = K log A * A^(-δ/(1+δ)).
  -- A⁻¹ * ((A - K log A) * e^(1/K)) ≤ A⁻¹ * (A * e^(1/K)) = e^(1/K).
  calc A⁻¹ * (∫ x in (1:ℝ)..A, A ^ (x⁻¹))
      ≤ A⁻¹ * (δ * A + (K * Real.log A - (1 + δ)) * A ^ ((1 + δ)⁻¹)
              + (A - K * Real.log A) * Real.exp (1 / K)) := hdiv
    _ = A⁻¹ * (δ * A) + A⁻¹ * ((K * Real.log A - (1 + δ)) * A ^ ((1 + δ)⁻¹))
        + A⁻¹ * ((A - K * Real.log A) * Real.exp (1 / K)) := by ring
    _ ≤ δ + K * Real.log A * A ^ (-(δ / (1 + δ))) + Real.exp (1 / K) := by
        have h_first : A⁻¹ * (δ * A) = δ := by
          field_simp
        have hApos_for_rpow : 0 < A := hA0
        have h_rpow_pos : 0 < A ^ ((1 + δ)⁻¹) := Real.rpow_pos_of_pos hA0 _
        have h_second :
            A⁻¹ * ((K * Real.log A - (1 + δ)) * A ^ ((1 + δ)⁻¹))
              ≤ K * Real.log A * A ^ (-(δ / (1 + δ))) := by
          have hle : (K * Real.log A - (1 + δ)) ≤ K * Real.log A := by linarith
          have h_mono : (K * Real.log A - (1 + δ)) * A ^ ((1 + δ)⁻¹)
              ≤ K * Real.log A * A ^ ((1 + δ)⁻¹) :=
            mul_le_mul_of_nonneg_right hle h_rpow_pos.le
          have hmul := mul_le_mul_of_nonneg_left h_mono hAinv_pos.le
          -- A⁻¹ * (K log A * A^(1/(1+δ))) = K log A * A^(1/(1+δ) - 1)
          --   = K log A * A^(-δ/(1+δ)).
          have hrw : A⁻¹ * (K * Real.log A * A ^ ((1 + δ)⁻¹))
              = K * Real.log A * A ^ (-(δ / (1 + δ))) := by
            have h_inv_rpow : A⁻¹ = A ^ (-(1 : ℝ)) := by
              rw [Real.rpow_neg_one]
            rw [h_inv_rpow]
            rw [show A ^ (-(1 : ℝ)) * (K * Real.log A * A ^ ((1 + δ)⁻¹))
                  = K * Real.log A * (A ^ (-(1 : ℝ)) * A ^ ((1 + δ)⁻¹))
                  from by ring]
            rw [← Real.rpow_add hA0]
            congr 2
            have h1δ_ne : (1 + δ : ℝ) ≠ 0 := h1δ_pos.ne'
            field_simp
            ring
          rw [hrw] at hmul
          exact hmul
        have h_third :
            A⁻¹ * ((A - K * Real.log A) * Real.exp (1 / K))
              ≤ Real.exp (1 / K) := by
          have hexp_pos : 0 < Real.exp (1 / K) := Real.exp_pos _
          have hle : (A - K * Real.log A) ≤ A := by linarith
          have h_mono : (A - K * Real.log A) * Real.exp (1 / K)
              ≤ A * Real.exp (1 / K) :=
            mul_le_mul_of_nonneg_right hle hexp_pos.le
          have hmul := mul_le_mul_of_nonneg_left h_mono hAinv_pos.le
          have hrw : A⁻¹ * (A * Real.exp (1 / K)) = Real.exp (1 / K) := by
            field_simp
          rw [hrw] at hmul
          exact hmul
        linarith [h_first]

/-- Main lemma: `(1/A) · ∫_1^A A^(1/x) dx → 1` as `A → ∞` (through reals `≥ 1`). -/
lemma tendsto_avg_integral :
    Tendsto (fun A : ℝ => A⁻¹ * ∫ x in (1 : ℝ)..A, A ^ (x⁻¹)) atTop (𝓝 1) := by
  -- Use `ε`-`N` characterization.
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Choose `δ = ε/3`, `K` so that `exp(1/K) < 1 + ε/3`.
  -- Pick `δ = ε/3`. Pick `K` so that `1/K < log(1 + ε/3)` is sufficient.
  -- Actually we need `e^(1/K) ≤ 1 + ε/3`, so `1/K ≤ log(1 + ε/3)`, i.e.,
  -- `K ≥ 1 / log(1 + ε/3)`.
  set δ : ℝ := ε / 3 with hδ_def
  have hδ_pos : 0 < δ := by rw [hδ_def]; linarith
  -- Pick `K` such that `exp(1/K) ≤ 1 + ε/3`, i.e., `K ≥ 1 / log(1 + ε/3)`.
  have hε3_pos : (0 : ℝ) < 1 + ε / 3 := by linarith
  have hε3_gt1 : (1 : ℝ) < 1 + ε / 3 := by linarith
  have hlog_pos : 0 < Real.log (1 + ε / 3) := Real.log_pos hε3_gt1
  set K : ℝ := (Real.log (1 + ε / 3))⁻¹ + 1 with hK_def
  have hK_pos : 0 < K := by
    show 0 < (Real.log (1 + ε / 3))⁻¹ + 1
    positivity
  have hKinv_lt : 1 / K < Real.log (1 + ε / 3) := by
    rw [div_lt_iff₀ hK_pos]
    show 1 < Real.log (1 + ε / 3) * ((Real.log (1 + ε / 3))⁻¹ + 1)
    have h1 : Real.log (1 + ε / 3) * ((Real.log (1 + ε / 3))⁻¹ + 1)
        = 1 + Real.log (1 + ε / 3) := by
      rw [mul_add, mul_inv_cancel₀ hlog_pos.ne', mul_one]
    rw [h1]; linarith
  have hexp_K : Real.exp (1 / K) < 1 + ε / 3 := by
    calc Real.exp (1 / K) < Real.exp (Real.log (1 + ε / 3)) :=
          Real.exp_lt_exp.mpr hKinv_lt
      _ = 1 + ε / 3 := Real.exp_log hε3_pos
  -- Middle term: `K * log A * A^(-δ/(1+δ)) → 0` as `A → ∞`.
  have hexp_neg_pos : 0 < δ / (1 + δ) := by positivity
  have h_middle_tendsto :
      Tendsto (fun A : ℝ => K * Real.log A * A ^ (-(δ / (1 + δ)))) atTop (𝓝 0) := by
    -- log A * A^(-c) → 0 for c > 0.
    have h_key : Tendsto (fun A : ℝ => Real.log A * A ^ (-(δ / (1 + δ)))) atTop (𝓝 0) := by
      have hlo : Real.log =o[atTop] (fun x : ℝ => x ^ (δ / (1 + δ))) :=
        isLittleO_log_rpow_atTop hexp_neg_pos
      have htend : Tendsto (fun A : ℝ => Real.log A / A ^ (δ / (1 + δ))) atTop (𝓝 0) :=
        hlo.tendsto_div_nhds_zero
      refine htend.congr' ?_
      rw [EventuallyEq, Filter.eventually_atTop]
      refine ⟨1, fun A hA => ?_⟩
      have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one hA
      rw [Real.rpow_neg hA_pos.le, div_eq_mul_inv]
    have h_mul : Tendsto (fun A : ℝ => K * (Real.log A * A ^ (-(δ / (1 + δ)))))
                   atTop (𝓝 (K * 0)) :=
      h_key.const_mul K
    rw [mul_zero] at h_mul
    refine h_mul.congr (fun A => ?_)
    ring
  -- Now: we want eventually `|A⁻¹ * ∫_1^A A^(1/x) dx - 1| < ε`.
  -- Lower bound gives `A⁻¹ * ∫ ≥ 1 - A⁻¹`, so `A⁻¹ * ∫ - 1 ≥ -A⁻¹`.
  -- Upper bound (when applicable) gives `A⁻¹ * ∫ ≤ δ + K log A * A^(-δ/(1+δ)) + exp(1/K)`
  --   `< ε/3 + ε/3 + (1 + ε/3) = 1 + ε` for A large.
  -- So `A⁻¹ * ∫ - 1 < ε`.
  -- We need `1 + δ ≤ K log A ≤ A`.
  -- `K log A ≥ 1 + δ` iff `log A ≥ (1+δ)/K`, i.e., `A ≥ exp((1+δ)/K)`.
  -- `K log A ≤ A`: for A ≥ exp(2K), we have log A ≥ 2K, so A = exp(log A) ≥ exp(2K)·... actually
  -- we need A/log A ≥ K. Use: A ≥ exp(something large) so that log A ≤ A/K.
  -- For A ≥ K² (say, with A > 1), log A ≤ A/K iff K log A ≤ A. Since log A ≤ √A for large A
  -- and √A * K ≤ A iff K ≤ √A iff A ≥ K². So we need A ≥ K² and A large enough for log bound.
  -- Actually simpler: as A → ∞, log A / A → 0, so eventually log A ≤ A/K, i.e. K log A ≤ A.
  -- Use `Real.tendsto_log_div_atTop_nhds_zero`.
  have h_logA_over_A : Tendsto (fun A : ℝ => Real.log A / A) atTop (𝓝 0) := by
    have hlo : Real.log =o[atTop] (fun x : ℝ => x ^ (1 : ℝ)) :=
      isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)
    have htend : Tendsto (fun A : ℝ => Real.log A / A ^ (1 : ℝ)) atTop (𝓝 0) :=
      hlo.tendsto_div_nhds_zero
    refine htend.congr' ?_
    rw [EventuallyEq, Filter.eventually_atTop]
    refine ⟨1, fun A _ => ?_⟩
    rw [Real.rpow_one]
  -- Get |log A / A| < 1/K eventually (for A large).
  have h_split_bound : ∀ᶠ A : ℝ in atTop, K * Real.log A ≤ A := by
    have hKinv_pos : 0 < 1 / K := by positivity
    have h_eventually : ∀ᶠ A : ℝ in atTop, Real.log A / A < 1 / K := by
      have : ∀ᶠ A : ℝ in atTop, Real.log A / A ∈ Set.Iio (1 / K) := by
        apply h_logA_over_A.eventually
        exact IsOpen.mem_nhds isOpen_Iio (by simpa using hKinv_pos)
      exact this
    have h_eventually_pos : ∀ᶠ A : ℝ in atTop, (1 : ℝ) < A := Filter.eventually_gt_atTop 1
    filter_upwards [h_eventually, h_eventually_pos] with A hA hA_gt
    have hA_pos : 0 < A := lt_trans zero_lt_one hA_gt
    rw [div_lt_div_iff₀ hA_pos hK_pos] at hA
    linarith
  -- First split condition: 1 + δ ≤ K log A iff log A ≥ (1+δ)/K.
  have h_split1 : ∀ᶠ A : ℝ in atTop, 1 + δ ≤ K * Real.log A := by
    have h_log_atTop : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
    have hlog_ge : ∀ᶠ A : ℝ in atTop, (1 + δ) / K ≤ Real.log A :=
      h_log_atTop.eventually_ge_atTop ((1 + δ) / K)
    filter_upwards [hlog_ge] with A hA
    rw [div_le_iff₀ hK_pos] at hA
    linarith
  -- Middle tendsto, get it small.
  have hε3_pos2 : (0 : ℝ) < ε / 3 := by linarith
  have h_middle_small : ∀ᶠ A : ℝ in atTop,
      K * Real.log A * A ^ (-(δ / (1 + δ))) < ε / 3 := by
    have : ∀ᶠ A : ℝ in atTop,
        K * Real.log A * A ^ (-(δ / (1 + δ))) ∈ Set.Iio (ε / 3) := by
      apply h_middle_tendsto.eventually
      exact IsOpen.mem_nhds isOpen_Iio (by simpa using hε3_pos2)
    exact this
  -- Also need A > 1 eventually, and 1/A < ε eventually.
  have h_A_gt1 : ∀ᶠ A : ℝ in atTop, (1 : ℝ) < A := Filter.eventually_gt_atTop 1
  have h_invA_small : ∀ᶠ A : ℝ in atTop, A⁻¹ < ε := by
    have h_invA_to_0 : Tendsto (fun A : ℝ => A⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero
    have : ∀ᶠ A : ℝ in atTop, A⁻¹ ∈ Set.Iio ε := by
      apply h_invA_to_0.eventually
      exact IsOpen.mem_nhds isOpen_Iio (by simpa using hε)
    exact this
  -- Combine eventualities.
  have h_all := (h_split_bound.and (h_split1.and (h_middle_small.and
    (h_A_gt1.and h_invA_small))))
  rw [Filter.eventually_atTop] at h_all
  obtain ⟨N, hN⟩ := h_all
  refine ⟨N, ?_⟩
  intro A hA
  obtain ⟨h_split_bd, h_split1_bd, h_mid_lt0, h_A_gt, h_invA_bd⟩ := hN A hA
  have h_A_pos : 0 < A := lt_trans zero_lt_one h_A_gt
  -- Apply lower and upper bounds.
  have h_lower := lower_bound h_A_gt
  have h_upper := upper_bound_split h_A_gt hδ_pos hK_pos h_split1_bd h_split_bd
  -- Combine.
  -- |A⁻¹ * ∫ - 1| < ε.
  rw [Real.dist_eq]
  -- A⁻¹ * ∫ ∈ [1 - A⁻¹, 1 + ε]: we need to show |·| < ε.
  set S : ℝ := A⁻¹ * ∫ x in (1 : ℝ)..A, A ^ (x⁻¹) with hS_def
  have h_S_ge : 1 - A⁻¹ ≤ S := h_lower
  have h_S_le : S ≤ δ + K * Real.log A * A ^ (-(δ / (1 + δ))) + Real.exp (1 / K) := h_upper
  -- The middle term is `< ε/3`.
  have h_mid_lt : K * Real.log A * A ^ (-(δ / (1 + δ))) < ε / 3 := h_mid_lt0
  have h_exp_lt : Real.exp (1 / K) < 1 + ε / 3 := hexp_K
  have h_upper2 : S < δ + ε / 3 + (1 + ε / 3) := by
    linarith
  have h_delta_eq : δ = ε / 3 := hδ_def
  rw [h_delta_eq] at h_upper2
  have h_upper3 : S < 1 + ε := by linarith
  have h_lower2 : 1 - ε < S := by linarith
  rw [abs_lt]
  exact ⟨by linarith, by linarith⟩

snip end

problem imc2015_p7 :
    Tendsto (fun A : ℝ => A⁻¹ * ∫ x in (1 : ℝ)..A, A ^ (x⁻¹)) atTop (𝓝 1) :=
  tendsto_avg_integral

end Imc2015P7
