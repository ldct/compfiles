/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2003, Problem 8
(IMC 2003, Day 2, Problem 2)

Let `m, n` be natural numbers. Evaluate

  `lim_{x → 0⁺} ∫_x^{2x} (sin t)^m / t^n dt`.

The answer is:
* `0` if `m ≥ n`;
* `ln 2` if `n = m + 1`;
* `+∞` if `n ≥ m + 2`.
-/

namespace Imc2003P8

open Real Set MeasureTheory intervalIntegral Filter Topology

snip begin

/-- For `0 < t ≤ 1`, `0 ≤ sin t ≤ t`. -/
lemma sin_bounds {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    0 ≤ Real.sin t ∧ Real.sin t ≤ t := by
  have hpi : t ≤ Real.pi := ht1.trans (by linarith [Real.pi_gt_three])
  exact ⟨Real.sin_nonneg_of_nonneg_of_le_pi ht.le hpi, Real.sin_le ht.le⟩

/-- For `0 < t ≤ 1`, `0 ≤ (sin t)^m ≤ t^m`. -/
lemma sin_pow_le_pow {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (m : ℕ) :
    0 ≤ (Real.sin t)^m ∧ (Real.sin t)^m ≤ t^m := by
  obtain ⟨h0, h1⟩ := sin_bounds ht ht1
  exact ⟨pow_nonneg h0 m, pow_le_pow_left₀ h0 h1 m⟩

/-- For `0 < t ≤ 1`, `(t - t^3/4)^m ≤ (sin t)^m`. -/
lemma sin_pow_ge {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (m : ℕ) :
    (t - t^3/4)^m ≤ (Real.sin t)^m := by
  have hlt : t - t^3/4 < Real.sin t := Real.sin_gt_sub_cube ht ht1
  have hnn : 0 ≤ t - t^3/4 := by
    have hcube : t^3 ≤ t := by
      have ht2 : t^2 ≤ 1 := by nlinarith
      calc t^3 = t^2 * t := by ring
        _ ≤ 1 * t := by apply mul_le_mul_of_nonneg_right ht2 ht.le
        _ = t := one_mul _
    linarith
  exact pow_le_pow_left₀ hnn hlt.le m

/-- The integral `∫_x^{2x} 1/t dt = ln 2` for `x > 0`. -/
lemma integral_inv_interval {x : ℝ} (hx : 0 < x) :
    ∫ t in x..(2*x), t⁻¹ = Real.log 2 := by
  have h2x : 0 < 2 * x := by linarith
  have hle : x ≤ 2 * x := by linarith
  rw [integral_inv (by
    rw [uIcc_of_le hle]
    intro h
    have hmem : (0:ℝ) ∈ Icc x (2*x) := h
    linarith [hmem.1])]
  rw [Real.log_div h2x.ne' hx.ne']
  have hmul : Real.log (2 * x) = Real.log 2 + Real.log x :=
    Real.log_mul (by norm_num) hx.ne'
  rw [hmul]; ring

/-- The integrand `(sin t)^m / t^n` is continuous on `[x, 2x]` for `x > 0`, hence integrable. -/
lemma intIntegrable_sinPow_div_tPow (m n : ℕ) {x : ℝ} (hx : 0 < x) :
    IntervalIntegrable (fun t : ℝ => (Real.sin t)^m / t^n) volume x (2*x) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by linarith : x ≤ 2*x)]
  apply ContinuousOn.div
  · exact (Real.continuous_sin.pow m).continuousOn
  · exact (continuous_id.pow n).continuousOn
  · intro t ht
    have : 0 < t := lt_of_lt_of_le hx ht.1
    exact pow_ne_zero _ this.ne'

/-- `∫_x^{2x} t^k dt`. -/
lemma integral_pow_interval (k : ℕ) (x : ℝ) :
    ∫ t in x..(2*x), t^k = ((2*x)^(k+1) - x^(k+1)) / (k+1) :=
  integral_pow (a := x) (b := 2 * x) (n := k)

snip end

/-- The answer depends on `(m, n)`. We state three separate claims. -/
problem imc2003_p8 :
    -- Case m ≥ n: limit is 0.
    (∀ m n : ℕ, n ≤ m →
      Tendsto (fun x : ℝ => ∫ t in x..(2*x), (Real.sin t)^m / t^n)
        (𝓝[>] 0) (𝓝 0)) ∧
    -- Case n = m + 1: limit is ln 2.
    (∀ m : ℕ,
      Tendsto (fun x : ℝ => ∫ t in x..(2*x), (Real.sin t)^m / t^(m+1))
        (𝓝[>] 0) (𝓝 (Real.log 2))) ∧
    -- Case n ≥ m + 2: limit is +∞.
    (∀ m n : ℕ, m + 2 ≤ n →
      Tendsto (fun x : ℝ => ∫ t in x..(2*x), (Real.sin t)^m / t^n)
        (𝓝[>] 0) atTop) := by
  refine ⟨?_, ?_, ?_⟩
  -- ============================================================
  -- Case 1: m ≥ n, limit is 0.
  -- ============================================================
  · intro m n hnm
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    set k : ℕ := m - n with hk_def
    have hk : m = n + k := by omega
    set C : ℝ := ((2:ℝ)^(k+1) - 1) / (k+1) with hC_def
    have hC_pos : 0 < C := by
      rw [hC_def]
      apply div_pos
      · have h2pow_gt : (1:ℝ) < 2^(k+1) := by
          have : (1:ℝ) = 1^(k+1) := (one_pow _).symm
          rw [this]
          exact pow_lt_pow_left₀ (by norm_num : (1:ℝ) < 2) (by norm_num) (by omega)
        linarith
      · exact_mod_cast (by omega : 0 < k+1)
    refine ⟨min (1/2) (ε / (C + 1)), ?_, ?_⟩
    · apply lt_min; · norm_num
      · exact div_pos hε (by linarith)
    intro x hx₁ hxdist
    simp only [Real.dist_eq] at hxdist
    have hx_pos : 0 < x := hx₁
    have hx_abs : |x| = x := abs_of_pos hx_pos
    have hx_lt : x < min (1/2) (ε / (C + 1)) := by rwa [sub_zero, hx_abs] at hxdist
    have hx_le_half : x ≤ 1/2 := le_of_lt (lt_of_lt_of_le hx_lt (min_le_left _ _))
    have hx_le_one : x ≤ 1 := by linarith
    have hx_lt_eps : x < ε / (C + 1) := lt_of_lt_of_le hx_lt (min_le_right _ _)
    have h2x_le_one : 2 * x ≤ 1 := by linarith
    -- Bound: sin^m t / t^n ≤ t^k, with both ≥ 0, for t ∈ [x, 2x].
    have h_le_integrand : ∀ t ∈ Icc x (2*x), 0 ≤ (Real.sin t)^m / t^n
        ∧ (Real.sin t)^m / t^n ≤ t^k := by
      intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le hx_pos ht.1
      have ht_le_one : t ≤ 1 := ht.2.trans h2x_le_one
      obtain ⟨hs_nn, hs_le⟩ := sin_pow_le_pow ht_pos ht_le_one m
      have ht_pow_pos : 0 < t^n := pow_pos ht_pos n
      refine ⟨div_nonneg hs_nn ht_pow_pos.le, ?_⟩
      rw [div_le_iff₀ ht_pow_pos]
      calc (Real.sin t)^m ≤ t^m := hs_le
        _ = t^(n+k) := by rw [← hk]
        _ = t^k * t^n := by rw [pow_add]; ring
    have hxle : x ≤ 2*x := by linarith
    have h_int_nn : 0 ≤ ∫ t in x..(2*x), (Real.sin t)^m / t^n := by
      apply integral_nonneg hxle
      intro t ht
      exact (h_le_integrand t ⟨ht.1, ht.2⟩).1
    have h_int_le : ∫ t in x..(2*x), (Real.sin t)^m / t^n ≤ ∫ t in x..(2*x), t^k := by
      apply integral_mono_on hxle
      · exact intIntegrable_sinPow_div_tPow m n hx_pos
      · exact ((continuous_id.pow k).continuousOn).intervalIntegrable
      · intro t ht
        exact (h_le_integrand t ht).2
    have h_eq : ∫ t in x..(2*x), t^k = C * x^(k+1) := by
      rw [integral_pow_interval, hC_def]
      have : (2*x)^(k+1) - x^(k+1) = (2^(k+1) - 1) * x^(k+1) := by
        rw [mul_pow]; ring
      rw [this]; ring
    have h_xpow_le : x^(k+1) ≤ x := by
      have hpow : x^(k+1) ≤ x^1 :=
        pow_le_pow_of_le_one hx_pos.le hx_le_one (by omega)
      simpa using hpow
    have habs : |(∫ t in x..(2*x), (Real.sin t)^m / t^n) - 0| =
        ∫ t in x..(2*x), (Real.sin t)^m / t^n := by
      rw [sub_zero]; exact abs_of_nonneg h_int_nn
    rw [Real.dist_eq, habs]
    calc ∫ t in x..(2*x), (Real.sin t)^m / t^n
        ≤ ∫ t in x..(2*x), t^k := h_int_le
      _ = C * x^(k+1) := h_eq
      _ ≤ C * x := mul_le_mul_of_nonneg_left h_xpow_le hC_pos.le
      _ < C * (ε/(C+1)) := mul_lt_mul_of_pos_left hx_lt_eps hC_pos
      _ = C * ε / (C + 1) := by rw [mul_div_assoc]
      _ ≤ ε := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith
  -- ============================================================
  -- Case 2: n = m + 1, limit is ln 2.
  -- ============================================================
  · intro m
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    by_cases hm : m = 0
    · -- m = 0: the integrand is 1/t, integral is exactly ln 2.
      subst hm
      refine ⟨1, by norm_num, ?_⟩
      intro x hx₁ hxdist
      simp only [Real.dist_eq] at hxdist
      have hx_pos : 0 < x := hx₁
      have hint : ∫ t in x..(2*x), (Real.sin t)^0 / t^(0+1) = ∫ t in x..(2*x), t⁻¹ := by
        congr 1
        ext t
        simp
      rw [hint, integral_inv_interval hx_pos, Real.dist_eq, sub_self, abs_zero]
      exact hε
    · -- m ≥ 1.
      have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      set δ : ℝ := min (1/2) (ε / ((m : ℝ) * Real.log 2 + 1)) with hδ_def
      have hδ_pos : 0 < δ := by
        apply lt_min; · norm_num
        · apply div_pos hε
          have : (0:ℝ) ≤ (m : ℝ) * Real.log 2 := mul_nonneg (by exact_mod_cast Nat.zero_le m) hlog2.le
          linarith
      refine ⟨δ, hδ_pos, ?_⟩
      intro x hx₁ hxdist
      simp only [Real.dist_eq] at hxdist
      have hx_pos : 0 < x := hx₁
      have hx_lt : x < δ := by rwa [sub_zero, abs_of_pos hx_pos] at hxdist
      have hx_le_half : x ≤ 1/2 := le_of_lt (lt_of_lt_of_le hx_lt (min_le_left _ _))
      have hx_le_one : x ≤ 1 := by linarith
      have hx_le_eps : x < ε / ((m : ℝ) * Real.log 2 + 1) := lt_of_lt_of_le hx_lt (min_le_right _ _)
      have h2x_le_one : 2 * x ≤ 1 := by linarith
      have hx_sq : x^2 ≤ x := by
        calc x^2 = x * x := sq x
          _ ≤ 1 * x := by apply mul_le_mul_of_nonneg_right hx_le_one hx_pos.le
          _ = x := one_mul _
      -- Upper bound: sin^m t / t^{m+1} ≤ 1/t on [x, 2x].
      have h_upper_pt : ∀ t ∈ Icc x (2*x), (Real.sin t)^m / t^(m+1) ≤ t⁻¹ := by
        intro t ht
        have ht_pos : 0 < t := lt_of_lt_of_le hx_pos ht.1
        have ht_le_one : t ≤ 1 := ht.2.trans h2x_le_one
        obtain ⟨_, hs_le⟩ := sin_pow_le_pow ht_pos ht_le_one m
        have ht_pow_pos : 0 < t^(m+1) := pow_pos ht_pos _
        rw [div_le_iff₀ ht_pow_pos, inv_eq_one_div, div_mul_eq_mul_div, le_div_iff₀ ht_pos, one_mul]
        calc (Real.sin t)^m * t ≤ t^m * t := mul_le_mul_of_nonneg_right hs_le ht_pos.le
          _ = t^(m+1) := by ring
      -- Lower bound: (1 - m x²)/t ≤ sin^m t / t^{m+1}.
      have h_lower_pt : ∀ t ∈ Icc x (2*x),
          (1 - (m : ℝ) * x^2) / t ≤ (Real.sin t)^m / t^(m+1) := by
        intro t ht
        have ht_pos : 0 < t := lt_of_lt_of_le hx_pos ht.1
        have ht_le_one : t ≤ 1 := ht.2.trans h2x_le_one
        have ht_le_2x : t ≤ 2*x := ht.2
        have ht_pow_pos : 0 < t^(m+1) := pow_pos ht_pos _
        have hsin_pow_ge : (t - t^3/4)^m ≤ (Real.sin t)^m := sin_pow_ge ht_pos ht_le_one m
        have h_factor : (t - t^3/4)^m = t^m * (1 - t^2/4)^m := by
          have : t - t^3/4 = t * (1 - t^2/4) := by ring
          rw [this, mul_pow]
        have h_t2_le_one : t^2/4 ≤ 1 := by
          have : t^2 ≤ 1 := by
            calc t^2 = t * t := sq t
              _ ≤ 1 * 1 := by apply mul_le_mul ht_le_one ht_le_one ht_pos.le (by norm_num)
              _ = 1 := by norm_num
          linarith
        have h_bernoulli : 1 - (m : ℝ) * (t^2/4) ≤ (1 - t^2/4)^m := by
          have hge : (-2 : ℝ) ≤ -(t^2/4) := by
            have : t^2/4 ≤ 1 := h_t2_le_one; linarith
          have := one_add_mul_le_pow hge m
          have h_eq1 : (1 : ℝ) + (m : ℝ) * (-(t^2/4)) = 1 - (m : ℝ) * (t^2/4) := by ring
          have h_eq2 : (1 : ℝ) + -(t^2/4) = 1 - t^2/4 := by ring
          rw [h_eq1, h_eq2] at this
          exact this
        have h_t2_le : t^2/4 ≤ x^2 := by
          have hnn : 0 ≤ t := ht_pos.le
          have h2x_nn : 0 ≤ 2*x := by linarith
          have : t^2 ≤ (2*x)^2 := by
            have := mul_self_le_mul_self hnn ht_le_2x
            calc t^2 = t * t := sq t
              _ ≤ (2*x) * (2*x) := this
              _ = (2*x)^2 := by ring
          calc t^2/4 ≤ (2*x)^2/4 := by linarith
            _ = x^2 := by ring
        have h_mt : (m : ℝ) * (t^2/4) ≤ (m : ℝ) * x^2 :=
          mul_le_mul_of_nonneg_left h_t2_le (by exact_mod_cast Nat.zero_le m)
        have h_pow_ge : 1 - (m : ℝ) * x^2 ≤ (1 - t^2/4)^m := by linarith
        have hstep : t^m * (1 - (m : ℝ) * x^2) ≤ (Real.sin t)^m := by
          calc t^m * (1 - (m : ℝ) * x^2) ≤ t^m * (1 - t^2/4)^m := by
                apply mul_le_mul_of_nonneg_left h_pow_ge (pow_nonneg ht_pos.le m)
            _ = (t - t^3/4)^m := h_factor.symm
            _ ≤ (Real.sin t)^m := hsin_pow_ge
        have heq : (1 - (m : ℝ) * x^2) / t = t^m * (1 - (m : ℝ) * x^2) / t^(m+1) := by
          rw [show t^(m+1) = t^m * t from by ring]
          rw [mul_div_mul_left _ _ (pow_ne_zero m ht_pos.ne')]
        rw [heq]
        exact div_le_div_of_nonneg_right hstep ht_pow_pos.le
      set I : ℝ := ∫ t in x..(2*x), (Real.sin t)^m / t^(m+1) with hI_def
      have hxle : x ≤ 2*x := by linarith
      have h_int_upper : I ≤ ∫ t in x..(2*x), t⁻¹ := by
        apply integral_mono_on hxle
        · exact intIntegrable_sinPow_div_tPow m (m+1) hx_pos
        · apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le hxle]
          apply ContinuousOn.inv₀
          · exact continuous_id.continuousOn
          · intro t ht
            have : 0 < t := lt_of_lt_of_le hx_pos ht.1
            exact this.ne'
        · exact h_upper_pt
      have h_int_lower : ∫ t in x..(2*x), (1 - (m : ℝ) * x^2) / t ≤ I := by
        apply integral_mono_on hxle
        · apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le hxle]
          apply ContinuousOn.div continuousOn_const continuous_id.continuousOn
          intro t ht hcontra
          simp only [id_eq] at hcontra
          linarith [ht.1]
        · exact intIntegrable_sinPow_div_tPow m (m+1) hx_pos
        · exact h_lower_pt
      have h_upper_eq : ∫ t in x..(2*x), t⁻¹ = Real.log 2 := integral_inv_interval hx_pos
      have h_lower_eq : ∫ t in x..(2*x), (1 - (m : ℝ) * x^2) / t
          = (1 - (m : ℝ) * x^2) * Real.log 2 := by
        have hrw : (fun t : ℝ => (1 - (m : ℝ) * x^2) / t)
            = fun t : ℝ => (1 - (m : ℝ) * x^2) * t⁻¹ := by
          ext t; rw [div_eq_mul_inv]
        rw [show (∫ t in x..(2*x), (1 - (m : ℝ) * x^2) / t)
          = ∫ t in x..(2*x), (1 - (m : ℝ) * x^2) * t⁻¹ from by
              simp_rw [div_eq_mul_inv]]
        rw [intervalIntegral.integral_const_mul, integral_inv_interval hx_pos]
      rw [Real.dist_eq]
      have hI_ge : (1 - (m : ℝ) * x^2) * Real.log 2 ≤ I := by
        rw [← h_lower_eq]; exact h_int_lower
      have hI_le : I ≤ Real.log 2 := by rw [← h_upper_eq]; exact h_int_upper
      have habs : |I - Real.log 2| ≤ (m : ℝ) * x^2 * Real.log 2 := by
        have h1 : I - Real.log 2 ≤ 0 := by linarith
        have hexpand : (1 - (m : ℝ) * x^2) * Real.log 2
            = Real.log 2 - (m : ℝ) * x^2 * Real.log 2 := by ring
        have h2 : -((m : ℝ) * x^2 * Real.log 2) ≤ I - Real.log 2 := by linarith
        rw [abs_le]
        refine ⟨h2, by linarith⟩
      -- Now: |I - log 2| ≤ m x² log 2 ≤ m x log 2 < m · ε/(m log 2 + 1) · log 2 < ε.
      have hmnn : (0:ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
      have hmpos : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
      calc |I - Real.log 2|
          ≤ (m : ℝ) * x^2 * Real.log 2 := habs
        _ ≤ (m : ℝ) * x * Real.log 2 := by
            apply mul_le_mul_of_nonneg_right _ hlog2.le
            exact mul_le_mul_of_nonneg_left hx_sq hmnn
        _ < (m : ℝ) * (ε / ((m : ℝ) * Real.log 2 + 1)) * Real.log 2 := by
            apply mul_lt_mul_of_pos_right _ hlog2
            exact mul_lt_mul_of_pos_left hx_le_eps hmpos
        _ = ((m : ℝ) * Real.log 2) * ε / ((m : ℝ) * Real.log 2 + 1) := by ring
        _ < ε := by
            have hprod_pos : 0 < (m : ℝ) * Real.log 2 := mul_pos hmpos hlog2
            rw [div_lt_iff₀ (by linarith)]
            nlinarith
  -- ============================================================
  -- Case 3: n ≥ m + 2, limit is +∞.
  -- ============================================================
  · intro m n hnm
    rw [tendsto_atTop]
    intro M
    -- k := n - m - 1 ≥ 1. On [x, 2x] ⊂ (0, 1]:
    -- sin t ≥ (2/π) t ⇒ sin^m t ≥ (2/π)^m t^m ⇒ sin^m t / t^n ≥ (2/π)^m / t^{k+1}.
    -- ∫ 1/t^{k+1} dt = (x^{-k} - (2x)^{-k})/k = (1 - 2^{-k})/k · x^{-k}.
    -- So integral ≥ D · x^{-k} where D = (2/π)^m · (1 - 2^{-k})/k > 0.
    -- Since k ≥ 1 and x ≤ 1, x^{-k} ≥ 1/x. Pick x small to make D/x ≥ M.
    set k : ℕ := n - m - 1 with hk_def
    have hk_ge : 1 ≤ k := by omega
    have hn_eq : n = m + (k + 1) := by omega
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have h2pi_pos : 0 < 2 / Real.pi := by positivity
    have h2pi_le : 2 / Real.pi ≤ 1 := by
      rw [div_le_one hpi_pos]
      linarith [Real.pi_gt_three]
    have hpow_pos : 0 < (2 / Real.pi)^m := pow_pos h2pi_pos _
    -- D = (2/π)^m * (1 - 2^{-k})/k.
    set D : ℝ := (2 / Real.pi)^m * ((1 - (2:ℝ)^(-(k:ℤ))) / k) with hD_def
    have h_2mk_pos : 0 < 1 - (2:ℝ)^(-(k:ℤ)) := by
      have h2lt : (2:ℝ)^(-(k:ℤ)) < 1 := by
        rw [zpow_neg, zpow_natCast]
        rw [inv_lt_one_iff₀]
        right
        have : (1:ℝ) = 1^k := (one_pow k).symm
        calc (1:ℝ) = 1^k := this
          _ < 2^k := by
              apply pow_lt_pow_left₀ (by norm_num : (1:ℝ) < 2) (by norm_num) (by omega)
      linarith
    have hD_pos : 0 < D := by
      rw [hD_def]
      apply mul_pos hpow_pos
      apply div_pos h_2mk_pos
      exact_mod_cast hk_ge
    -- Choose x ∈ (0, min(1/2, D/(|M|+1))).
    set Mp : ℝ := max M 1 with hMp_def
    have hMp_ge : M ≤ Mp := le_max_left _ _
    have hMp_pos : 0 < Mp := lt_of_lt_of_le one_pos (le_max_right _ _)
    set δ : ℝ := min (1/2) (D / Mp) with hδ_def
    have hδ_pos : 0 < δ := by
      apply lt_min; · norm_num
      · exact div_pos hD_pos hMp_pos
    -- Use eventually: since 𝓝[>] 0 contains Ioo 0 δ.
    have hIoo : Ioo 0 δ ∈ 𝓝[>] (0 : ℝ) := by
      rw [mem_nhdsWithin]
      refine ⟨Iio δ, isOpen_Iio, hδ_pos, ?_⟩
      intro y hy
      exact ⟨hy.2, hy.1⟩
    filter_upwards [hIoo] with x hx
    have hx_pos : 0 < x := hx.1
    have hx_lt_δ : x < δ := hx.2
    have hx_le_half : x ≤ 1/2 := le_of_lt (lt_of_lt_of_le hx_lt_δ (min_le_left _ _))
    have hx_le_one : x ≤ 1 := by linarith
    have hx_le_D : x < D / Mp := lt_of_lt_of_le hx_lt_δ (min_le_right _ _)
    have h2x_le_one : 2 * x ≤ 1 := by linarith
    have h2x_le_pi2 : 2 * x ≤ Real.pi / 2 := by
      calc 2 * x ≤ 1 := h2x_le_one
        _ ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
    -- Lower bound pointwise: sin^m t / t^n ≥ (2/π)^m / t^{k+1}.
    have h_lower_pt : ∀ t ∈ Icc x (2*x),
        (2 / Real.pi)^m / t^(k+1) ≤ (Real.sin t)^m / t^n := by
      intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le hx_pos ht.1
      have ht_le_2x : t ≤ 2*x := ht.2
      have ht_le_pi2 : t ≤ Real.pi / 2 := ht_le_2x.trans h2x_le_pi2
      have hsin_ge : (2 / Real.pi) * t ≤ Real.sin t := Real.mul_le_sin ht_pos.le ht_le_pi2
      have h2pt_nn : 0 ≤ (2 / Real.pi) * t := mul_nonneg h2pi_pos.le ht_pos.le
      have h_sinpow_ge : ((2 / Real.pi) * t)^m ≤ (Real.sin t)^m :=
        pow_le_pow_left₀ h2pt_nn hsin_ge m
      have h_sinpow_expand : ((2 / Real.pi) * t)^m = (2 / Real.pi)^m * t^m := mul_pow _ _ _
      have ht_pow_pos_n : 0 < t^n := pow_pos ht_pos n
      have ht_pow_pos_k : 0 < t^(k+1) := pow_pos ht_pos _
      rw [div_le_div_iff₀ ht_pow_pos_k ht_pow_pos_n]
      calc (2/Real.pi)^m * t^n = (2/Real.pi)^m * t^m * t^(k+1) := by
              rw [hn_eq]; ring
        _ = ((2/Real.pi) * t)^m * t^(k+1) := by rw [mul_pow]
        _ ≤ (Real.sin t)^m * t^(k+1) := by
            apply mul_le_mul_of_nonneg_right h_sinpow_ge (pow_nonneg ht_pos.le _)
    -- Compute ∫ 1/t^{k+1} over [x, 2x] = (x^{-k} - (2x)^{-k})/k = (1 - 2^{-k})/k * x^{-k}.
    have h_int_inv_pow : ∫ t in x..(2*x), t^(-((k+1):ℤ))
        = ((2*x)^(-((k:ℤ)+1)+1) - x^(-((k:ℤ)+1)+1)) / ((-((k:ℤ)+1) : ℝ)+1) := by
      have h2x : 0 < 2 * x := by linarith
      have hle : x ≤ 2 * x := by linarith
      have hnot_in : (0:ℝ) ∉ uIcc x (2*x) := by
        rw [uIcc_of_le hle]
        intro h
        have hmem : (0:ℝ) ∈ Icc x (2*x) := h
        linarith [hmem.1]
      have hne : (-((k+1):ℤ)) ≠ -1 := by
        intro heq
        have hk_eq : (k : ℤ) = 0 := by linarith
        have : k = 0 := by exact_mod_cast hk_eq
        omega
      have h := integral_zpow (a := x) (b := 2*x) (n := -((k:ℤ)+1)) (Or.inr ⟨hne, hnot_in⟩)
      convert h using 2
      push_cast; ring
    -- Simplify: -(k+1)+1 = -k.
    have h_exp_simp : ∀ (a : ℝ), 0 < a → a^(-((k+1):ℤ)+1) = a^(-(k:ℤ)) := by
      intro a ha
      congr 1; omega
    have h_int_inv_pow' : ∫ t in x..(2*x), t^(-((k+1):ℤ))
        = ((2*x)^(-(k:ℤ)) - x^(-(k:ℤ))) / (-(k:ℤ)) := by
      rw [h_int_inv_pow]
      have h2x : 0 < 2 * x := by linarith
      rw [h_exp_simp _ hx_pos, h_exp_simp _ h2x]
      congr 1
      push_cast; ring
    -- Rewrite (x^{-k} - (2x)^{-k})/k = -((2x)^{-k} - x^{-k})/k.
    -- Actually: ((2x)^{-k} - x^{-k})/(-k) = (x^{-k} - (2x)^{-k})/k.
    -- Want: = (1 - 2^{-k})/k · x^{-k}.
    -- x^{-k} - (2x)^{-k} = x^{-k} (1 - 2^{-k}).
    have h_int_eq_D_form : ∫ t in x..(2*x), t^(-((k+1):ℤ))
        = (1 - (2:ℝ)^(-(k:ℤ))) / k * x^(-(k:ℤ)) := by
      rw [h_int_inv_pow']
      have h2x : 0 < 2 * x := by linarith
      have h2x_ne : (2 * x) ≠ 0 := h2x.ne'
      have h2_ne : (2 : ℝ) ≠ 0 := by norm_num
      have hx_ne : x ≠ 0 := hx_pos.ne'
      -- (2x)^{-k} = 2^{-k} * x^{-k}.
      have h2x_pow : (2*x)^(-(k:ℤ)) = (2:ℝ)^(-(k:ℤ)) * x^(-(k:ℤ)) := by
        rw [mul_zpow]
      rw [h2x_pow]
      have hk_ne : (k : ℝ) ≠ 0 := by
        have : (0 : ℝ) < k := by exact_mod_cast hk_ge
        linarith
      field_simp
      push_cast
      ring
    -- Now 1/t^{k+1} = t^{-(k+1)}:
    have h_inv_pow_eq : ∀ t : ℝ, t > 0 → (1 : ℝ) / t^(k+1) = t^(-((k+1):ℤ)) := by
      intro t ht
      rw [one_div, ← zpow_natCast, ← zpow_neg]
      push_cast; rfl
    -- Lower bound the integral:
    have h_mono : ∫ t in x..(2*x), (2 / Real.pi)^m / t^(k+1)
        ≤ ∫ t in x..(2*x), (Real.sin t)^m / t^n := by
      have hxle : x ≤ 2*x := by linarith
      apply integral_mono_on hxle
      · apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hxle]
        apply ContinuousOn.div continuousOn_const
        · exact (continuous_id.pow _).continuousOn
        · intro t ht; exact pow_ne_zero _ (lt_of_lt_of_le hx_pos ht.1).ne'
      · exact intIntegrable_sinPow_div_tPow m n hx_pos
      · exact h_lower_pt
    -- Compute the lower integral = (2/π)^m · (1 - 2^{-k})/k · x^{-k} = D · x^{-k}.
    have h_lower_int_eq : ∫ t in x..(2*x), (2 / Real.pi)^m / t^(k+1)
        = D * x^(-(k:ℤ)) := by
      have : (fun t : ℝ => (2 / Real.pi)^m / t^(k+1))
          = fun t : ℝ => (2 / Real.pi)^m * (t^(k+1))⁻¹ := by
        ext t; rw [div_eq_mul_inv]
      rw [show (∫ t in x..(2*x), (2 / Real.pi)^m / t^(k+1))
        = ∫ t in x..(2*x), (2 / Real.pi)^m * (t^(k+1))⁻¹ from by
            simp_rw [div_eq_mul_inv]]
      rw [intervalIntegral.integral_const_mul]
      have h_inv_eq : (fun t : ℝ => (t^(k+1))⁻¹) = fun t : ℝ => t^(-((k+1):ℤ)) := by
        ext t
        rw [← zpow_natCast, ← zpow_neg]
        push_cast; rfl
      rw [h_inv_eq]
      rw [h_int_eq_D_form]
      rw [hD_def]; ring
    -- x^{-k} ≥ 1/x since k ≥ 1 and x ≤ 1. So D * x^{-k} ≥ D/x.
    have h_xk_inv_ge : (1 : ℝ) / x ≤ x^(-(k:ℤ)) := by
      rw [zpow_neg, zpow_natCast, one_div]
      rw [inv_le_inv₀ hx_pos (pow_pos hx_pos _)]
      have : x^k ≤ x^1 := pow_le_pow_of_le_one hx_pos.le hx_le_one hk_ge
      simpa using this
    have h_Dxk_ge : D / x ≤ D * x^(-(k:ℤ)) := by
      rw [show D / x = D * (1/x) from by rw [mul_one_div]]
      exact mul_le_mul_of_nonneg_left h_xk_inv_ge hD_pos.le
    -- D/x ≥ Mp since x < D/Mp. Hence ≥ M.
    have hDx_ge_Mp : Mp ≤ D / x := by
      rw [le_div_iff₀ hx_pos]
      rw [lt_div_iff₀ hMp_pos] at hx_le_D
      linarith
    calc M ≤ Mp := hMp_ge
      _ ≤ D / x := hDx_ge_Mp
      _ ≤ D * x^(-(k:ℤ)) := h_Dxk_ge
      _ = ∫ t in x..(2*x), (2 / Real.pi)^m / t^(k+1) := h_lower_int_eq.symm
      _ ≤ ∫ t in x..(2*x), (Real.sin t)^m / t^n := h_mono

end Imc2003P8
