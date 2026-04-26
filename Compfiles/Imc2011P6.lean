/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2011, Problem 6

Let `(aₙ)` be a sequence with `1/2 < aₙ < 1` for all `n ≥ 0`. Define `(xₙ)` by
`x₀ = a₀` and `x_{n+1} = (a_{n+1} + xₙ) / (1 + a_{n+1} * xₙ)`. Prove that
`xₙ → 1`.

## Solution

We show by induction that `1/2 < xₙ < 1` and `0 < 1 - xₙ < 1/2^{n+1}`. From the
recurrence,
  `1 - x_{n+1} = (1 - a_{n+1}) / (1 + a_{n+1} xₙ) · (1 - xₙ)`,
and the multiplier is in `(0, 1/2)`, so `1 - xₙ` decays geometrically.
-/

namespace Imc2011P6

snip begin

/-- Joint induction: both `1/2 < xₙ < 1` and `0 < 1 - xₙ < 1/2^{n+1}`. -/
lemma bounds (a : ℕ → ℝ) (ha : ∀ n, 1/2 < a n ∧ a n < 1)
    (x : ℕ → ℝ) (hx0 : x 0 = a 0)
    (hxrec : ∀ n, x (n+1) = (a (n+1) + x n) / (1 + a (n+1) * x n)) :
    ∀ n, 1/2 < x n ∧ x n < 1 ∧ 1 - x n < 1 / 2^(n+1) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · rw [hx0]; exact (ha 0).1
    · rw [hx0]; exact (ha 0).2
    · rw [hx0]; have := (ha 0).1; norm_num; linarith
  | succ n ih =>
    obtain ⟨hxlo, hxhi, hxdiff⟩ := ih
    have han := ha (n+1)
    -- denominator positive and ≥ 5/4 > 1
    have hden_pos : 0 < 1 + a (n+1) * x n := by
      have h1 : 0 < a (n+1) := by linarith [han.1]
      have h2 : 0 < x n := by linarith
      have : 0 < a (n+1) * x n := mul_pos h1 h2
      linarith
    have hden_gt_one : 1 < 1 + a (n+1) * x n := by
      have h1 : 1/2 < a (n+1) := han.1
      have h2 : 1/2 < x n := hxlo
      have h3 : 0 < a (n+1) := by linarith
      have h4 : 0 < x n := by linarith
      have : 1/4 < a (n+1) * x n := by
        calc (1:ℝ)/4 = (1/2) * (1/2) := by norm_num
          _ < a (n+1) * x n := by
            have := mul_lt_mul' (le_of_lt h1) h2 (by norm_num) h3
            linarith [this]
      linarith
    -- key formula: 1 - x_{n+1} = (1 - a_{n+1})/(1 + a_{n+1} x_n) * (1 - x_n)
    have hkey : 1 - x (n+1) = (1 - a (n+1)) / (1 + a (n+1) * x n) * (1 - x n) := by
      rw [hxrec n]
      field_simp
      ring
    -- multiplier in (0, 1/2)
    have hnumer_pos : 0 < 1 - a (n+1) := by linarith [han.2]
    have hnumer_lt : 1 - a (n+1) < 1/2 := by linarith [han.1]
    have hmult_pos : 0 < (1 - a (n+1)) / (1 + a (n+1) * x n) :=
      div_pos hnumer_pos hden_pos
    have hmult_lt_half : (1 - a (n+1)) / (1 + a (n+1) * x n) < 1/2 := by
      rw [div_lt_iff₀ hden_pos]
      have : 1 - a (n+1) < 1/2 * 1 := by linarith
      have h2 : (1:ℝ)/2 * 1 ≤ 1/2 * (1 + a (n+1) * x n) := by
        have h3 : (1:ℝ) ≤ 1 + a (n+1) * x n := le_of_lt hden_gt_one
        linarith
      linarith
    have h1mxn_pos : 0 < 1 - x n := by linarith
    -- 0 < 1 - x_{n+1}
    have hpos_succ : 0 < 1 - x (n+1) := by
      rw [hkey]
      exact mul_pos hmult_pos h1mxn_pos
    -- 1 - x_{n+1} < (1/2) * (1 - x n)
    have hhalf : 1 - x (n+1) < (1/2) * (1 - x n) := by
      rw [hkey]
      exact mul_lt_mul_of_pos_right hmult_lt_half h1mxn_pos
    -- 1 - x_{n+1} < 1 / 2^(n+2)
    have hgeom : 1 - x (n+1) < 1 / 2^(n+2) := by
      calc 1 - x (n+1) < (1/2) * (1 - x n) := hhalf
        _ < (1/2) * (1 / 2^(n+1)) := by
            apply mul_lt_mul_of_pos_left hxdiff (by norm_num)
        _ = 1 / 2^(n+2) := by
            rw [pow_succ]; ring
    -- x_{n+1} < 1
    have hxn1_lt : x (n+1) < 1 := by linarith
    -- x_{n+1} > 1/2: need 1 - x_{n+1} < 1/2.
    have h_sub_half : 1 - x (n+1) < 1/2 := by
      calc 1 - x (n+1) < 1 / 2^(n+2) := hgeom
        _ ≤ 1 / 2 := by
            apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
            have : (2:ℝ)^1 ≤ 2^(n+2) := by
              apply pow_le_pow_right₀ (by norm_num); omega
            simpa using this
    have hxn1_gt : 1/2 < x (n+1) := by linarith
    exact ⟨hxn1_gt, hxn1_lt, hgeom⟩

snip end

problem imc2011_p6 (a : ℕ → ℝ) (ha : ∀ n, 1/2 < a n ∧ a n < 1)
    (x : ℕ → ℝ) (hx0 : x 0 = a 0)
    (hxrec : ∀ n, x (n+1) = (a (n+1) + x n) / (1 + a (n+1) * x n)) :
    Filter.Tendsto x Filter.atTop (nhds 1) := by
  have hb := bounds a ha x hx0 hxrec
  -- x n → 1 follows from |1 - x n| < 1/2^(n+1) → 0.
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Choose N with 1/2^(N+1) < ε.
  have h2pos : (0:ℝ) < 2 := by norm_num
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / (2:ℝ)^(N+1) < ε := by
    -- 1/2^k → 0
    have h : Filter.Tendsto (fun k : ℕ => (1:ℝ) / 2^(k+1)) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun k : ℕ => ((1:ℝ)/2)^(k+1)) Filter.atTop (nhds 0) := by
        have := tendsto_pow_atTop_nhds_zero_of_lt_one (show (0:ℝ) ≤ 1/2 by norm_num)
          (show (1:ℝ)/2 < 1 by norm_num)
        exact this.comp (Filter.tendsto_add_atTop_nat 1)
      apply h1.congr
      intro k
      rw [div_pow, one_pow]
    rw [Metric.tendsto_atTop] at h
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, ?_⟩
    have := hN N (le_refl _)
    rw [Real.dist_eq, sub_zero] at this
    have hpos : 0 < (1:ℝ) / 2^(N+1) := by positivity
    rw [abs_of_pos hpos] at this
    exact this
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨_, _, hdiff⟩ := hb n
  rw [Real.dist_eq]
  have h1mxn_pos : 0 ≤ 1 - x n := by
    obtain ⟨h1, h2, _⟩ := hb n
    linarith
  have habs : |x n - 1| = 1 - x n := by
    rw [abs_sub_comm, abs_of_nonneg h1mxn_pos]
  rw [habs]
  calc 1 - x n < 1 / 2^(n+1) := hdiff
    _ ≤ 1 / 2^(N+1) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact pow_le_pow_right₀ (by norm_num) (by omega)
    _ < ε := hN

end Imc2011P6
