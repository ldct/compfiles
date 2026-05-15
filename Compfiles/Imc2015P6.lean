/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2015, Problem 6

Prove that
\[ \sum_{n=1}^\infty \frac{1}{\sqrt{n}\,(n+1)} < 2. \]
-/

namespace Imc2015P6

open Real

snip begin

/-- Pointwise bound: for `n ≥ 1`, `1 / (√n · (n+1)) < 2/√n - 2/√(n+1)`.
We shift by 1 and index from `n : ℕ` starting at `0`. -/
lemma term_lt_diff (n : ℕ) :
    1 / (Real.sqrt (n + 1) * ((n : ℝ) + 2)) <
      2 / Real.sqrt (n + 1) - 2 / Real.sqrt (n + 2) := by
  set a : ℝ := Real.sqrt (n + 1) with ha
  set b : ℝ := Real.sqrt (n + 2) with hb
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have ha_pos : 0 < a := Real.sqrt_pos.mpr hn1
  have hb_pos : 0 < b := Real.sqrt_pos.mpr hn2
  have ha_sq : a ^ 2 = (n : ℝ) + 1 := by
    rw [ha, sq_sqrt hn1.le]
  have hb_sq : b ^ 2 = (n : ℝ) + 2 := by
    rw [hb, sq_sqrt hn2.le]
  -- a < b since n+1 < n+2
  have hab : a < b := by
    rw [ha, hb]; exact Real.sqrt_lt_sqrt hn1.le (by linarith)
  -- Key: 2 a b < a^2 + b^2 (since (b-a)^2 > 0)
  have hamgm : 2 * a * b < a ^ 2 + b ^ 2 := by
    have h : 0 < (b - a) ^ 2 := by
      apply sq_pos_of_ne_zero
      exact sub_ne_zero.mpr (ne_of_gt hab)
    nlinarith [h]
  -- Cross-multiply: 1 / (a * b^2) < 2/a - 2/b = 2(b-a)/(a*b)
  -- so want: b < 2 * b^2 * (b - a), i.e. b < 2 b^2 (b - a).
  -- Actually cleaner: multiply both sides by a * b * b^2 > 0:
  --   b < 2 b^2 * (b - a) * (? ) ... just do nlinarith after clearing denoms.
  have hab_pos : 0 < a * b := mul_pos ha_pos hb_pos
  have habb : 0 < a * b ^ 2 := by positivity
  -- Rewrite LHS and RHS in terms of a, b.
  -- LHS: 1 / (a * b^2) (note (n+1)+1 = n+2 = b^2).
  -- RHS: 2/a - 2/b.
  -- Rewrite 1/(a * ((n:ℝ)+2)) = 1/(a*b^2).
  have hlhs : 1 / (a * ((n : ℝ) + 2)) = 1 / (a * b ^ 2) := by rw [hb_sq]
  rw [hlhs]
  -- Now the inequality: 1/(a*b^2) < 2/a - 2/b.
  -- Key: 2 a b < a^2 + b^2 = (n+1) + (n+2) = 2n+3, so 2(n+2) - 2ab > 1.
  have hkey : 2 * a * b + 1 < 2 * ((n : ℝ) + 2) := by
    have h1 : a ^ 2 + b ^ 2 = 2 * (n : ℝ) + 3 := by rw [ha_sq, hb_sq]; ring
    linarith [hamgm, h1]
  -- Clear denominators: 1/(a*b^2) < 2/a - 2/b means (after multiplying by a*b^2 > 0):
  -- 1 < 2*b^2 - 2*a*b = 2(b^2 - a*b) = 2*(n+2) - 2*a*b, i.e. 2ab + 1 < 2(n+2). That's hkey.
  rw [lt_sub_iff_add_lt]
  rw [show (1 : ℝ) / (a * b ^ 2) + 2 / b = (1 + 2 * a * b) / (a * b ^ 2) from by
    field_simp]
  rw [div_lt_div_iff₀ (by positivity) ha_pos]
  -- Goal: (1 + 2 * a * b) * a < 2 * (a * b ^ 2)
  have hbsq : b ^ 2 = (n : ℝ) + 2 := hb_sq
  nlinarith [hkey, hbsq, ha_pos, hb_pos]

/-- Nonnegativity of the term. -/
lemma term_nonneg (n : ℕ) : 0 ≤ 1 / (Real.sqrt (n + 1) * ((n : ℝ) + 2)) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have ha : 0 < Real.sqrt (n + 1) := Real.sqrt_pos.mpr hn1
  positivity

/-- Nonnegativity of the difference `2/√(n+1) - 2/√(n+2)`. -/
lemma diff_nonneg (n : ℕ) :
    0 ≤ 2 / Real.sqrt (n + 1) - 2 / Real.sqrt (n + 2) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have ha : 0 < Real.sqrt (n + 1) := Real.sqrt_pos.mpr hn1
  have hb : 0 < Real.sqrt (n + 2) := Real.sqrt_pos.mpr hn2
  have hab : Real.sqrt (n + 1) ≤ Real.sqrt (n + 2) := by
    apply Real.sqrt_le_sqrt; linarith
  have : 2 / Real.sqrt (n + 2) ≤ 2 / Real.sqrt (n + 1) :=
    div_le_div_of_nonneg_left (by norm_num) ha hab
  linarith

/-- Partial sum of the telescoping series. -/
lemma telescoping_sum (N : ℕ) :
    ∑ k ∈ Finset.range N,
      (2 / Real.sqrt ((k : ℝ) + 1) - 2 / Real.sqrt ((k : ℝ) + 2)) =
    2 - 2 / Real.sqrt ((N : ℝ) + 1) := by
  induction N with
  | zero =>
    simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have h : ((N + 1 : ℕ) : ℝ) + 1 = (N : ℝ) + 2 := by push_cast; ring
    rw [h]
    ring

/-- `HasSum` for the telescoping series: it sums to `2`. -/
lemma hasSum_diff :
    HasSum (fun n : ℕ => 2 / Real.sqrt ((n : ℝ) + 1) - 2 / Real.sqrt ((n : ℝ) + 2)) 2 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg diff_nonneg]
  -- Show partial sums tend to 2.
  simp_rw [telescoping_sum]
  -- Need: Tendsto (fun N => 2 - 2/√(N+1)) atTop (𝓝 2).
  have : Filter.Tendsto (fun N : ℕ => 2 / Real.sqrt ((N : ℝ) + 1))
      Filter.atTop (nhds 0) := by
    -- 2/√(N+1) → 0 since √(N+1) → ∞.
    have hsqrt : Filter.Tendsto (fun N : ℕ => Real.sqrt ((N : ℝ) + 1))
        Filter.atTop Filter.atTop := by
      apply Filter.Tendsto.comp Real.tendsto_sqrt_atTop
      exact Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hinv := hsqrt.inv_tendsto_atTop
    have h2 : Filter.Tendsto (fun N : ℕ => 2 * (Real.sqrt ((N : ℝ) + 1))⁻¹)
        Filter.atTop (nhds (2 * 0)) :=
      hinv.const_mul 2
    rw [mul_zero] at h2
    refine h2.congr (fun N => ?_)
    rw [div_eq_mul_inv]
  -- 2 - 2/√(N+1) → 2 - 0 = 2
  have h : Filter.Tendsto
      (fun N : ℕ => (2 : ℝ) - 2 / Real.sqrt ((N : ℝ) + 1))
      Filter.atTop (nhds (2 - 0)) :=
    tendsto_const_nhds.sub this
  simp only [sub_zero] at h
  exact h

/-- Summability of the difference series. -/
lemma summable_diff :
    Summable fun n : ℕ => 2 / Real.sqrt ((n : ℝ) + 1) - 2 / Real.sqrt ((n : ℝ) + 2) :=
  hasSum_diff.summable

/-- The tsum of the telescoping series equals 2. -/
lemma tsum_diff :
    ∑' n : ℕ, (2 / Real.sqrt ((n : ℝ) + 1) - 2 / Real.sqrt ((n : ℝ) + 2)) = 2 :=
  hasSum_diff.tsum_eq

snip end

problem imc2015_p6 :
    ∑' n : ℕ, 1 / (Real.sqrt ((n : ℝ) + 1) * ((n : ℝ) + 2)) < 2 := by
  have h : ∑' n : ℕ, 1 / (Real.sqrt ((n : ℝ) + 1) * ((n : ℝ) + 2)) <
      ∑' n : ℕ, (2 / Real.sqrt ((n : ℝ) + 1) - 2 / Real.sqrt ((n : ℝ) + 2)) := by
    apply Summable.tsum_lt_tsum_of_nonneg (i := 0) term_nonneg
    · intro n; exact (term_lt_diff n).le
    · exact term_lt_diff 0
    · exact summable_diff
  rw [tsum_diff] at h
  exact h

end Imc2015P6
