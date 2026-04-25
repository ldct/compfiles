/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2016, Problem 6

Let `(x₁, x₂, …)` be a sequence of positive real numbers satisfying
`∑_{n=1}^∞ x_n / (2n - 1) = 1`.  Prove that
`∑_{k=1}^∞ ∑_{n=1}^k x_n / k² ≤ 2`.

We index `x` from `0`, so original `x_n` becomes our `x (n-1)`; thus the
hypothesis becomes `∑' n, x n / (2n+1) = 1` and the goal becomes
`∑' k, ∑ n ∈ range (k+1), x n / (k+1)² ≤ 2`.
-/

namespace Imc2016P6

open Finset

snip begin

/-- For natural `k`, `1 / (k+1)^2 ≤ 1/(k + 1/2) - 1/(k + 3/2)`. -/
lemma inv_sq_le_diff (k : ℕ) :
    (1 : ℝ) / ((k : ℝ) + 1)^2 ≤ 1/((k : ℝ) + 1/2) - 1/((k : ℝ) + 3/2) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1/2 := by positivity
  have hk' : (0 : ℝ) < (k : ℝ) + 3/2 := by positivity
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hdiff : 1/((k : ℝ) + 1/2) - 1/((k : ℝ) + 3/2)
              = 1/(((k : ℝ) + 1/2) * ((k : ℝ) + 3/2)) := by
    field_simp
    ring
  rw [hdiff]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg ((k : ℝ) + 1)]

/-- Telescoping: `∑_{k ∈ Ico n N} (1/(k+1/2) - 1/(k+3/2)) ≤ 1/(n+1/2)`. -/
lemma sum_telescope_le (n N : ℕ) :
    ∑ k ∈ Ico n N, (1/((k : ℝ) + 1/2) - 1/((k : ℝ) + 3/2))
      ≤ 1/((n : ℝ) + 1/2) := by
  by_cases h : n ≤ N
  · have heq : ∑ k ∈ Ico n N, (1/((k : ℝ) + 1/2) - 1/((k : ℝ) + 3/2))
          = 1/((n : ℝ) + 1/2) - 1/((N : ℝ) + 1/2) := by
      induction N, h using Nat.le_induction with
      | base => simp
      | succ N hN ih =>
        rw [Finset.sum_Ico_succ_top hN, ih]
        have hN' : ((N : ℝ) + 3/2) = ((N + 1 : ℕ) : ℝ) + 1/2 := by push_cast; ring
        rw [hN']
        ring
    rw [heq]
    have hNpos : (0 : ℝ) < (N : ℝ) + 1/2 := by positivity
    have : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1/2) := le_of_lt (one_div_pos.mpr hNpos)
    linarith
  · have hNlt : N < n := lt_of_not_ge h
    rw [Finset.Ico_eq_empty_of_le hNlt.le, Finset.sum_empty]
    have hpos : (0 : ℝ) < (n : ℝ) + 1/2 := by positivity
    have : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1/2) := le_of_lt (one_div_pos.mpr hpos)
    linarith

/-- Swap order of summation for the partial double sum. -/
lemma double_sum_swap (x : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ range N, ∑ n ∈ range (k+1), x n / ((k : ℝ) + 1)^2
      = ∑ n ∈ range N, x n * ∑ k ∈ Ico n N, 1/((k : ℝ) + 1)^2 := by
  have hcomm :
      ∑ k ∈ range N, ∑ n ∈ range (k+1), x n / ((k : ℝ) + 1)^2
        = ∑ n ∈ range N, ∑ k ∈ Ico n N, x n / ((k : ℝ) + 1)^2 := by
    apply Finset.sum_comm' (s := range N) (t := fun k => range (k+1))
        (t' := range N) (s' := fun n => Ico n N)
    intro k n
    simp only [mem_range, mem_Ico]
    omega
  rw [hcomm]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_one_div]

/-- Bound on the partial double sum. -/
lemma partial_double_sum_bound (x : ℕ → ℝ) (hx_nn : ∀ n, 0 ≤ x n) (N : ℕ) :
    ∑ k ∈ range N, (∑ n ∈ range (k+1), x n) / ((k : ℝ) + 1)^2
      ≤ ∑ n ∈ range N, x n * (1/((n : ℝ) + 1/2)) := by
  have hrw1 : ∀ k, (∑ n ∈ range (k+1), x n) / ((k : ℝ) + 1)^2
              = ∑ n ∈ range (k+1), x n / ((k : ℝ) + 1)^2 := by
    intro k; rw [sum_div]
  simp_rw [hrw1]
  rw [double_sum_swap x N]
  apply Finset.sum_le_sum
  intro n _
  have hbound :
      ∑ k ∈ Ico n N, 1/((k : ℝ) + 1)^2 ≤ 1/((n : ℝ) + 1/2) := by
    calc ∑ k ∈ Ico n N, 1/((k : ℝ) + 1)^2
        ≤ ∑ k ∈ Ico n N, (1/((k : ℝ) + 1/2) - 1/((k : ℝ) + 3/2)) := by
          apply Finset.sum_le_sum
          intro k _
          exact inv_sq_le_diff k
      _ ≤ 1/((n : ℝ) + 1/2) := sum_telescope_le n N
  exact mul_le_mul_of_nonneg_left hbound (hx_nn n)

snip end

problem imc2016_p6 (x : ℕ → ℝ) (hx_pos : ∀ n, 0 < x n)
    (hx_sum : ∑' n : ℕ, x n / (2 * (n : ℝ) + 1) = 1) :
    ∑' k : ℕ, (∑ n ∈ range (k+1), x n) / ((k : ℝ) + 1)^2 ≤ 2 := by
  have hx_nn : ∀ n, 0 ≤ x n := fun n => (hx_pos n).le
  have hterm_nn : ∀ k, 0 ≤ (∑ n ∈ range (k+1), x n) / ((k : ℝ) + 1)^2 := by
    intro k
    apply div_nonneg
    · exact Finset.sum_nonneg (fun n _ => hx_nn n)
    · positivity
  have hxterm_nn : ∀ n, 0 ≤ x n / (2 * (n : ℝ) + 1) := by
    intro n
    apply div_nonneg (hx_nn n)
    positivity
  -- Summability of `x n / (2n+1)`: if not summable, tsum would be 0 ≠ 1.
  have hsumm : Summable (fun n => x n / (2 * (n : ℝ) + 1)) := by
    by_contra hns
    rw [tsum_eq_zero_of_not_summable hns] at hx_sum
    norm_num at hx_sum
  apply Real.tsum_le_of_sum_range_le hterm_nn
  intro N
  -- Apply partial bound and rewrite the comparison sum.
  have h1 := partial_double_sum_bound x hx_nn N
  have h2 : ∀ n, x n * (1/((n : ℝ) + 1/2)) = 2 * (x n / (2 * (n : ℝ) + 1)) := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1/2 := by positivity
    have hpos2 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
    field_simp
  have hrhs_eq : ∑ n ∈ range N, x n * (1/((n : ℝ) + 1/2))
      = 2 * ∑ n ∈ range N, x n / (2 * (n : ℝ) + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros n _; rw [h2]
  rw [hrhs_eq] at h1
  have hsumx_le : ∑ n ∈ range N, x n / (2 * (n : ℝ) + 1) ≤ 1 := by
    have := hsumm.sum_le_tsum (range N) (fun n _ => hxterm_nn n)
    rw [hx_sum] at this
    exact this
  calc ∑ k ∈ range N, (∑ n ∈ range (k+1), x n) / ((k : ℝ) + 1)^2
      ≤ 2 * ∑ n ∈ range N, x n / (2 * (n : ℝ) + 1) := h1
    _ ≤ 2 * 1 := by
        apply mul_le_mul_of_nonneg_left hsumx_le
        norm_num
    _ = 2 := by norm_num

end Imc2016P6
