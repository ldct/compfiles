/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2015, Problem 3

Let `F(0) = 0`, `F(1) = 3/2`, and `F(n) = (5/2) F(n-1) - F(n-2)` for `n ≥ 2`.
Determine whether or not `∑_{n=0}^∞ 1/F(2^n)` is a rational number.

Answer: it is rational. In fact, the sum equals `1`.

The characteristic polynomial `x^2 - (5/2)x + 1 = 0` has roots `2` and `1/2`,
so `F(n) = 2^n - 2^{-n}`. Then
`1/F(2^n) = 2^{2^n} / (2^{2·2^n} - 1) = 1/(2^{2^n} - 1) - 1/(2^{2^{n+1}} - 1)`,
a telescoping series summing to `1/(2^{2^0} - 1) = 1`.
-/

namespace Imc2015P3

open Topology Filter

noncomputable def F : ℕ → ℝ
  | 0 => 0
  | 1 => 3 / 2
  | n + 2 => (5 / 2) * F (n + 1) - F n

determine answer : Prop := ∃ q : ℚ, HasSum (fun n : ℕ => 1 / F (2 ^ n)) (q : ℝ)

-- snip begin

/-- Closed form for `F`: `F n = 2^n - (1/2)^n`. -/
lemma F_eq (n : ℕ) : F n = (2 : ℝ) ^ n - (1 / 2) ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [F]
    | 1 => show (3 : ℝ) / 2 = 2 ^ 1 - (1 / 2) ^ 1; norm_num
    | k + 2 =>
      have h1 : F (k + 1) = (2 : ℝ) ^ (k + 1) - (1 / 2) ^ (k + 1) := ih (k + 1) (by omega)
      have h0 : F k = (2 : ℝ) ^ k - (1 / 2) ^ k := ih k (by omega)
      show (5 / 2) * F (k + 1) - F k = (2 : ℝ) ^ (k + 2) - (1 / 2) ^ (k + 2)
      rw [h1, h0]
      ring

/-- For `m ≥ 1`, `1 < 2^m` over `ℝ`. -/
lemma one_lt_two_pow {m : ℕ} (hm : 1 ≤ m) : (1 : ℝ) < 2 ^ m := by
  calc (1 : ℝ) = 2 ^ 0 := by norm_num
    _ < 2 ^ m := by apply pow_lt_pow_right₀ (by norm_num) (by omega)

/-- `2^n` is a positive natural number. -/
lemma two_pow_pos_nat (n : ℕ) : 1 ≤ 2 ^ n := Nat.one_le_two_pow

/-- The telescoping identity: for `n ≥ 0`,
`1/F(2^n) = 1/(2^{2^n} - 1) - 1/(2^{2^{n+1}} - 1)`. -/
lemma inv_F_telescope (n : ℕ) :
    1 / F (2 ^ n) =
      1 / ((2 : ℝ) ^ (2 ^ n) - 1) - 1 / ((2 : ℝ) ^ (2 ^ (n + 1)) - 1) := by
  rw [F_eq]
  -- Let x = 2^{2^n}, so (1/2)^{2^n} = 1/x and 2^{2^{n+1}} = x^2.
  set x : ℝ := (2 : ℝ) ^ (2 ^ n) with hx_def
  have hx_gt : 1 < x := one_lt_two_pow (two_pow_pos_nat n)
  have hx_pos : 0 < x := by linarith
  have hx_ne : x ≠ 0 := by linarith
  have hxsq_gt : 1 < x ^ 2 := by nlinarith
  have hx_ne1 : x - 1 ≠ 0 := by linarith
  have hxsq_ne1 : x ^ 2 - 1 ≠ 0 := by linarith
  have hhalf : (1 / 2 : ℝ) ^ (2 ^ n) = 1 / x := by
    rw [hx_def, one_div, one_div, ← inv_pow]
  have hpow_succ : (2 : ℝ) ^ (2 ^ (n + 1)) = x ^ 2 := by
    rw [hx_def, ← pow_mul, pow_succ, mul_comm]
  rw [hhalf, hpow_succ]
  -- LHS = 1/(x - 1/x) = x/(x^2 - 1) = (x+1)/(x^2-1) - 1/(x^2-1) = 1/(x-1) - 1/(x^2-1)
  field_simp
  ring

/-- Partial sums telescope. -/
lemma partial_sum_eq (N : ℕ) :
    ∑ n ∈ Finset.range N, 1 / F (2 ^ n) =
      1 / ((2 : ℝ) ^ (2 ^ 0) - 1) - 1 / ((2 : ℝ) ^ (2 ^ N) - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, inv_F_telescope]
    ring

/-- `2^(2^N) → ∞` as `N → ∞` in `ℝ`. -/
lemma tendsto_two_pow_two_pow :
    Filter.Tendsto (fun N : ℕ => (2 : ℝ) ^ (2 ^ N)) Filter.atTop Filter.atTop := by
  have h1 : Filter.Tendsto (fun N : ℕ => 2 ^ N) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2)
  have h2 : Filter.Tendsto (fun k : ℕ => (2 : ℝ) ^ k) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  exact h2.comp h1

/-- `1/(2^{2^N} - 1) → 0`. -/
lemma tendsto_tail_zero :
    Filter.Tendsto (fun N : ℕ => 1 / ((2 : ℝ) ^ (2 ^ N) - 1)) Filter.atTop (𝓝 0) := by
  have h1 : Filter.Tendsto (fun N : ℕ => (2 : ℝ) ^ (2 ^ N) - 1) Filter.atTop Filter.atTop := by
    have h := tendsto_two_pow_two_pow
    have : Filter.Tendsto (fun N : ℕ => (2 : ℝ) ^ (2 ^ N) + (-1)) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ _ h
    exact this.congr (fun N => by ring)
  have h2 := h1.inv_tendsto_atTop
  refine h2.congr ?_
  intro N
  show ((fun M => ((2 : ℝ) ^ (2 ^ M) - 1))⁻¹) N = 1 / ((2 : ℝ) ^ (2 ^ N) - 1)
  rw [Pi.inv_apply, one_div]

/-- Partial sums tend to `1`. -/
lemma tendsto_partial_sum :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, 1 / F (2 ^ n)) Filter.atTop (𝓝 1) := by
  have heq : ∀ N : ℕ, ∑ n ∈ Finset.range N, 1 / F (2 ^ n) =
      1 - 1 / ((2 : ℝ) ^ (2 ^ N) - 1) := by
    intro N
    rw [partial_sum_eq]
    norm_num
  apply Filter.Tendsto.congr (fun N => (heq N).symm)
  have : Filter.Tendsto (fun N : ℕ => (1 : ℝ) - 1 / ((2 : ℝ) ^ (2 ^ N) - 1))
      Filter.atTop (𝓝 (1 - 0)) :=
    Filter.Tendsto.sub tendsto_const_nhds tendsto_tail_zero
  simpa using this

/-- `F(2^n) ≥ 0`. -/
lemma F_two_pow_nonneg (n : ℕ) : 0 ≤ F (2 ^ n) := by
  rw [F_eq]
  have h1 : (1 / 2 : ℝ) ^ (2 ^ n) ≤ 1 := by
    have h0a : (0 : ℝ) ≤ 1 / 2 := by norm_num
    have h0b : (1 / 2 : ℝ) ≤ 1 := by norm_num
    calc (1 / 2 : ℝ) ^ (2 ^ n) ≤ 1 ^ (2 ^ n) := by
            apply pow_le_pow_left₀ h0a h0b
      _ = 1 := one_pow _
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 ^ n) := by
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  linarith

/-- Each term `1/F(2^n)` is nonneg. -/
lemma inv_F_nonneg (n : ℕ) : 0 ≤ 1 / F (2 ^ n) :=
  div_nonneg zero_le_one (F_two_pow_nonneg n)

/-- The series sums to `1`. -/
lemma hasSum_inv_F : HasSum (fun n : ℕ => 1 / F (2 ^ n)) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg inv_F_nonneg]
  exact tendsto_partial_sum

-- snip end

problem imc2015_p3 : answer := ⟨1, by exact_mod_cast hasSum_inv_F⟩

end Imc2015P3
