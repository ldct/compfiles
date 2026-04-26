/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1995, Problem 8 (Day 2 Problem 2)

Let `b₀ = 1` and `bₙ = 2 + √b_{n-1} - 2√(1 + √b_{n-1})`. Compute
`∑_{n=1}^∞ bₙ · 2^n`.

## Answer

The sum equals `2 - 2 log 2`.

## Proof outline (official solution)

Set `aₙ = 1 + √bₙ`, so `a₀ = 2`. Then

  `aₙ = 1 + √(1 + a_{n-1} - 2√a_{n-1}) = 1 + |√a_{n-1} - 1| = √a_{n-1}`,

so `aₙ² = a_{n-1}` and inductively `aₙ = 2^{1/2^n}`. Also `bₙ = (aₙ - 1)²`.

Using `aₙ² = a_{n-1}`, we have

  `bₙ · 2^n = (aₙ - 1)² · 2^n = a_{n-1} · 2^n - aₙ · 2^{n+1} + 2^n`
            ` = (a_{n-1} - 1) · 2^n - (aₙ - 1) · 2^{n+1}`,

a telescoping difference. Hence the partial sums are

  `S_N = (a₀ - 1) · 2 - (a_N - 1) · 2^{N+1} = 2 - 2 · (2^{2^{-N}} - 1) / 2^{-N}`.

As `N → ∞`, with `x = 2^{-N} → 0⁺`, we use `(2^x - 1)/x → log 2`, giving

  `∑_{n=1}^∞ bₙ · 2^n = 2 - 2 log 2`.
-/

namespace Imc1995P8

open Real Filter Topology

/-- The auxiliary sequence `aₙ = 2^{1/2^n}`, defined directly so we can reason
about it without inducting through square roots. -/
private noncomputable def a (n : ℕ) : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 2 ^ n)

private lemma a_zero : a 0 = 2 := by
  simp [a]

private lemma a_pos (n : ℕ) : 0 < a n := by
  unfold a
  exact Real.rpow_pos_of_pos (by norm_num) _

private lemma a_ge_one (n : ℕ) : 1 ≤ a n := by
  unfold a
  apply Real.one_le_rpow (by norm_num)
  positivity

private lemma a_succ_sq (n : ℕ) : a (n + 1) ^ 2 = a n := by
  unfold a
  rw [← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 2 ^ (n+1))) 2,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  push_cast
  rw [pow_succ]
  field_simp

private lemma sqrt_a_succ (n : ℕ) : Real.sqrt (a n) = a (n + 1) := by
  rw [← a_succ_sq n]
  exact Real.sqrt_sq (le_of_lt (a_pos _))

/-- The sequence `bₙ = (aₙ - 1)²` for `n ≥ 1`. -/
private noncomputable def b : ℕ → ℝ
  | 0 => 1
  | n + 1 => (a (n + 1) - 1) ^ 2

private lemma b_zero : b 0 = 1 := rfl

private lemma sqrt_b_zero : Real.sqrt (b 0) = 1 := by
  rw [b_zero, Real.sqrt_one]

private lemma sqrt_b_succ (n : ℕ) : Real.sqrt (b (n + 1)) = a (n + 1) - 1 := by
  unfold b
  rw [Real.sqrt_sq (by linarith [a_ge_one (n + 1)])]

/-- Recursion: `bₙ = 2 + √b_{n-1} - 2√(1 + √b_{n-1})`. -/
private lemma b_recursion (n : ℕ) :
    b (n + 1) = 2 + Real.sqrt (b n) - 2 * Real.sqrt (1 + Real.sqrt (b n)) := by
  have hsqrt_bn : Real.sqrt (b n) = a n - 1 := by
    cases n with
    | zero => rw [sqrt_b_zero, a_zero]; ring
    | succ k => exact sqrt_b_succ k
  have h1 : 1 + Real.sqrt (b n) = a n := by rw [hsqrt_bn]; ring
  have h2 : Real.sqrt (1 + Real.sqrt (b n)) = a (n + 1) := by
    rw [h1, sqrt_a_succ]
  rw [h2, hsqrt_bn]
  show (a (n + 1) - 1) ^ 2 = 2 + (a n - 1) - 2 * a (n + 1)
  have ha2 : a (n + 1) ^ 2 = a n := a_succ_sq n
  nlinarith [ha2]

/-- The crucial telescoping identity:
`bₙ · 2^n = (a_{n-1} - 1) · 2^n - (aₙ - 1) · 2^{n+1}`. -/
private lemma b_telescope (n : ℕ) :
    b (n + 1) * 2 ^ (n + 1) =
      (a n - 1) * 2 ^ (n + 1) - (a (n + 1) - 1) * 2 ^ (n + 2) := by
  show (a (n + 1) - 1) ^ 2 * (2:ℝ) ^ (n + 1) =
      (a n - 1) * 2 ^ (n + 1) - (a (n + 1) - 1) * 2 ^ (n + 2)
  have ha2 : a (n + 1) ^ 2 = a n := a_succ_sq n
  have h2pow : (2 : ℝ) ^ (n + 2) = 2 ^ (n + 1) * 2 := by
    rw [pow_succ]
  rw [h2pow]
  have h2pos : (0:ℝ) < (2:ℝ) ^ (n+1) := by positivity
  nlinarith [ha2, h2pos]

/-- Partial sum formula: telescoping. -/
private lemma partial_sum_eq (N : ℕ) :
    ∑ n ∈ Finset.range N, b (n + 1) * 2 ^ (n + 1) =
      (a 0 - 1) * 2 - (a N - 1) * 2 ^ (N + 1) := by
  induction N with
  | zero =>
    simp [a_zero]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, b_telescope]
    ring

/-- The bridge from `2 - 2 (a N - 1) · 2^N` (where `a N = 2^{2^{-N}}`)
to `2 - 2 log 2`. We show the partial-sum tail tends to `2 log 2`. -/
private lemma tail_tendsto :
    Tendsto (fun N : ℕ => (a N - 1) * 2 ^ (N + 1)) atTop (𝓝 (2 * Real.log 2)) := by
  -- (a N - 1) * 2^{N+1} = 2 * ((2^{1/2^N} - 1) * 2^N) = 2 * ((1/2^N)⁻¹ * (2^{1/2^N} - 1)).
  have hbase : Tendsto (fun p : ℝ => p⁻¹ * ((2 : ℝ) ^ p - 1)) (𝓝[>] 0)
      (𝓝 (Real.log 2)) :=
    tendsto_rpow_sub_one_log (by norm_num : (0:ℝ) < 2)
  -- The map `N ↦ 1 / 2^N` tends to 0 within `(0, ∞)` from atTop.
  have hpsmall : Tendsto (fun N : ℕ => (1 : ℝ) / 2 ^ N) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h1 : Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ N) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have heq : (fun N : ℕ => (1 : ℝ) / 2 ^ N) = (fun N : ℕ => (1 / 2 : ℝ) ^ N) := by
        funext N; rw [div_pow, one_pow]
      rw [heq]; exact h1
    · filter_upwards with N
      simp only [Set.mem_Ioi]
      positivity
  have hcomp := hbase.comp hpsmall
  have htwo : Tendsto (fun N : ℕ => 2 * ((fun p : ℝ => p⁻¹ * ((2 : ℝ) ^ p - 1))
      ((1 : ℝ) / 2 ^ N))) atTop (𝓝 (2 * Real.log 2)) :=
    hcomp.const_mul 2
  -- Show the inner expression equals (a N - 1) * 2^{N+1}.
  convert htwo using 1
  funext N
  unfold a
  -- Goal (after Function.comp simplification): RHS expands to
  --   2 * ((1 / 2^N)⁻¹ * (2^{1/2^N} - 1)).
  show ((2:ℝ) ^ ((1:ℝ) / 2 ^ N) - 1) * 2 ^ (N + 1) =
       2 * ((1 / (2:ℝ) ^ N)⁻¹ * ((2:ℝ) ^ ((1:ℝ) / 2 ^ N) - 1))
  have h2N_pos : (0:ℝ) < (2:ℝ) ^ N := by positivity
  rw [one_div, inv_inv, pow_succ]
  ring

/-- Partial sums tend to `2 - 2 log 2`. -/
private lemma sum_tendsto :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, b (n + 1) * 2 ^ (n + 1))
      atTop (𝓝 (2 - 2 * Real.log 2)) := by
  have heq : ∀ N, ∑ n ∈ Finset.range N, b (n + 1) * 2 ^ (n + 1)
        = (a 0 - 1) * 2 - (a N - 1) * 2 ^ (N + 1) := partial_sum_eq
  simp_rw [heq, a_zero]
  have h := tail_tendsto
  have hgoal : Tendsto (fun N : ℕ => (2 - 1 : ℝ) * 2 - (a N - 1) * 2 ^ (N + 1))
      atTop (𝓝 ((2 - 1) * 2 - 2 * Real.log 2)) :=
    tendsto_const_nhds.sub h
  have htarget : ((2 : ℝ) - 1) * 2 - 2 * Real.log 2 = 2 - 2 * Real.log 2 := by ring
  rw [← htarget]
  exact hgoal

/-- The series `∑ bₙ · 2^n` (starting at `n = 1`) sums to `2 - 2 log 2`. -/
problem imc1995_p8 (b' : ℕ → ℝ) (hb0 : b' 0 = 1)
    (hb : ∀ n, b' (n + 1) = 2 + Real.sqrt (b' n) - 2 * Real.sqrt (1 + Real.sqrt (b' n))) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, b' (n + 1) * 2 ^ (n + 1))
      atTop (𝓝 (2 - 2 * Real.log 2)) := by
  -- Show b' = b on all of ℕ.
  have hbeq : ∀ n, b' n = b n := by
    intro n
    induction n with
    | zero => rw [hb0, b_zero]
    | succ k ih =>
      rw [hb k, b_recursion, ih]
  simp_rw [hbeq]
  exact sum_tendsto

end Imc1995P8
