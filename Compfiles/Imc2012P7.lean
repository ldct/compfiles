/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2012, Problem 7 (Day 2, Problem 2)

Define the sequence `a₀, a₁, …` inductively by `a₀ = 1`, `a₁ = 1/2` and
`aₙ₊₁ = n · aₙ² / (1 + (n+1) · aₙ)` for `n ≥ 1`.
Show that the series `∑_{k=0}^∞ a_{k+1} / a_k` converges and determine its value.

Answer: the sum equals `1`.
-/

namespace Imc2012P7

/-- The sequence `a₀ = 1`, `a₁ = 1/2`, `aₙ₊₁ = n·aₙ²/(1+(n+1)aₙ)` for `n ≥ 1`. -/
noncomputable def a : ℕ → ℝ
  | 0 => 1
  | 1 => 1 / 2
  | (n + 2) => (n + 1) * (a (n + 1))^2 / (1 + (n + 2) * a (n + 1))

determine answer : ℝ := 1

-- snip begin

lemma a_zero : a 0 = 1 := rfl
lemma a_one : a 1 = 1 / 2 := rfl

lemma a_succ_succ (n : ℕ) :
    a (n + 2) = (n + 1) * (a (n + 1))^2 / (1 + (n + 2) * a (n + 1)) := rfl

/-- Each term of the sequence is positive. -/
lemma a_pos : ∀ n, 0 < a n
  | 0 => by rw [a_zero]; norm_num
  | 1 => by rw [a_one]; norm_num
  | (n + 2) => by
    rw [a_succ_succ]
    have hpos := a_pos (n + 1)
    have hnum : 0 < (n + 1 : ℝ) * (a (n + 1))^2 := by positivity
    have hden : 0 < 1 + (n + 2 : ℝ) * a (n + 1) := by positivity
    exact div_pos hnum hden

/-- The key identity: for `k ≥ 1`, `a_{k+1}/a_k = k·a_k - (k+1)·a_{k+1}`. -/
lemma key_identity (k : ℕ) :
    a (k + 2) / a (k + 1) = (k + 1) * a (k + 1) - (k + 2) * a (k + 2) := by
  have hpos : 0 < a (k + 1) := a_pos (k + 1)
  have hne : a (k + 1) ≠ 0 := hpos.ne'
  have hden : 0 < 1 + (k + 2 : ℝ) * a (k + 1) := by positivity
  have hden_ne : 1 + (k + 2 : ℝ) * a (k + 1) ≠ 0 := hden.ne'
  rw [a_succ_succ]
  field_simp
  ring

/-- The partial sum identity: for `n ≥ 0`,
`∑_{k=0}^n a_{k+1}/a_k = 1 - (n+1)·a_{n+1}`. -/
lemma partial_sum_eq (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), a (k + 1) / a k =
      1 - (n + 1) * a (n + 1) := by
  induction n with
  | zero =>
    simp [a_zero, a_one]
    norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    -- need: 1 - (m+1)·a(m+1) + a(m+2)/a(m+1) = 1 - (m+2)·a(m+2)
    have hk := key_identity m
    push_cast
    linarith [hk]

/-- Each term `a_{k+1}/a_k` is positive. -/
lemma term_pos (k : ℕ) : 0 < a (k + 1) / a k :=
  div_pos (a_pos _) (a_pos _)

/-- From the partial sum identity, `(n+1)·a(n+1)` is in `(0, 1)`. -/
lemma mul_a_lt_one (n : ℕ) : (n + 1 : ℝ) * a (n + 1) < 1 := by
  have hs := partial_sum_eq n
  have hpos : 0 < ∑ k ∈ Finset.range (n + 1), a (k + 1) / a k := by
    apply Finset.sum_pos
    · intros k _; exact term_pos k
    · exact ⟨0, Finset.mem_range.mpr (by omega)⟩
  linarith

lemma mul_a_nonneg (n : ℕ) : 0 ≤ (n + 1 : ℝ) * a (n + 1) := by
  have h1 : (0 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.zero_le _
  have h2 : 0 ≤ a (n + 1) := (a_pos (n + 1)).le
  positivity

/-- The inequality `2 * (m + 1) ≤ 2^(m+1)` for all natural `m`. -/
lemma two_mul_succ_le_pow (m : ℕ) : 2 * (m + 1 : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by
  induction m with
  | zero => norm_num
  | succ k ihk =>
    have hk2 : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
      have hle : (1 : ℝ) ≤ 2 := by norm_num
      calc (1 : ℝ) = 1 ^ (k + 1) := (one_pow _).symm
        _ ≤ 2 ^ (k + 1) := pow_le_pow_left₀ (by norm_num) hle _
    have hgoal : 2 * (↑(k + 1) + 1 : ℝ) ≤ (2 : ℝ) ^ (k + 1 + 1) := by
      have h1 : 2 * (↑(k + 1) + 1 : ℝ) = 2 * (↑k + 1) + 2 := by push_cast; ring
      have h2 : (2 : ℝ) ^ (k + 1 + 1) = 2 * (2 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
      rw [h1, h2]
      linarith
    exact hgoal

/-- The bound `a n ≤ 1 / 2^n`. We prove this by strong induction. -/
lemma a_le_pow (n : ℕ) : a n ≤ 1 / 2 ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [a_zero]; norm_num
    | 1 => rw [a_one]; norm_num
    | (m + 2) =>
      rw [a_succ_succ]
      have hm_ih : a (m + 1) ≤ 1 / 2 ^ (m + 1) := ih (m + 1) (by omega)
      have hm_pos : 0 < a (m + 1) := a_pos (m + 1)
      have hden_pos : 0 < 1 + (m + 2 : ℝ) * a (m + 1) := by positivity
      -- First bound: a (m+2) ≤ (m+1) * (a (m+1))^2 since denominator ≥ 1
      have h1 : (m + 1 : ℝ) * (a (m + 1))^2 / (1 + (m + 2 : ℝ) * a (m + 1))
                  ≤ (m + 1 : ℝ) * (a (m + 1))^2 := by
        rw [div_le_iff₀ hden_pos]
        have hmp : 0 ≤ (m + 1 : ℝ) * (a (m + 1))^2 := by positivity
        have : (1 : ℝ) ≤ 1 + (m + 2 : ℝ) * a (m + 1) := by
          have : 0 ≤ (m + 2 : ℝ) * a (m + 1) := by positivity
          linarith
        calc (m + 1 : ℝ) * (a (m + 1))^2
            = (m + 1 : ℝ) * (a (m + 1))^2 * 1 := by ring
          _ ≤ (m + 1 : ℝ) * (a (m + 1))^2 * (1 + (m + 2 : ℝ) * a (m + 1)) :=
              mul_le_mul_of_nonneg_left this hmp
      -- Second: (m+1) * (a (m+1))^2 ≤ (m+1) / 4^(m+1)
      have h2 : (m + 1 : ℝ) * (a (m + 1))^2 ≤ (m + 1 : ℝ) / 4 ^ (m + 1) := by
        have hsq : (a (m + 1))^2 ≤ (1 / 2 ^ (m + 1))^2 := by
          apply sq_le_sq'
          · have : 0 ≤ (1 / 2 ^ (m + 1) : ℝ) := by positivity
            linarith [hm_pos]
          · exact hm_ih
        have : (1 / 2 ^ (m + 1) : ℝ)^2 = 1 / 4 ^ (m + 1) := by
          rw [div_pow, one_pow, ← pow_mul, show (4 : ℝ) = 2^2 from by norm_num,
              ← pow_mul, mul_comm 2 (m+1)]
        rw [this] at hsq
        have hnn : (0 : ℝ) ≤ (m + 1 : ℝ) := by positivity
        calc (m + 1 : ℝ) * (a (m + 1))^2
            ≤ (m + 1 : ℝ) * (1 / 4 ^ (m + 1)) := by
              apply mul_le_mul_of_nonneg_left hsq hnn
          _ = (m + 1 : ℝ) / 4 ^ (m + 1) := by ring
      -- Third: (m+1) / 4^(m+1) ≤ 1 / 2^(m+2), i.e., 2*(m+1) * 2^(m+1) ≤ 4^(m+1)
      have h3 : (m + 1 : ℝ) / 4 ^ (m + 1) ≤ 1 / 2 ^ (m + 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        -- (m+1) * 2^(m+2) ≤ 1 * 4^(m+1)
        rw [one_mul]
        -- 4^(m+1) = 2^(m+1) * 2^(m+1), 2^(m+2) = 2 * 2^(m+1)
        have h4 : (4 : ℝ) ^ (m + 1) = (2 : ℝ) ^ (m + 1) * (2 : ℝ) ^ (m + 1) := by
          rw [show (4 : ℝ) = 2 * 2 from by norm_num, mul_pow]
        have h2p : (2 : ℝ) ^ (m + 2) = 2 * (2 : ℝ) ^ (m + 1) := by
          rw [pow_succ]; ring
        rw [h4, h2p]
        -- (m+1) * (2 * 2^(m+1)) ≤ 2^(m+1) * 2^(m+1)
        -- factor out 2^(m+1): 2 * (m+1) ≤ 2^(m+1)
        have hkey : 2 * (m + 1 : ℝ) ≤ (2 : ℝ) ^ (m + 1) := two_mul_succ_le_pow m
        have hpp : (0 : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by positivity
        calc (m + 1 : ℝ) * (2 * (2 : ℝ) ^ (m + 1))
            = (2 * (m + 1 : ℝ)) * (2 : ℝ) ^ (m + 1) := by ring
          _ ≤ (2 : ℝ) ^ (m + 1) * (2 : ℝ) ^ (m + 1) :=
              mul_le_mul_of_nonneg_right hkey hpp
      linarith

/-- `(n+1) * a(n+1) → 0`. -/
lemma mul_a_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => (n + 1 : ℝ) * a (n + 1)) Filter.atTop (nhds 0) := by
  -- We show 0 ≤ (n+1)·a(n+1) ≤ (n+1)/2^(n+1), and the RHS → 0.
  have hsq : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℝ)) / 2 ^ (n + 1)) Filter.atTop (nhds 0) := by
    -- Standard: n / 2^n → 0. Shift the index by one.
    have h : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 1 / 2 ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)
    have h' : Filter.Tendsto (fun n : ℕ => (n : ℝ) / 2 ^ n) Filter.atTop (nhds 0) := by
      convert h using 1; funext n; rw [pow_one]
    have := h'.comp (Filter.tendsto_add_atTop_nat 1)
    convert this using 1
    funext n
    simp
  apply squeeze_zero (fun n => mul_a_nonneg n) _ hsq
  intro n
  -- Need: (n+1) * a (n+1) ≤ (n+1) / 2^(n+1)
  have hbound : a (n + 1) ≤ 1 / 2 ^ (n + 1) := a_le_pow (n + 1)
  have hnn : (0 : ℝ) ≤ (n + 1 : ℝ) := by positivity
  calc (n + 1 : ℝ) * a (n + 1)
      ≤ (n + 1 : ℝ) * (1 / 2 ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left hbound hnn
    _ = (n + 1 : ℝ) / 2 ^ (n + 1) := by ring

-- snip end

problem imc2012_p7 :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), a (k + 1) / a k)
      Filter.atTop (nhds L) ∧ L = answer := by
  refine ⟨1, ?_, rfl⟩
  have hP : (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), a (k + 1) / a k) =
            (fun n : ℕ => 1 - (n + 1) * a (n + 1)) := by
    funext n; exact partial_sum_eq n
  rw [hP]
  have : Filter.Tendsto (fun n : ℕ => (1 : ℝ) - (n + 1) * a (n + 1))
      Filter.atTop (nhds (1 - 0)) := by
    apply Filter.Tendsto.sub tendsto_const_nhds mul_a_tendsto_zero
  simpa using this

end Imc2012P7
