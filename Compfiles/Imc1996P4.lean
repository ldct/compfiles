/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1996, Problem 4 (Day 1)

Let `a₁ = 1` and, for `n ≥ 2`,
`a_n = (1/n) · Σ_{k=1}^{n-1} a_k · a_{n-k}`.

Show
(i) `limsup_{n → ∞} |a_n|^{1/n} < 2^{-1/2}`;
(ii) `limsup_{n → ∞} |a_n|^{1/n} ≥ 2/3`.

## Proof outline (official solution)

By induction `a_n > 0` for all `n ≥ 1`, so `|a_n| = a_n`.

(i) Choose `q = 7/10 < 1/√2 = 0.7071…`. Compute
    `a_2 = 1/2`, `a_3 = 1/3`, `a_4 = 11/48`. Verify `a_n ≤ q^n` for `n = 3, 4`.
    For `N ≥ 5`, assuming `a_n ≤ q^n` for `3 ≤ n ≤ N-1` and `a_1 = 1`, `a_2 = 1/2`:
    Split the recurrence
    `a_N = (1/N) Σ_{k=1}^{N-1} a_k a_{N-k}`
    by extracting the boundary terms. Since `a_1 = 1` and `a_2 = 1/2`,
    `(1/N)(a_1 a_{N-1} + a_{N-1} a_1) = (2/N) a_{N-1}`
    and `(1/N)(a_2 a_{N-2} + a_{N-2} a_2) = (1/N) a_{N-2}`. Hence
    `a_N = (2/N) a_{N-1} + (1/N) a_{N-2} + (1/N) Σ_{k=3}^{N-3} a_k a_{N-k}`
        ≤ (2/N) q^{N-1} + (1/N) q^{N-2} + ((N-5)/N) q^N
        = (q^N / N) · (2/q + 1/q^2 + (N-5))
        ≤ q^N
    iff `2/q + 1/q^2 ≤ 5`, i.e. `2q + 1 ≤ 5 q^2`. With `q = 7/10`,
    `5 q^2 = 245/100 = 2.45` and `2q + 1 = 2.4 < 2.45`. ✓
    Then `a_n^{1/n} ≤ q < 1/√2`, and the limsup is bounded by `q < 1/√2`.

(ii) Choose `q = 2/3`. Compute `a_2 = 1/2 > (2/3)^2 = 4/9`. By induction,
     for `N ≥ 3`,
     `a_N = (2/N) a_{N-1} + (1/N) Σ_{k=2}^{N-2} a_k a_{N-k}`
         ≥ (2/N) q^{N-1} + ((N-3)/N) q^N
         = (q^N / N) (2/q + (N-3)) = q^N · (1/N)(3 + N - 3) = q^N
     since `2/q = 3`. Thus `a_n^{1/n} ≥ q = 2/3` for `n ≥ 2`,
     and so the limsup is at least `2/3`.

## Status

This formalization defines the sequence and states the two limsup
bounds. The full proof — combining the two `q^n` bounds with the
asymptotic `(C^{1/n}) → 1` and `(q^n)^{1/n} = q` — is left as `sorry`
with detailed TODO. Positivity of the sequence and several key
algebraic identities are established as lemmas.
-/

namespace Imc1996P4

open scoped Topology BigOperators

/-- The sequence `a` defined by `a 0 = 0`, `a 1 = 1`, and for `n ≥ 2`:
`a n = (1/n) · Σ_{k=1}^{n-1} a_k · a_{n-k}`. -/
noncomputable def a : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | (n + 2) =>
      (1 / ((n + 2 : ℕ) : ℝ)) *
        ∑ k ∈ (Finset.Ioo 0 (n + 2)).attach,
          a k.val * a ((n + 2) - k.val)
termination_by n => n
decreasing_by
  all_goals
    have hk := (Finset.mem_Ioo.mp k.2)
    omega

snip begin

/-- `a 0 = 0`. -/
@[simp] lemma a_zero : a 0 = 0 := by unfold a; rfl

/-- `a 1 = 1`. -/
@[simp] lemma a_one : a 1 = 1 := by unfold a; rfl

/-- Recurrence for `n + 2 ≥ 2`. -/
lemma a_succ_succ (n : ℕ) :
    a (n + 2) = (1 / ((n + 2 : ℕ) : ℝ)) *
      ∑ k ∈ Finset.Ioo 0 (n + 2), a k * a ((n + 2) - k) := by
  conv_lhs => unfold a
  rw [Finset.sum_attach (Finset.Ioo 0 (n + 2)) (fun k => a k * a ((n + 2) - k))]

/-- `a 2 = 1/2`. -/
lemma a_two : a 2 = 1 / 2 := by
  show a (0 + 2) = 1 / 2
  rw [a_succ_succ]
  -- ∑ k ∈ Ioo 0 2 = {1}; a 1 * a 1 = 1
  have : Finset.Ioo 0 2 = {1} := by decide
  simp [this]

/-- `a 3 = 1/3`. -/
lemma a_three : a 3 = 1 / 3 := by
  show a (1 + 2) = 1 / 3
  rw [a_succ_succ]
  have hset : Finset.Ioo 0 3 = {1, 2} := by decide
  rw [hset]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [a_one, a_two]
  norm_num

/-- For `n ≥ 1`, `a n > 0`. We prove by strong induction. -/
lemma a_pos : ∀ n, 1 ≤ n → 0 < a n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, hn with
    | 1, _ => simp [a_one]
    | (k + 2), _ =>
      rw [a_succ_succ]
      apply mul_pos
      · positivity
      · -- Sum of positive terms
        apply Finset.sum_pos
        · intro i hi
          rw [Finset.mem_Ioo] at hi
          obtain ⟨hi1, hi2⟩ := hi
          have hipos : 1 ≤ i := hi1
          have hiup : i < k + 2 := hi2
          have hki : 1 ≤ (k + 2) - i := by omega
          have hki' : (k + 2) - i < k + 2 := by omega
          have h1 : 0 < a i := ih i hiup hipos
          have h2 : 0 < a ((k + 2) - i) := ih ((k + 2) - i) hki' hki
          exact mul_pos h1 h2
        · -- Nonempty
          refine ⟨1, ?_⟩
          rw [Finset.mem_Ioo]
          exact ⟨by omega, by omega⟩

/-- `|a n| = a n` for `n ≥ 1`. -/
lemma abs_a (n : ℕ) (hn : 1 ≤ n) : |a n| = a n :=
  abs_of_pos (a_pos n hn)

/-- Algebraic verification that `2/q + 1/q² ≤ 5` for `q = 7/10`,
equivalently `2q + 1 ≤ 5q²`. -/
lemma key_ineq_part_i : (2 : ℝ) * (7/10) + 1 ≤ 5 * (7/10)^2 := by norm_num

/-- `(7/10 : ℝ) < 2^{-1/2} = 1/√2`. Equivalently, `(7/10)^2 < 1/2`,
i.e. `49/100 < 50/100`. -/
lemma seven_tenths_lt_inv_sqrt_two : (7 / 10 : ℝ) < (2 : ℝ) ^ (-(1/2 : ℝ)) := by
  have h1 : (0 : ℝ) < (2 : ℝ) ^ (-(1/2 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  -- (2 ^ (-1/2))^2 = 2 ^ (-1) = 1/2.
  have h2 : ((2 : ℝ) ^ (-(1/2 : ℝ))) ^ 2 = 1 / 2 := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(1/2 : ℝ))) 2, ← Real.rpow_mul (by norm_num)]
    norm_num
  -- Compare squares: (7/10)^2 = 49/100 < 50/100 = 1/2.
  have hsq : (7/10 : ℝ)^2 < ((2 : ℝ) ^ (-(1/2 : ℝ)))^2 := by
    rw [h2]; norm_num
  have h3 : (0 : ℝ) ≤ 7/10 := by norm_num
  exact lt_of_pow_lt_pow_left₀ 2 h1.le hsq

snip end

/-- The first part: `limsup |a n|^{1/n} < 2^{-1/2}`. -/
problem imc1996_p4_part_i :
    Filter.limsup (fun n : ℕ => |a n| ^ ((1 : ℝ) / n)) Filter.atTop
      < (2 : ℝ) ^ (-(1/2 : ℝ)) := by
  -- TODO: full formalization. Outline:
  --
  -- Step 1. Prove `a n ≤ (7/10)^n` for `n ≥ 3` by strong induction
  --   (base cases `n = 3, 4` from `a_three` and the explicit value
  --   `a_4 = 11/48 ≈ 0.229 < (7/10)^4 = 0.2401`; inductive step using
  --   the splitting
  --   `a_N = (2/N) a_{N-1} + (1/N) a_{N-2} + (1/N) Σ_{k=3}^{N-3} a_k a_{N-k}`
  --   together with `a_k ≤ (7/10)^k` for `k = N-1, N-2` and for `3 ≤ k ≤ N-3`,
  --   and using `key_ineq_part_i`).
  --
  -- Step 2. Then `|a n|^{1/n} = (a n)^{1/n} ≤ ((7/10)^n)^{1/n} = 7/10`
  --   for `n ≥ 3`, so the limsup is `≤ 7/10 < 2^{-1/2}`
  --   (using `seven_tenths_lt_inv_sqrt_two`).
  sorry

/-- The second part: `limsup |a n|^{1/n} ≥ 2/3`. -/
problem imc1996_p4_part_ii :
    Filter.limsup (fun n : ℕ => |a n| ^ ((1 : ℝ) / n)) Filter.atTop
      ≥ (2 / 3 : ℝ) := by
  -- TODO: full formalization. Outline:
  --
  -- Step 1. Prove `a n ≥ (2/3)^n` for `n ≥ 2` by strong induction.
  --   Base case `n = 2`: `a 2 = 1/2 > 4/9 = (2/3)^2`.
  --   Inductive step for `N ≥ 3`:
  --   `a_N = (2/N) a_{N-1} + (1/N) Σ_{k=2}^{N-2} a_k a_{N-k}`
  --       ≥ (2/N)(2/3)^{N-1} + ((N-3)/N)(2/3)^N
  --       = (2/3)^N · (1/N) · (2 · (3/2) + (N-3)) = (2/3)^N.
  --
  -- Step 2. Then `|a n|^{1/n} ≥ ((2/3)^n)^{1/n} = 2/3` eventually,
  --   so the limsup is `≥ 2/3`.
  sorry

end Imc1996P4
