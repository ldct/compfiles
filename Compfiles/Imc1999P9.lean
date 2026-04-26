/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra, .Inequality] }

/-!
# International Mathematical Competition 1999, Problem 9 (Day 2, Problem 3)

If `x_1, …, x_n ≥ -1` and `∑ x_i^3 = 0`, prove that `∑ x_i ≤ n/3`.

## Solution sketch (official)

For `x ≥ -1`, the polynomial identity
  `(x + 1) (x - 1/2)^2 = x^3 - (3/4) x + 1/4`
yields a nonnegative quantity (product of `x + 1 ≥ 0` and a square).
Summing over `i = 1, …, n`:
  `0 ≤ ∑ x_i^3 - (3/4) ∑ x_i + n/4 = -(3/4) ∑ x_i + n/4`,
since `∑ x_i^3 = 0`. Hence `∑ x_i ≤ n/3`.
-/

namespace Imc1999P9

open scoped BigOperators
open Finset

snip begin

/-- The pointwise inequality: for `x ≥ -1`,
    `(x + 1) (x - 1/2)^2 = x^3 - (3/4) x + 1/4 ≥ 0`. -/
lemma pointwise_ineq (x : ℝ) (hx : -1 ≤ x) :
    x ^ 3 - (3 / 4) * x + 1 / 4 ≥ 0 := by
  have h1 : (0 : ℝ) ≤ x + 1 := by linarith
  have h2 : (0 : ℝ) ≤ (x - 1 / 2) ^ 2 := sq_nonneg _
  have hprod : 0 ≤ (x + 1) * (x - 1 / 2) ^ 2 := mul_nonneg h1 h2
  have hexpand : (x + 1) * (x - 1 / 2) ^ 2 = x ^ 3 - (3 / 4) * x + 1 / 4 := by
    ring
  linarith [hprod, hexpand.symm ▸ hprod]

snip end

problem imc1999_p9 (n : ℕ) (x : Fin n → ℝ)
    (hx : ∀ i, -1 ≤ x i) (hsum : ∑ i, (x i) ^ 3 = 0) :
    ∑ i, x i ≤ n / 3 := by
  -- Sum the pointwise inequality over all `i`.
  have hpt : ∀ i, (x i) ^ 3 - (3 / 4) * x i + 1 / 4 ≥ 0 :=
    fun i => pointwise_ineq (x i) (hx i)
  have hsum_ineq : (0 : ℝ) ≤ ∑ i, ((x i) ^ 3 - (3 / 4) * x i + 1 / 4) :=
    Finset.sum_nonneg (fun i _ => hpt i)
  -- Split the sum.
  have hsplit : ∑ i, ((x i) ^ 3 - (3 / 4) * x i + 1 / 4)
      = (∑ i, (x i) ^ 3) - (3 / 4) * (∑ i, x i) + n / 4 := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [Finset.sum_const, Finset.card_univ]
    ring
  rw [hsplit, hsum] at hsum_ineq
  -- 0 ≤ 0 - (3/4) * S + n/4, so S ≤ n/3.
  linarith
end Imc1999P9
