/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Competition 2007, Problem 1
(IMC 2007, Day 1, Problem 1)

Let `f` be a polynomial of degree 2 with integer coefficients. Suppose that
`5 ∣ f(k)` for every integer `k`. Prove that all coefficients of `f` are
divisible by `5`.
-/

namespace Imc2007P1

open Polynomial

snip begin

/-
Write `f = a X^2 + b X + c`.
From `5 ∣ f(0) = c`, we get `5 ∣ c`.
From `5 ∣ f(1) = a + b + c`, subtracting `5 ∣ c` gives `5 ∣ a + b`.
From `5 ∣ f(-1) = a - b + c`, subtracting `5 ∣ c` gives `5 ∣ a - b`.
Adding and subtracting, `5 ∣ 2a` and `5 ∣ 2b`, and since `gcd(2, 5) = 1`,
we get `5 ∣ a` and `5 ∣ b`.
-/

snip end

problem imc2007_p1 (f : ℤ[X]) (hdeg : f.natDegree = 2)
    (hdvd : ∀ k : ℤ, (5 : ℤ) ∣ f.eval k) :
    ∀ i, (5 : ℤ) ∣ f.coeff i := by
  -- Evaluate f at 0, 1, -1 to extract congruences on the coefficients.
  have eval_form : ∀ k : ℤ,
      f.eval k = f.coeff 2 * k ^ 2 + f.coeff 1 * k + f.coeff 0 := by
    intro k
    rw [Polynomial.eval_eq_sum_range, hdeg]
    simp [Finset.sum_range_succ, pow_succ]
    ring
  have h0 := hdvd 0
  have h1 := hdvd 1
  have hm1 := hdvd (-1)
  rw [eval_form 0] at h0
  rw [eval_form 1] at h1
  rw [eval_form (-1)] at hm1
  simp at h0 h1 hm1
  -- h0 : 5 ∣ f.coeff 0
  -- h1 : 5 ∣ f.coeff 2 + f.coeff 1 + f.coeff 0
  -- hm1 : 5 ∣ f.coeff 2 - f.coeff 1 + f.coeff 0
  have hc0 : (5 : ℤ) ∣ f.coeff 0 := h0
  -- Subtract h0 from h1 and hm1.
  have hab : (5 : ℤ) ∣ (f.coeff 2 + f.coeff 1) := by
    have : f.coeff 2 + f.coeff 1 + f.coeff 0 - f.coeff 0 = f.coeff 2 + f.coeff 1 := by ring
    have hsub : (5 : ℤ) ∣ (f.coeff 2 + f.coeff 1 + f.coeff 0 - f.coeff 0) := dvd_sub h1 hc0
    rwa [this] at hsub
  have hamb : (5 : ℤ) ∣ (f.coeff 2 - f.coeff 1) := by
    have hc0' : (5 : ℤ) ∣ f.coeff 0 := h0
    have heq : f.coeff 2 - f.coeff 1 + f.coeff 0 - f.coeff 0 = f.coeff 2 - f.coeff 1 := by ring
    have hsub : (5 : ℤ) ∣ (f.coeff 2 - f.coeff 1 + f.coeff 0 - f.coeff 0) := dvd_sub hm1 hc0'
    rwa [heq] at hsub
  -- Adding: 5 ∣ 2 * f.coeff 2.
  have h2a : (5 : ℤ) ∣ (2 * f.coeff 2) := by
    have hadd : (5 : ℤ) ∣ ((f.coeff 2 + f.coeff 1) + (f.coeff 2 - f.coeff 1)) :=
      dvd_add hab hamb
    have : (f.coeff 2 + f.coeff 1) + (f.coeff 2 - f.coeff 1) = 2 * f.coeff 2 := by ring
    rwa [this] at hadd
  -- Subtracting: 5 ∣ 2 * f.coeff 1.
  have h2b : (5 : ℤ) ∣ (2 * f.coeff 1) := by
    have hsub : (5 : ℤ) ∣ ((f.coeff 2 + f.coeff 1) - (f.coeff 2 - f.coeff 1)) :=
      dvd_sub hab hamb
    have : (f.coeff 2 + f.coeff 1) - (f.coeff 2 - f.coeff 1) = 2 * f.coeff 1 := by ring
    rwa [this] at hsub
  -- Since gcd(2, 5) = 1, conclude 5 ∣ f.coeff 2 and 5 ∣ f.coeff 1.
  have hca : (5 : ℤ) ∣ f.coeff 2 := by
    have h5cop : IsCoprime (5 : ℤ) 2 := by decide
    exact h5cop.dvd_of_dvd_mul_left h2a
  have hcb : (5 : ℤ) ∣ f.coeff 1 := by
    have h5cop : IsCoprime (5 : ℤ) 2 := by decide
    exact h5cop.dvd_of_dvd_mul_left h2b
  -- Now conclude for all i.
  intro i
  match i with
  | 0 => exact hc0
  | 1 => exact hcb
  | 2 => exact hca
  | (n + 3) =>
    -- natDegree = 2, so coefficient at n + 3 is 0.
    have : f.coeff (n + 3) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      omega
    rw [this]
    exact dvd_zero _

end Imc2007P1
