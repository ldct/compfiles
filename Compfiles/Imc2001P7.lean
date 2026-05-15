/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2001, Problem 7
(IMC 2001, Day 2, Problem 1)

Let `r, s ≥ 1` be integers, and let `a_0, …, a_{r-1}, b_0, …, b_{s-1}` be
nonnegative real numbers satisfying
`(a_0 + a_1 x + ⋯ + a_{r-1} x^{r-1} + x^r)(b_0 + ⋯ + b_{s-1} x^{s-1} + x^s)
  = 1 + x + ⋯ + x^{r+s}`.
Prove that each `a_i` and `b_j` is either `0` or `1`.
-/

namespace Imc2001P7

open Polynomial

/-- The target polynomial `1 + x + ⋯ + x^n`. -/
noncomputable def psi (n : ℕ) : ℝ[X] := ∑ k ∈ Finset.range (n + 1), (X : ℝ[X]) ^ k

snip begin

lemma psi_coeff (n k : ℕ) :
    (psi n).coeff k = if k ≤ n then 1 else 0 := by
  unfold psi
  rw [finset_sum_coeff]
  simp only [coeff_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single k]
    · simp
    · intros i _ hik
      simp [Ne.symm hik]
    · intro hk
      exfalso; apply hk
      rw [Finset.mem_range]; omega
  · apply Finset.sum_eq_zero
    intros i hi
    rw [Finset.mem_range] at hi
    simp only [ite_eq_right_iff]
    intro h'; subst h'; omega

/-- Coefficient of `p * q` at degree `k`, restated from `Polynomial.coeff_mul`. -/
lemma coeff_mul_eq (p q : ℝ[X]) (k : ℕ) :
    (p * q).coeff k = ∑ ij ∈ Finset.antidiagonal k, p.coeff ij.1 * q.coeff ij.2 :=
  coeff_mul p q k

snip end

/--
  Main statement. We encode the hypothesis using two monic polynomials `p, q`
  of degrees `r` and `s` with nonnegative coefficients whose product is `psi (r+s)`.
  The conclusion is that every coefficient of `p` and of `q` is `0` or `1`.
-/
problem imc2001_p7 (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (p q : ℝ[X])
    (hp_monic : p.Monic) (hq_monic : q.Monic)
    (hp_deg : p.natDegree = r) (hq_deg : q.natDegree = s)
    (hp_nn : ∀ i, 0 ≤ p.coeff i) (hq_nn : ∀ j, 0 ≤ q.coeff j)
    (hprod : p * q = psi (r + s)) :
    (∀ i, p.coeff i = 0 ∨ p.coeff i = 1) ∧
    (∀ j, q.coeff j = 0 ∨ q.coeff j = 1) := by
  -- TODO: The proof is via induction on r + s. Key steps:
  --
  -- (1) `a_0 * b_0 = 1` (constant coefficient).
  -- (2) WLOG `r ≤ s`. Look at coefficient of `x^r` in the product. One summand
  --     is `a_r * b_0 = b_0` (using leading `a_r = 1`). The rest are nonneg,
  --     summing to `1`. Hence `b_0 ≤ 1`.
  -- (3) Similarly, coefficient of `x^s` gives `a_0 ≤ 1`.
  -- (4) Combined with `a_0 * b_0 = 1`, conclude `a_0 = b_0 = 1`.
  -- (5) Induct on higher coefficients, or reduce to a smaller factorization
  --     problem via palindrome symmetry of `psi` and careful case analysis.
  sorry

end Imc2001P7
