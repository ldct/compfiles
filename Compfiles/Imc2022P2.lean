/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2022, Problem 2

Let `n` be a positive integer. Find all `n × n` real matrices `A` with only
real eigenvalues satisfying
  `A + A^k = A^T`
for some integer `k ≥ n`.

Answer: `A = 0`.
-/

namespace Imc2022P2

open Matrix

/-- The answer: the only such matrix is the zero matrix. -/
determine answer {n : ℕ} : Matrix (Fin n) (Fin n) ℝ := 0

snip begin

/-- For real `x` and integer `k ≥ 2`, the value `1 + (1 + x^(k-1))^k` is positive.
This is the key inequality behind the minimal polynomial argument. -/
lemma one_add_pow_pos {k : ℕ} (hk : 2 ≤ k) (x : ℝ) :
    0 < 1 + (1 + x ^ (k - 1)) ^ k := by
  -- Case split on parity of k.
  rcases Nat.even_or_odd k with hke | hko
  · -- k even: (1 + x^(k-1))^k ≥ 0 since k is even.
    have h1 : 0 ≤ (1 + x ^ (k - 1)) ^ k := Even.pow_nonneg hke _
    linarith
  · -- k odd: k-1 is even, so x^(k-1) ≥ 0. Thus 1 + x^(k-1) ≥ 1 > 0,
    -- so (1 + x^(k-1))^k > 0.
    have hk1even : Even (k - 1) := by
      rcases hko with ⟨m, hm⟩
      refine ⟨m, ?_⟩
      omega
    have hxpow : 0 ≤ x ^ (k - 1) := Even.pow_nonneg hk1even x
    have h1 : 0 < 1 + x ^ (k - 1) := by linarith
    have h2 : 0 < (1 + x ^ (k - 1)) ^ k := pow_pos h1 k
    linarith

/-- From `A + A^k = Aᵀ`, transposing and substituting gives the annihilating
identity `A^k * (1 + (1 + A^(k-1))^k) = 0`. That is,
`p(x) = x^k * (1 + (1 + x^(k-1))^k)` annihilates `A`. -/
lemma annihilating_identity {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hEq : A + A ^ k = A.transpose) :
    A ^ k * (1 + (1 + A ^ (k - 1)) ^ k) = 0 := by
  -- Take transpose of hEq: Aᵀ + (Aᵀ)^k = A.
  have hT : A.transpose + (A.transpose) ^ k = A := by
    have ht := congrArg Matrix.transpose hEq
    simpa [Matrix.transpose_add, Matrix.transpose_pow] using ht
  -- Substitute Aᵀ = A + A^k. Then (A + A^k) + (A + A^k)^k = A.
  have h2 : (A + A ^ k) + (A + A ^ k) ^ k = A := by
    conv_lhs => rw [hEq]
    exact hT
  -- So (A + A^k)^k = -A^k.
  have h3 : (A + A ^ k) ^ k = - A ^ k := by
    have : (A + A ^ k) + (A + A ^ k) ^ k - (A + A ^ k) = A - (A + A ^ k) := by
      rw [h2]
    simpa using this
  -- Factor A + A^k = A * (1 + A^(k-1)) since k ≥ 1.
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hfac : A + A ^ k = A * (1 + A ^ (k - 1)) := by
    rw [Matrix.mul_add, Matrix.mul_one, ← pow_succ', hk']
  -- Substitute and compute: (A * (1 + A^(k-1)))^k = -A^k.
  -- Since powers of A and (1 + A^(k-1)) commute (both are polynomials in A),
  -- (A * (1 + A^(k-1)))^k = A^k * (1 + A^(k-1))^k.
  have hcomm : Commute A (1 + A ^ (k - 1)) := by
    refine (Commute.one_right A).add_right ?_
    exact (Commute.refl A).pow_right (k - 1)
  have hexp : (A * (1 + A ^ (k - 1))) ^ k = A ^ k * (1 + A ^ (k - 1)) ^ k :=
    hcomm.mul_pow k
  rw [hfac, hexp] at h3
  -- h3 : A^k * (1 + A^(k-1))^k = -A^k.
  -- So A^k * (1 + (1 + A^(k-1))^k) = A^k * 1 + A^k * (1 + A^(k-1))^k
  --                                = A^k + (-A^k) = 0.
  rw [Matrix.mul_add, Matrix.mul_one, h3]
  exact add_neg_cancel (A ^ k)

snip end

problem imc2022_p2 {n : ℕ} (_hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (k : ℕ) (_hk : n ≤ k)
    (_hreal : ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toLin' (A.map ((algebraMap ℝ ℂ)))) μ → μ.im = 0)
    (_hEq : A + A ^ k = A.transpose) :
    A = answer := by
  -- The argument: transposing `A + A^k = A^T` and substituting gives
  --   `A^k * (I + (I + A^(k-1))^k) = 0`,
  -- so `p(x) = x^k * (1 + (1 + x^(k-1))^k)` annihilates `A`.
  -- The only real root of `p` is `x = 0` (by `one_add_pow_pos`), so every real
  -- eigenvalue of `A` is `0`. Since all eigenvalues of `A` are real, `A` is
  -- nilpotent of index ≤ n, hence `A^n = 0`, so `A^k = 0` (as `k ≥ n`). Then
  -- `A = A^T` is symmetric and nilpotent, hence `A = 0`.
  -- TODO: full formalization requires eigenvalue/Cayley–Hamilton machinery.
  sorry

end Imc2022P2
