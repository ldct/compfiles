/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2021, Problem 5

Let `A` be a real `n × n` matrix and suppose that for every positive
integer `m` there exists a real symmetric matrix `B` such that
`2021 B = A^m + B²`. Prove that `|det A| ≤ 1`.
-/

namespace Imc2021P5

open Matrix

/-- The problem: if for every `m ≥ 1` there exists a real symmetric `B`
with `2021 B = A^m + B²`, then `|det A| ≤ 1`.

Official solution: for `m = 1`, `A = 2021 B - B²` is real symmetric and
diagonalizable with real eigenvalues. For any eigenvalue `λ` of `A` and
corresponding eigenvalue `μ` of the symmetric `B = B_m`, we have
`μ² - 2021 μ + λ^m = 0`. Real discriminant gives `λ^m ≤ 2021²/4`. Since
this holds for all `m`, `|λ| ≤ 1`, so `|det A| ≤ 1`.

TODO: formalize. Mathlib gaps: real-symmetric diagonalization with real
eigenvalues; coupling of eigenvalues of `A` and `B`.
-/
problem imc2021_p5 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hAB : ∀ m : ℕ, 0 < m → ∃ B : Matrix (Fin n) (Fin n) ℝ,
      B.IsSymm ∧ (2021 : ℝ) • B = A ^ m + B ^ 2) :
    |A.det| ≤ 1 := by
  -- TODO: Proof plan (out of reach within current formalization budget):
  -- Step 1: From m=1 case, A = 2021·B₁ - B₁² with B₁ symmetric (so A is symmetric
  --   and commutes with B₁). Use Matrix.IsHermitian.eigenvectorBasis to diagonalize A
  --   and B₁ simultaneously; A's eigenvalues are real.
  -- Step 2: For each m, obtain B_m symmetric; use that A commutes with B_m
  --   (from 2021 B_m = A^m + B_m², A and B_m are polynomials in each other ⇒
  --   they commute). Simultaneous diagonalization yields: for each eigenvalue λ of A
  --   there is a real eigenvalue μ of B_m with 2021 μ = λ^m + μ². Discriminant ≥ 0
  --   gives λ^m ≤ 2021²/4.
  -- Step 3: Taking m even and m→∞, |λ| ≤ 1. Since |det A| = ∏|λᵢ| ≤ 1.
  -- Mathlib gaps:
  --   (a) Coupling the eigenvalues of two commuting Hermitian matrices (there is no
  --       direct lemma; needs manual construction of simultaneous eigenvector basis).
  --   (b) |det A| = ∏ |eigenvalue|: via Matrix.det_eq_prod_roots_charpoly_of_splits
  --       over ℂ, combined with the fact that A's characteristic poly has real roots.
  sorry

end Imc2021P5
