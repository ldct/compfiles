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
  sorry

end Imc2021P5
