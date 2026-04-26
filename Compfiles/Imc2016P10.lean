/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2016, Problem 10

Let `A` be an `n × n` complex matrix whose eigenvalues have absolute value at
most `1`. Prove that
`‖A^n‖ ≤ (n / ln 2) * ‖A‖^(n-1)`.

Here `‖B‖ = sup_{‖x‖ ≤ 1} ‖B x‖` is the operator norm with respect to the
Euclidean (ℓ²) norm on `ℂ^n`.
-/

namespace Imc2016P10

open scoped Matrix.Norms.L2Operator

problem imc2016_p10 (n : ℕ) (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ μ ∈ spectrum ℂ A, ‖μ‖ ≤ 1) :
    ‖A ^ n‖ ≤ (n / Real.log 2) * ‖A‖ ^ (n - 1) := by
  -- TODO: full proof.
  -- Approach (Cayley–Hamilton):
  --   Let r = ‖A‖. The characteristic polynomial of A is
  --     χ(t) = t^n + c₁ t^{n-1} + ⋯ + c_n,
  --   with |c_k| ≤ binomial n k by Vieta (the roots of χ are the eigenvalues
  --   and have absolute value ≤ 1).
  --   Cayley–Hamilton gives A^n = -∑_{k=1}^n c_k A^{n-k}, so
  --     ‖A^n‖ ≤ ∑_{k=1}^n binomial n k * r^{n-k} = (1+r)^n - r^n.
  --   Combined with the trivial bound ‖A^n‖ ≤ r^n: setting
  --     r₀ = (2^{1/n} - 1)^{-1},
  --   the two bounds agree at r = r₀, and r₀ < n / log 2.
  --     • For r ≤ r₀: ‖A^n‖ ≤ r^n ≤ r₀ r^{n-1} < (n / log 2) r^{n-1}.
  --     • For r > r₀: ((1+r)^n - r^n)/r^{n-1} is decreasing in r, hence
  --       ≤ r₀ ((1 + 1/r₀)^n - 1) = r₀ < n / log 2.
  sorry

end Imc2016P10
