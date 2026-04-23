/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Competition 2023, Problem 10

For every positive integer `n`, let `f(n), g(n)` be the minimal positive
integers such that

  `1 + 1/1! + 1/2! + ⋯ + 1/n! = f(n) / g(n)`.

Determine whether there exists a positive integer `n` for which
`g(n) > n^{0.999 n}`.

Answer: Yes.
-/

namespace Imc2023P10

/-- The sum `Σ_{k=0}^n 1/k!` as a rational number (with `0! = 1` and
`1/0! = 1`). -/
def partialExpSum (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), (1 : ℚ) / Nat.factorial k

/-- `g n` is the denominator of the reduced form of `partialExpSum n`. -/
def g (n : ℕ) : ℕ := (partialExpSum n).den

problem imc2023_p10 :
    ∃ n : ℕ, 0 < n ∧ (g n : ℝ) > (n : ℝ) ^ ((0.999 : ℝ) * n) := by
  -- TODO: Following the official solution.
  -- Call a prime p "special" if for some k ≤ p-1, p divides f(j) for
  -- at least ε k values j ≤ k, where ε = 10^{-10}. Prove only finitely
  -- many special primes exist. For non-special p ≤ n, bound
  --   ν_p(g(1)⋯g(n)) ≥ (1-ε) ν_p(1! · 2! ⋯ n!).
  -- Summing over non-special primes contradicts g(n) ≤ n^{0.999n}.
  sorry

end Imc2023P10
