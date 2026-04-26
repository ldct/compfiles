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
  -- TODO: Following the official solution (Fedor Petrov, IMC 2023).
  -- Proof by contradiction: assume `g n ≤ n^{0.999 n}` for all `n`.
  --
  -- Step 1. Fix `ε = 10^{-10}`. Call a prime `p` *special* if there is
  -- some `k ∈ {1, …, p-1}` such that `p ∣ f(j)` for at least `ε·k` values
  -- of `j ∈ {1, …, k}`. Prove a *Lemma*: only finitely many special primes
  -- exist. (If `p ∣ f(j)` and `p ∣ f(j+r)`, then `p` divides
  -- `(j+r)! · (f(j+r)/g(j+r) − f(j)/g(j))`, a polynomial of degree `r-1`
  -- in `j`; so each fixed `r > 0` produces at most `r-1` such gaps.
  -- A gap-counting argument bounds `k`, hence bounds `p`.)
  --
  -- Step 2. For non-special `p ≤ n`, prove
  --   `ν_p(g(1)·g(2)···g(n)) ≥ (1-ε) · ν_p(1!·2!···n!)`.    (*)
  -- Partition `{p, p+1, …, n}` into blocks of length `p`. On a block
  -- `Δ = [a·p, a·p+k]` all `x!` with `x ∈ Δ` share the same p-adic
  -- valuation `T = ν_p((a·p)!)`. For `j = 0` or `1 ≤ j ≤ k` with
  -- `p ∤ f(j)`, the partial sum `∑_{i=0}^{a·p+j} 1/i!` has p-adic
  -- valuation `−T`, so `ν_p(g(a·p+j)) = T`. Since `p` is non-special,
  -- this happens for ≥ `(1-ε)(k+1)` values of `j` in each block.
  --
  -- Step 3. Let `A = ∏_p ∏_k p^{ν_p(g(k))}` over non-special primes
  -- `p ≤ n` and `k ≤ n`. Since `ν_p(g(k)) ≤ ν_p(k!) ≤ k`, we have
  -- `A ≤ (∏_p p)^{1+2+⋯+n} ≤ C^{n²}` for some constant `C`. Combining
  -- (*) over all non-special primes yields
  --   `A · g(1)·g(2)···g(n) ≥ (1!·2!···n!)^{1-ε}`.
  -- The hypothesis `g(n) ≤ n^{0.999 n} ≤ e^n · (n!)^{0.999}` gives
  --   `log(A·∏g(k)) ≤ O(n²) + 0.999 · log(∏k!)`,
  -- contradicting the lower bound for `n` large since
  -- `log(∏k!) = Θ(n² log n)`.
  sorry

end Imc2023P10
