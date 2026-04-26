/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2002, Problem 6
(IMC 2002, Day 1, Problem 6)

For a real `n × n` matrix `M`, let `‖M‖` denote the operator `2`-norm.
Suppose `A` is a real `n × n` matrix such that for every integer `k ≥ 1`,
`‖A^k - A^{k-1}‖ ≤ 1 / (2002 * k)`. Prove that `‖A^k‖ ≤ 2002` for every `k`.

We formulate the problem for an arbitrary continuous linear endomorphism
of a (finite-dimensional) real normed space `E`, using the standard
operator norm on `E →L[ℝ] E`. The matrix case follows by identifying
`Matrix (Fin n) (Fin n) ℝ` with `EuclideanSpace ℝ (Fin n) →L[ℝ]
EuclideanSpace ℝ (Fin n)` via the operator-2-norm.

## Proof sketch (Solov’ev / IMC official solution)

Let `a_n := ‖A^{n+1} - A^n‖`. The key algebraic identity
  `A^{k+m+1} - A^{k+m} = (A^{k+m+2} - A^{k+m+1}) - (A^{k+1} - A^k)(A^{m+1} - A^m)`
gives the submultiplicative inequality `a_{k+m} ≤ a_{k+m+1} + a_k * a_m`.

A delicate analytic lemma then shows: if `(b_n)` is a non-negative sequence
satisfying `b_{2k} - b_{2k+1} ≤ b_k^2`, `b_{2k+1} - b_{2k+2} ≤ b_k * b_{k+1}`,
and `limsup n b_n < 1/4`, then `limsup b_n^{1/n} < 1`. Apply with
`b_n = a_n`. Since the hypothesis gives `n a_n ≤ 1/2002 < 1/4`, this
yields geometric decay of `a_n`, hence `∑ a_n < ∞`. Telescoping
`A^k = A^0 + Σ_{j<k}(A^{j+1} - A^j)` gives `‖A^k‖ ≤ 1 + ∑ a_j`.

This is a deep analytic result; we record the statement here and leave
the proof as a `sorry`.
-/

namespace Imc2002P6

open scoped Topology

/-- The IMC 2002 P6 statement, formulated for a continuous linear
endomorphism of a real normed space. -/
problem imc2002_p6
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E)
    (h : ∀ k : ℕ, 1 ≤ k → ‖A ^ k - A ^ (k - 1)‖ ≤ 1 / (2002 * k)) :
    ∀ k : ℕ, ‖A ^ k‖ ≤ 2002 := by
  -- The full proof of this theorem requires the analytic limsup lemma
  -- (Lemma 1 in the official solution): if `(b_n)` is non-negative with
  -- `b_{2k} - b_{2k+1} ≤ b_k^2`, `b_{2k+1} - b_{2k+2} ≤ b_k * b_{k+1}`,
  -- and `limsup n b_n < 1/4`, then `limsup b_n^{1/n} < 1`.
  -- Combined with the algebraic identity
  --   `A^{k+m+1} - A^{k+m} = (A^{k+m+2} - A^{k+m+1})
  --                          - (A^{k+1} - A^k)(A^{m+1} - A^m)`
  -- which gives `‖A^{k+m+1} - A^{k+m}‖ ≤ ‖A^{k+m+2} - A^{k+m+1}‖
  --                                       + ‖A^{k+1} - A^k‖ * ‖A^{m+1} - A^m‖`,
  -- this yields summability of `‖A^{n+1} - A^n‖` and the telescoping bound
  -- `‖A^k‖ ≤ 1 + ∑_{j<k} ‖A^{j+1} - A^j‖`.
  -- TODO: complete the proof.
  sorry

end Imc2002P6
