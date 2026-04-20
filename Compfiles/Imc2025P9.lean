/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2025, Problem 9

Let `n` be a positive integer. Consider the following random process which
produces a sequence of `n` distinct positive integers `X₁, X₂, …, Xₙ`.

First, `X₁` is chosen randomly with `P(X₁ = i) = 2⁻ⁱ` for every positive
integer `i`. For `1 ≤ j ≤ n − 1`, having chosen `X₁, …, Xⱼ`, arrange the
remaining positive integers in increasing order as `n₁ < n₂ < ⋯`, and choose
`Xⱼ₊₁` randomly with `P(Xⱼ₊₁ = nᵢ) = 2⁻ⁱ` for every positive integer `i`.

Let `Yₙ = max{X₁, …, Xₙ}`. Show that

  `E[Yₙ] = Σᵢ₌₁ⁿ 2ⁱ / (2ⁱ − 1)`.
-/

namespace Imc2025P9

/-- We model the process abstractly: we assert the existence of a sequence
`EY : ℕ → ℝ` representing `E[Yₙ]` satisfying two natural properties,
  - `EY 0 = 0` (empty maximum taken as 0 by convention), and
  - the increment `EY (n+1) - EY n` equals the expected gain, which the
    solution computes to be `2^(n+1)/(2^(n+1) - 1)`.
The problem then says `EY n = Σ_{i=1}^n 2^i / (2^i - 1)`.

This captures the mathematical content while sidestepping the heavy
measure-theoretic setup of the underlying probability space. -/
problem imc2025_p9 (EY : ℕ → ℝ)
    (hEY0 : EY 0 = 0)
    (hEYstep : ∀ n : ℕ, EY (n + 1) - EY n =
      (2 : ℝ) ^ (n + 1) / ((2 : ℝ) ^ (n + 1) - 1)) :
    ∀ n : ℕ, EY n = ∑ i ∈ Finset.range n, (2 : ℝ) ^ (i + 1) / ((2 : ℝ) ^ (i + 1) - 1) := by
  intro n
  induction n with
  | zero => simpa using hEY0
  | succ k ih =>
    have hstep := hEYstep k
    rw [Finset.sum_range_succ, ← ih]
    linarith

end Imc2025P9
