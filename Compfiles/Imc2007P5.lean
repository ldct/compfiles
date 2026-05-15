/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2007, Problem 5
(IMC 2007, Day 1, Problem 5)

Let `n` be a positive integer and `a_1, …, a_n` be arbitrary integers.
Suppose that a function `f : ℤ → ℝ` satisfies
`∑_{i=1}^n f(k + a_i * ℓ) = 0`
whenever `k` and `ℓ` are integers and `ℓ ≠ 0`.  Prove that `f = 0`.
-/

namespace Imc2007P5

open scoped Polynomial
open Polynomial Finset

snip begin

/-!
## Outline of the proof

Let `I` be the set of polynomials `P = ∑ b_j X^j ∈ ℝ[X]` such that
`∑ b_j f(k + j ℓ) = 0` for every `k ∈ ℤ` and every `ℓ ≠ 0`.

* `I` is an ideal of `ℝ[X]` (closed under addition, scalar multiplication and
  multiplication by `X`; the latter follows from the substitution `k ↦ k + ℓ`).
* By translating the index, we may assume `min a_i = 0`; in particular all
  `a_i ≥ 0`.  Then `R(X) = ∑ X^{a_i}` lies in `I` and is non-zero.
* Since `ℝ[X]` is a PID, `I = (Q)` for some non-zero `Q`.
* If `deg Q = 0` then `1 ∈ I`, hence `f(k) = 0` for all `k`.
* Otherwise `Q` has a complex root `c`.  The substitution `ℓ ↦ m ℓ` shows
  `Q(X^m) ∈ I`, so `Q ∣ Q(X^m)` in `ℝ[X]`, hence also in `ℂ[X]`, giving
  `Q(c^m) = 0` for every `m ≥ 1`.
* Because `min a_i = 0`, `R(0) ≥ 1`, so `Q(0) ≠ 0`; therefore `c ≠ 0`.
* The non-zero powers `c, c^2, c^3, …` all lie among the finitely many roots
  of `Q`, so two of them coincide: `c^N = c^M` with `N > M`, whence
  `c^{N-M} = 1`.  In particular `1` is a root of `Q`.
* But `R(1) = n ≥ 1` together with `Q ∣ R` forces `Q(1) ≠ 0`, a contradiction.

The full formalisation of this argument requires a substantial amount of
infrastructure (the ideal `I` and its generator inside `ℝ[X]`, complex roots
of real polynomials, …) and is left for future work.
-/

snip end

/-- IMC 2007 P5: any function `f : ℤ → ℝ` satisfying
`∑_{i=1}^n f(k + a_i ℓ) = 0` for all `k ∈ ℤ` and all `ℓ ≠ 0` is identically
zero. -/
problem imc2007_p5
    (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℤ) (f : ℤ → ℝ)
    (hf : ∀ (k ℓ : ℤ), ℓ ≠ 0 → ∑ i, f (k + a i * ℓ) = 0) :
    f = 0 := by
  -- TODO: full formalisation of the polynomial-ideal argument.
  sorry

end Imc2007P5
