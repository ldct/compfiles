/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2003, Problem 6
(IMC 2003, Day 1, Problem 6)

Let `f(z) = ∑ aₖ zᵏ` be a polynomial with real coefficients of degree `n`,
such that every complex root has strictly negative real part.

Prove that `aₖ · aₖ₊₃ < aₖ₊₁ · aₖ₊₂` for every `0 ≤ k ≤ n - 3`.
-/

namespace Imc2003P6

open Polynomial

problem imc2003_p6 (f : ℝ[X]) (hf : f.natDegree ≥ 3)
    (hroots : ∀ z : ℂ, z ∈ f.aroots ℂ → z.re < 0)
    (k : ℕ) (hk : k + 3 ≤ f.natDegree) :
    f.coeff k * f.coeff (k+3) < f.coeff (k+1) * f.coeff (k+2) := by
  -- Proof outline (from official solution):
  -- Factor f over ℝ as a product of linear factors `(kᵢ z + lᵢ)` with `kᵢ, lᵢ > 0`
  -- (root `-lᵢ/kᵢ < 0`) and quadratic factors `(pⱼ z² + qⱼ z + rⱼ)` with all
  -- coefficients positive (roots have negative real part). WLOG every coefficient
  -- of f is positive.
  --
  -- Extend `aₖ = 0` for `k < 0` or `k > n`, and induct on `n`.
  -- Base case `n ≤ 2`: vacuous since `aₖ aₖ₊₃ = 0`.
  -- Inductive step `n ≥ 3`: factor `f = (z² + p z + q) · g` with `p, q > 0`
  -- and `g = ∑ bₖ zᵏ`. Then `aₖ = q bₖ + p bₖ₋₁ + bₖ₋₂`. By induction
  -- `bₖ₊₁ bₖ₊₂ ≥ bₖ bₖ₊₃` for all k.
  --
  -- A direct expansion gives
  --   aₖ₊₁ aₖ₊₂ - aₖ aₖ₊₃
  --     = (bₖ₋₁ bₖ - bₖ₋₂ bₖ₊₁) + p (bₖ² - bₖ₋₂ bₖ₊₂)
  --     + q (bₖ₋₁ bₖ₊₂ - bₖ₋₂ bₖ₊₃) + p² (bₖ bₖ₊₁ - bₖ₋₁ bₖ₊₂)
  --     + q² (bₖ₊₁ bₖ₊₂ - bₖ bₖ₊₃) + p q (bₖ₊₁² - bₖ₋₁ bₖ₊₃).
  -- Each summand is nonnegative by the inductive hypothesis (Newton-type
  -- inequalities `bᵢ bⱼ ≥ bᵢ₋₁ bⱼ₊₁` for nonnegative log-concave sequences),
  -- and the `p²`-term is strictly positive in the valid range `0 ≤ k ≤ n - 3`.
  --
  -- TODO: The full formalization requires polynomial real-factorization
  -- (linear times irreducible quadratic) and a careful induction on the
  -- quadratic factors. This is left as future work.
  sorry

end Imc2003P6
