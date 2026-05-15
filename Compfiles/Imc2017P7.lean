/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2017, Problem 7

Let `p(x)` be a nonconstant polynomial with real coefficients.
For every positive integer `n`, let
  `q_n(x) = (x+1)^n p(x) + x^n p(x+1)`.
Prove that there are only finitely many numbers `n` such that all roots of `q_n(x)`
are real.

## Outline of proof

The argument proceeds via a Newton-type inequality for real-rooted polynomials.

* Lemma. If a real polynomial `f` of degree `m ≥ 2` has all real roots and leading
  coefficients `f.coeff m = aₘ`, `f.coeff (m-1) = aₘ₋₁`, `f.coeff (m-2) = aₘ₋₂`,
  then `aₘ₋₁² ≥ 2 aₘ aₘ₋₂` (since `Σ wᵢ² = (Σ wᵢ)² - 2 Σ_{i<j} wᵢ wⱼ ≥ 0`).

* Compute the top three coefficients of `q_n`. Writing
  `p(x) = a x^k + b x^{k-1} + c x^{k-2} + …`, one finds
    `Aₙ = 2a`, `Bₙ = (n+k)a + 2b`,
    `Cₙ = ((n(n-1)+k(k-1))/2) a + (n+k-1) b + 2c`.

* Then `Bₙ² - 2 Aₙ Cₙ = -a² n² + O(n)`, which is eventually negative,
  contradicting the lemma. Hence only finitely many `n` give a real-rooted `q_n`.
-/

namespace Imc2017P7

open Polynomial

/-- The polynomial `q_n(x) = (x+1)^n p(x) + x^n p(x+1)`. -/
noncomputable def q (p : ℝ[X]) (n : ℕ) : ℝ[X] :=
  (X + 1) ^ n * p + X ^ n * p.comp (X + 1)

snip begin

/-- Newton-type inequality: for a real polynomial `f` of degree `m ≥ 2` whose
roots are all real, we have `f.coeff (m-1)² ≥ 2 * f.coeff m * f.coeff (m-2)`.

This follows from `Σ rᵢ² = (Σ rᵢ)² - 2 e₂(r) ≥ 0` together with Vieta. -/
lemma newton_ineq (f : ℝ[X]) (hm : 2 ≤ f.natDegree)
    (hsplit : Splits f) :
    2 * f.leadingCoeff * f.coeff (f.natDegree - 2)
      ≤ f.coeff (f.natDegree - 1) ^ 2 := by
  sorry

/-- Coefficient computation: leading natDegree of `q p n` is `n + p.natDegree`,
and the leading coefficient is `2 * p.leadingCoeff`. -/
lemma q_natDegree_and_leadingCoeff
    (p : ℝ[X]) (hp : 1 ≤ p.natDegree) (n : ℕ) (hn : 1 ≤ n) :
    (q p n).natDegree = n + p.natDegree ∧
    (q p n).coeff (n + p.natDegree) = 2 * p.leadingCoeff := by
  sorry

/-- The "B_n" coefficient of `q_n`: the coefficient of `x^{n+k-1}` is
`(n+k) * a + 2 * b`, where `a, b` are the top two coefficients of `p`. -/
lemma q_coeff_subOne
    (p : ℝ[X]) (hp : 1 ≤ p.natDegree) (n : ℕ) (hn : 1 ≤ n) :
    (q p n).coeff (n + p.natDegree - 1)
      = (n + p.natDegree) * p.leadingCoeff
        + 2 * p.coeff (p.natDegree - 1) := by
  sorry

/-- The "C_n" coefficient of `q_n`: the coefficient of `x^{n+k-2}`. We allow
`p.natDegree = 1`, in which case `p.coeff (p.natDegree - 2)` is the constant
term of `p` shifted (actually `p.coeff (-1) = 0` does not occur since natDegree ≥ 1
makes `natDegree - 2 = 0` when natDegree = 1, etc.). For our application we just
need the case `natDegree ≥ 2`. -/
lemma q_coeff_subTwo
    (p : ℝ[X]) (hp : 2 ≤ p.natDegree) (n : ℕ) (hn : 2 ≤ n) :
    (2 : ℝ) * (q p n).coeff (n + p.natDegree - 2)
      = ((n * (n - 1) : ℕ) + (p.natDegree * (p.natDegree - 1) : ℕ) : ℝ)
          * p.leadingCoeff
        + 2 * (n + p.natDegree - 1 : ℝ) * p.coeff (p.natDegree - 1)
        + 4 * p.coeff (p.natDegree - 2) := by
  sorry

snip end

/-- Main theorem: there are only finitely many `n ≥ 1` such that all roots of
`q_n(x) = (x+1)^n p(x) + x^n p(x+1)` are real. -/
problem imc2017_p7 (p : ℝ[X]) (hp : 1 ≤ p.natDegree) :
    Set.Finite {n : ℕ | 1 ≤ n ∧ Splits (q p n)} := by
  sorry

end Imc2017P7
