/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2006, Problem 6

(Day 1, Problem 6.)

Find all `(a₀, a₁, …, aₙ)` (with `aₙ ≠ 0`) such that for every `n`-times
differentiable function `f : ℝ → ℝ` for which there exist `n + 1`
points `x₀ < x₁ < … < xₙ` with `f(xᵢ) = 0`, there exists `ξ ∈ (x₀, xₙ)` with

`a₀ f(ξ) + a₁ f'(ξ) + … + aₙ f⁽ⁿ⁾(ξ) = 0`.

Answer: exactly those tuples such that all roots (over `ℂ`) of the polynomial
`A(x) = a₀ + a₁ x + ⋯ + aₙ xⁿ` are real.
-/

namespace Imc2006P6

open Polynomial

/-- The set of polynomials `A ∈ ℝ[X]` (of positive degree) encoding the tuples that satisfy the
property: the roots of `A` (viewed over `ℂ`) are all real, equivalently `A` splits over `ℝ`. -/
determine solution_set : Set ℝ[X] := { A | 0 < A.natDegree ∧ A.Splits }

/-- The "mean value" property for a polynomial `A = ∑ aᵢ X^i` of degree `n`:
every `n`-times differentiable function `f` with `n + 1` zeros in an increasing sequence
admits some `ξ` strictly between the extreme zeros with
`∑ aᵢ · f⁽ⁱ⁾(ξ) = 0`. -/
def MeanValueProperty (A : ℝ[X]) : Prop :=
  ∀ (f : ℝ → ℝ) (x : ℕ → ℝ), ContDiff ℝ A.natDegree f →
    StrictMono x →
    (∀ i ≤ A.natDegree, f (x i) = 0) →
    ∃ ξ, x 0 < ξ ∧ ξ < x A.natDegree ∧
      (∑ i ∈ Finset.range (A.natDegree + 1), A.coeff i * iteratedDeriv i f ξ) = 0

problem imc2006_p6 :
    ∀ A : ℝ[X], 0 < A.natDegree →
      (A ∈ solution_set ↔ MeanValueProperty A) := by
  -- The full proof requires:
  --   (⇐) Necessary direction: if A has a non-real root u + iv (v ≠ 0),
  --       consider g(x) = e^{ux} sin(vx); it satisfies ∑ aᵢ g⁽ⁱ⁾ = 0 and has infinitely many
  --       zeros. Perturbing by ε · x^k (k = minimal index with a_k ≠ 0) still yields n + 1
  --       zeros but ∑ aᵢ f⁽ⁱ⁾(ξ) = a_k · ε · k! ≠ 0 everywhere.
  --   (⇒) Sufficient direction: induct on n. For n = 1 use Rolle on g(x) = e^{a₀ x / a₁} f(x).
  --       For n > 1, factor A(x) = (x − c) B(x) with c ∈ ℝ, find zeros of (f' − c f),
  --       and apply the inductive hypothesis to B.
  -- Both directions are substantial analysis arguments requiring a development of
  -- facts about exponentials, iterated Rolle applications, and polynomial factorization.
  sorry

end Imc2006P6
