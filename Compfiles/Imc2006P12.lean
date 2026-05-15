/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2006, Problem 12

(Also listed as Day 2, Problem 6.)

Let `A₁, A₂, A₃, B₁, B₂, B₃ ∈ GL₂(ℝ)` and suppose there exist
`S₁, S₂, S₃ ∈ GL₂(ℝ)` with

* `Aᵢ = Sᵢ⁻¹ * Bᵢ * Sᵢ` for `i = 1, 2, 3`,
* `A₁ * A₂ * A₃ = B₁ * B₂ * B₃ = I`,
* the matrices `A₁, A₂, A₃` have no common real eigenvector.

Prove that there exists a single `S ∈ GL₂(ℝ)` with `Aᵢ = S⁻¹ * Bᵢ * Sᵢ` for all
`i`. (More precisely: there is a single `S` such that `Aᵢ = S⁻¹ * Bᵢ * S` for
all three `i`.)

## Proof sketch

The argument is a case analysis on the Jordan form of `A₃` (after scaling so
the trivial scalar case is dispatched):

* **Distinct real eigenvalues.** Conjugate so `A₃` is diagonal, equal to `B₃`.
  The conditions `tr(A₂) = tr(B₂)` and `tr(A₂ A₃) = tr(A₁⁻¹) = tr(B₁⁻¹) =
  tr(B₂ B₃)` together with `det A₂ = det B₂` force `A₂` and `B₂` to have the
  same diagonal and off-diagonal product. A diagonal `S` then conjugates
  simultaneously, using non-vanishing of off-diagonal entries (otherwise `A₁,
  A₂, A₃` share an eigenvector).
* **Complex (non-real) eigenvalues.** Working over `ℂ`, the triples are
  conjugate via some `S_ℂ = S₀ + i S₁`. If either real part is invertible we
  are done; otherwise both are singular, and rank-one structure forces a real
  common eigenvector of all `Aⱼ`, contradicting the hypothesis.
* **Repeated real eigenvalue (non-scalar).** Each `Aⱼ` is similar to a Jordan
  block; conjugation reduces all three matrices to a normal form depending on
  two scalars `(u, v)` which are similarity invariants (determined by traces
  and determinants). The same normal form applies to the `Bⱼ`, giving a
  simultaneous conjugation.
-/

namespace Imc2006P12

open Matrix

/-- The hypothesis that the three matrices have no common (nonzero) real
eigenvector. -/
def NoCommonEigenvector (A₁ A₂ A₃ : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ¬ ∃ v : (Fin 2) → ℝ, v ≠ 0 ∧
      (∃ μ₁ : ℝ, A₁.mulVec v = μ₁ • v) ∧
      (∃ μ₂ : ℝ, A₂.mulVec v = μ₂ • v) ∧
      (∃ μ₃ : ℝ, A₃.mulVec v = μ₃ • v)

problem imc2006_p12
    (A₁ A₂ A₃ B₁ B₂ B₃ S₁ S₂ S₃ : Matrix (Fin 2) (Fin 2) ℝ)
    (hA₁ : IsUnit A₁) (hA₂ : IsUnit A₂) (hA₃ : IsUnit A₃)
    (hB₁ : IsUnit B₁) (hB₂ : IsUnit B₂) (hB₃ : IsUnit B₃)
    (hS₁ : IsUnit S₁) (hS₂ : IsUnit S₂) (hS₃ : IsUnit S₃)
    (hconj₁ : A₁ = S₁⁻¹ * B₁ * S₁)
    (hconj₂ : A₂ = S₂⁻¹ * B₂ * S₂)
    (hconj₃ : A₃ = S₃⁻¹ * B₃ * S₃)
    (hA : A₁ * A₂ * A₃ = 1)
    (hB : B₁ * B₂ * B₃ = 1)
    (hne : NoCommonEigenvector A₁ A₂ A₃) :
    ∃ S : Matrix (Fin 2) (Fin 2) ℝ, IsUnit S ∧
      A₁ = S⁻¹ * B₁ * S ∧
      A₂ = S⁻¹ * B₂ * S ∧
      A₃ = S⁻¹ * B₃ * S := by
  sorry

end Imc2006P12
