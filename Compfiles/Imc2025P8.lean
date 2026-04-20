/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2025, Problem 8

For an `n × n` real matrix `A ∈ M_n(ℝ)`, denote by `A^R` its counter-clockwise
`90°` rotation. For example,

  `⎡1 2 3⎤^R   ⎡3 6 9⎤`
  `⎢4 5 6⎥   = ⎢2 5 8⎥`.
  `⎣7 8 9⎦     ⎣1 4 7⎦`

Formally, `(A^R)_{i,j} = A_{j, n+1-i}`.

Prove that if `A = A^R` then for any eigenvalue `λ` of `A` (as a complex
matrix), we have `Re λ = 0` or `Im λ = 0`.
-/

namespace Imc2025P8

open Matrix

/-- The counter-clockwise 90° rotation of a square matrix: sending position
  `(i, j)` to `(n + 1 - j, i)`. Equivalently, `(A^R)_{i,j} = A_{j, n+1-i}`.
  We encode `n+1-i` using `Fin.rev`. -/
def rot90 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => A j i.rev

/-- The statement: if `A = A^R`, then every complex eigenvalue `λ` of `A`
satisfies `Re λ = 0` or `Im λ = 0`. -/
problem imc2025_p8 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A = rot90 A)
    (lam : ℂ) (hlam : ∃ v : Fin n → ℂ, v ≠ 0 ∧
      (A.map (fun r => (r : ℂ))) *ᵥ v = lam • v) :
    lam.re = 0 ∨ lam.im = 0 := by
  -- TODO: Proof follows the official solution.
  -- Let J be the permutation matrix with J_{i,j} = δ_{i, n+1-j}. Then J is
  -- symmetric, J² = I, and A^R = J Aᵀ. So the condition A = A^R becomes
  -- A = J Aᵀ, i.e., J A = Aᵀ.
  -- Let x be a complex eigenvector with eigenvalue λ. Compute ⟨Ax, Ax⟩ two ways:
  --   (a) |λ|² ‖x‖² (using Ax = λx).
  --   (b) ⟨A* A x, x⟩ = ⟨Aᵀ A x, x⟩ = ⟨J A (λ x), x⟩ = λ² ⟨J x, x⟩.
  -- Since J is real symmetric, ⟨J x, x⟩ is real. So λ² is real, hence
  -- either Re λ = 0 (if λ² < 0) or Im λ = 0 (if λ² ≥ 0).
  sorry

end Imc2025P8
