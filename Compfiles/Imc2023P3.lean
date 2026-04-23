/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2023, Problem 3

Find all polynomials `P` in two variables with real coefficients satisfying
`P(x,y) P(z,t) = P(xz - yt, xt + yz)`.

Answer: `P = 0` or `P(x, y) = (x² + y²)^n` for some `n : ℕ`.
-/

namespace Imc2023P3

open MvPolynomial

/-- The set of polynomials `P : ℝ[X, Y]` satisfying the identity
`P(x,y) P(z,t) = P(xz - yt, xt + yz)`. The answer is
`P = 0 ∨ ∃ n, P = (X² + Y²)^n`. -/
determine answer : Set (MvPolynomial (Fin 2) ℝ) :=
  {0} ∪ { P | ∃ n : ℕ, P = (X 0 ^ 2 + X 1 ^ 2) ^ n }

problem imc2023_p3 (P : MvPolynomial (Fin 2) ℝ) :
    P ∈ answer ↔
    ∀ x y z t : ℝ,
      (P.eval ![x, y]) * (P.eval ![z, t]) = P.eval ![x * z - y * t, x * t + y * z] := by
  constructor
  · -- Easy direction
    rintro (hP | ⟨n, rfl⟩)
    · -- P = 0
      simp at hP
      subst hP
      intro x y z t
      simp
    · -- P = (X² + Y²)^n
      intro x y z t
      simp only [eval_pow, eval_add, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
                  Matrix.cons_val_fin_one]
      rw [← mul_pow]
      congr 1
      ring
  · -- Hard direction: classification
    -- TODO: full classification requires factoring P over ℂ as
    -- P(x,y) = c (x+iy)^n (x-iy)^m and using real-coefficient constraint.
    sorry

end Imc2023P3
