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
  · -- Hard direction: classification.
    -- The key idea: view the identity as multiplicativity of the function
    --   Q(w) := P(Re w, Im w) : ℂ → ℝ
    -- under complex multiplication. Over ℂ, one factors
    --   P(x,y) = c · (x + iy)^n · (x - iy)^m,
    -- and the real-coefficient constraint forces n = m, giving
    -- P(x,y) = (x² + y²)^n.
    --
    -- A full formalization requires substantial machinery:
    --   * transfer to ℂ[x,y] via `MvPolynomial.map`,
    --   * factorization over the UFD ℂ[x,y],
    --   * the substitution w = x+iy, w̄ = x-iy (a ring isomorphism),
    --   * real-coefficient reality constraint.
    -- We state the key multiplicative identity as a `have` and leave
    -- the classification argument as a scoped sorry.
    intro hP
    -- Establishing the functional multiplicativity:
    have hmul : ∀ x y z t : ℝ,
        (P.eval ![x, y]) * (P.eval ![z, t]) = P.eval ![x * z - y * t, x * t + y * z] := hP
    -- Evaluating at (0,0) with z = t = 0 gives P(0,0)² = P(0,0),
    -- so P(0,0) = 0 or P(0,0) = 1.
    have hP00_sq : (P.eval ![0, 0]) * (P.eval ![0, 0]) = P.eval ![0, 0] := by
      have := hmul 0 0 0 0
      simpa using this
    -- Setting z=x, t=-y gives P(x,y) * P(x,-y) = P(x² + y², 0).
    have hnorm : ∀ x y : ℝ,
        (P.eval ![x, y]) * (P.eval ![x, -y]) = P.eval ![x * x + y * y, 0] := by
      intro x y
      have h := hmul x y x (-y)
      have e1 : x * x - y * (-y) = x * x + y * y := by ring
      have e2 : x * (-y) + y * x = 0 := by ring
      rw [e1, e2] at h
      exact h
    -- Classification proof (remaining):
    sorry

end Imc2023P3
