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
    -- Outline of the mathematical argument (following the IMC 2023 solution):
    -- 1. Over ℂ, factor P(x,y) = (x+iy)^n (x-iy)^m · Q(x,y) with Q not divisible
    --    by (x+iy) or (x-iy). Using the identity one shows Q is a constant c
    --    with c² = c, so c ∈ {0, 1}.
    -- 2. If c = 0, then P = 0 (contradiction with P ≠ 0 case), else Q = 1.
    -- 3. For P to have real coefficients, we need n = m, giving P = (x²+y²)^n.
    --
    -- The elementary intermediate steps are derived below. The full classification
    -- requires factorization in ℂ[x, y], which needs substantial Mathlib
    -- infrastructure (MvPolynomial as UFD, complex substitution isomorphism,
    -- real-vs-complex coefficient descent). We state these intermediate facts as
    -- `have` hypotheses and leave the full classification as a scoped sorry.
    intro hP
    have hmul : ∀ x y z t : ℝ,
        (P.eval ![x, y]) * (P.eval ![z, t]) = P.eval ![x * z - y * t, x * t + y * z] := hP
    -- Evaluating at (0,0,0,0) gives P(0,0)² = P(0,0),
    -- so P(0,0) = 0 or P(0,0) = 1.
    have hP00_sq : (P.eval ![0, 0]) * (P.eval ![0, 0]) = P.eval ![0, 0] := by
      have := hmul 0 0 0 0
      simpa using this
    have hP00_cases : P.eval ![0, 0] = 0 ∨ P.eval ![0, 0] = 1 := by
      have h := hP00_sq
      have : (P.eval ![0, 0]) * (P.eval ![0, 0] - 1) = 0 := by ring_nf; linarith
      rcases mul_eq_zero.mp this with h1 | h2
      · left; exact h1
      · right; linarith
    -- Setting z = x, t = -y gives P(x,y) * P(x,-y) = P(x² + y², 0).
    have hnorm : ∀ x y : ℝ,
        (P.eval ![x, y]) * (P.eval ![x, -y]) = P.eval ![x * x + y * y, 0] := by
      intro x y
      have h := hmul x y x (-y)
      have e1 : x * x - y * (-y) = x * x + y * y := by ring
      have e2 : x * (-y) + y * x = 0 := by ring
      rw [e1, e2] at h
      exact h
    -- Setting y = 0, t = 0 gives P(x,0) * P(z,0) = P(x*z, 0);
    -- so R(s) := P(s, 0) is multiplicative on ℝ as a function.
    have hmul_R : ∀ x z : ℝ,
        (P.eval ![x, 0]) * (P.eval ![z, 0]) = P.eval ![x * z, 0] := by
      intro x z
      have h := hmul x 0 z 0
      have e1 : x * z - 0 * 0 = x * z := by ring
      have e2 : x * 0 + 0 * z = 0 := by ring
      rw [e1, e2] at h
      exact h
    -- Setting y = 0, z = 0 gives P(x,0) * P(0,t) = P(0, x*t)
    have hmix : ∀ x t : ℝ,
        (P.eval ![x, 0]) * (P.eval ![0, t]) = P.eval ![0, x * t] := by
      intro x t
      have h := hmul x 0 0 t
      have e1 : x * 0 - 0 * t = 0 := by ring
      have e2 : x * t + 0 * 0 = x * t := by ring
      rw [e1, e2] at h
      exact h
    -- Rotation: setting (x=0, y=1, z=x, t=y) gives P(0,1) · P(x,y) = P(-y, x).
    have hrot : ∀ x y : ℝ,
        (P.eval ![0, 1]) * (P.eval ![x, y]) = P.eval ![-y, x] := by
      intro x y
      have h := hmul 0 1 x y
      have e1 : (0:ℝ) * x - 1 * y = -y := by ring
      have e2 : (0:ℝ) * y + 1 * x = x := by ring
      rw [e1, e2] at h
      exact h
    -- Scaling along x-axis: setting (x=s, y=0, z, t) gives
    -- P(s,0) · P(z,t) = P(s*z, s*t): P(s,0) scales P uniformly.
    have hscale : ∀ s z t : ℝ,
        (P.eval ![s, 0]) * (P.eval ![z, t]) = P.eval ![s * z, s * t] := by
      intro s z t
      have h := hmul s 0 z t
      have e1 : s * z - 0 * t = s * z := by ring
      have e2 : s * t + 0 * z = s * t := by ring
      rw [e1, e2] at h
      exact h
    -- Full classification requires UFD factorization over ℂ[x,y] and the
    -- complex substitution argument; left as a scoped sorry.
    sorry

end Imc2023P3
