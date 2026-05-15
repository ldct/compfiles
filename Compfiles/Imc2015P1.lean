/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2015, Problem 1

For any integer `n ≥ 2` and two `n × n` matrices with real entries `A`, `B`
such that `A`, `B` and `A + B` are invertible and
`A⁻¹ + B⁻¹ = (A + B)⁻¹`, prove that `det A = det B`.
-/

namespace Imc2015P1

open Matrix

-- snip begin

/-- Over ℝ, if `x^3 = 1` then `x = 1`. -/
lemma real_cube_eq_one {x : ℝ} (hx : x ^ 3 = 1) : x = 1 := by
  have hfact : (x - 1) * (x ^ 2 + x + 1) = 0 := by nlinarith [hx]
  have hpos : x ^ 2 + x + 1 > 0 := by nlinarith [sq_nonneg (2 * x + 1)]
  rcases mul_eq_zero.mp hfact with h | h
  · linarith
  · linarith

-- snip end

problem imc2015_p1 {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsUnit A.det) (hB : IsUnit B.det) (hAB : IsUnit (A + B).det)
    (h : A⁻¹ + B⁻¹ = (A + B)⁻¹) :
    A.det = B.det := by
  have hAinv_r : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have hBinv_l : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
  have hBinv_r : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
  have hAinv_l : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  -- From h: (A+B) * (A⁻¹ + B⁻¹) = 1.
  have hmul : (A + B) * (A⁻¹ + B⁻¹) = 1 := by
    rw [h]; exact Matrix.mul_nonsing_inv (A + B) hAB
  -- Expand: (A+B)(A⁻¹+B⁻¹) = A*A⁻¹ + A*B⁻¹ + B*A⁻¹ + B*B⁻¹ = 1 + A*B⁻¹ + B*A⁻¹ + 1.
  have hexpand : (A + B) * (A⁻¹ + B⁻¹) =
      A * B⁻¹ + B * A⁻¹ + (1 + 1) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hAinv_r, hBinv_r]
    abel
  rw [hexpand] at hmul
  -- So A*B⁻¹ + B*A⁻¹ + 1 = 0.
  have hkey : A * B⁻¹ + B * A⁻¹ + 1 = 0 := by
    have h2 : A * B⁻¹ + B * A⁻¹ + (1 + 1) - 1 = 1 - 1 := by rw [hmul]
    have : A * B⁻¹ + B * A⁻¹ + 1 = A * B⁻¹ + B * A⁻¹ + (1 + 1) - 1 := by abel
    rw [this, h2]; abel
  -- Set X = A * B⁻¹.
  set X : Matrix (Fin n) (Fin n) ℝ := A * B⁻¹ with hX_def
  -- (B*A⁻¹)*X = B*(A⁻¹*A)*B⁻¹ = B*B⁻¹ = 1.
  have hBA_X : (B * A⁻¹) * X = 1 := by
    show (B * A⁻¹) * (A * B⁻¹) = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc A⁻¹, hAinv_l, Matrix.one_mul, hBinv_r]
  -- Multiply hkey on right by X. (X + B*A⁻¹ + 1) * X = 0 * X = 0.
  -- X*X + (B*A⁻¹)*X + 1*X = 0, i.e. X*X + 1 + X = 0.
  have hXsq : X * X + X + 1 = 0 := by
    have hm : (X + B * A⁻¹ + 1) * X = 0 := by rw [hkey, Matrix.zero_mul]
    have hdist : X * X + B * A⁻¹ * X + 1 * X = 0 := by
      rw [show (X + B * A⁻¹ + 1) * X = X * X + B * A⁻¹ * X + 1 * X from by
        rw [Matrix.add_mul, Matrix.add_mul]] at hm
      exact hm
    rw [hBA_X, Matrix.one_mul] at hdist
    -- hdist : X * X + 1 + X = 0
    have : X * X + X + 1 = X * X + 1 + X := by abel
    rw [this]; exact hdist
  -- So X² + X + 1 = 0.
  have hXpoly : X^2 + X + 1 = 0 := by
    rw [sq]; exact hXsq
  -- Multiply by (X - 1): (X-1)(X² + X + 1) = X³ - 1, so X³ = 1.
  have hXcube : X^3 = 1 := by
    have hexp : (X - 1) * (X^2 + X + 1) = X^3 - 1 := by noncomm_ring
    have hz : (X - 1) * (X^2 + X + 1) = 0 := by rw [hXpoly, Matrix.mul_zero]
    rw [hexp] at hz
    -- hz : X^3 - 1 = 0
    have : X^3 = 1 := by
      have h2 : X^3 = X^3 - 1 + 1 := by abel
      rw [h2, hz]; abel
    exact this
  -- det X ^ 3 = 1 over ℝ, hence det X = 1.
  have hdetX : X.det = 1 := by
    have h1 : X.det ^ 3 = 1 := by
      rw [← Matrix.det_pow, hXcube, Matrix.det_one]
    exact real_cube_eq_one h1
  -- det X = det A * det B⁻¹ = det A / det B.
  have hdetX2 : X.det = A.det * (B.det)⁻¹ := by
    show (A * B⁻¹).det = A.det * (B.det)⁻¹
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  rw [hdetX2] at hdetX
  have hBne : B.det ≠ 0 := hB.ne_zero
  field_simp at hdetX
  exact hdetX

end Imc2015P1
