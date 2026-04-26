/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2009, Problem 2

Let `A, B, C` be real square matrices of the same size, with `A` invertible.
Prove that if `(A - B) * C = B * A⁻¹`, then `C * (A - B) = A⁻¹ * B`.
-/

namespace Imc2009P2

open Matrix

problem imc2009_p2 {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsUnit A) (h : (A - B) * C = B * A⁻¹) :
    C * (A - B) = A⁻¹ * B := by
  rw [Matrix.isUnit_iff_isUnit_det] at hA
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have hA'inv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  -- From `(A - B) * C = B * A⁻¹`, derive `(A - B) * (C + A⁻¹) = 1`.
  have h1 : (A - B) * (C + A⁻¹) = 1 := by
    rw [Matrix.mul_add, h, Matrix.sub_mul, hAinv]
    abel
  -- Since the matrix ring is Dedekind-finite, left inverse = right inverse.
  have h2 : (C + A⁻¹) * (A - B) = 1 := mul_eq_one_comm.mp h1
  -- Expand: `C * (A - B) + A⁻¹ * (A - B) = 1`.
  have h3 : C * (A - B) + A⁻¹ * (A - B) = 1 := by
    rw [← Matrix.add_mul]; exact h2
  -- `A⁻¹ * (A - B) = 1 - A⁻¹ * B`.
  have h4 : A⁻¹ * (A - B) = 1 - A⁻¹ * B := by
    rw [Matrix.mul_sub, hA'inv]
  rw [h4] at h3
  -- `h3 : C * (A - B) + (1 - A⁻¹ * B) = 1`.
  -- Subtract `1 - A⁻¹ * B` from both sides.
  have h5 : C * (A - B) = 1 - (1 - A⁻¹ * B) := eq_sub_of_add_eq h3
  rw [h5]; abel

end Imc2009P2
