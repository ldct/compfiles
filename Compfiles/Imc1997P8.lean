/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1997, Problem 8 (Day 2, Problem 2)

Let `M` be a `2n × 2n` invertible block matrix
`M = fromBlocks A B C D`
where `A, B, C, D` are `n × n` matrices, and let
`M⁻¹ = fromBlocks E F G H`.
Prove that `det M · det H = det A`.

## Solution outline (official)

Consider the product
  `M · fromBlocks 1 F 0 H`.
Using `fromBlocks_multiply` this equals
  `fromBlocks A (A·F + B·H) C (C·F + D·H)`.
But the right column of `M · M⁻¹ = I` says `A·F + B·H = 0` and `C·F + D·H = I`,
so the product equals `fromBlocks A 0 C 1`. Taking determinants and using
the upper-triangular block determinant formula on both sides gives
  `det M · det H = det A · det 1 = det A`.
-/

namespace Imc1997P8

open Matrix

problem imc1997_p8 {n : ℕ} {R : Type*} [CommRing R]
    (A B C D E F G H : Matrix (Fin n) (Fin n) R)
    (hM : (fromBlocks A B C D) * (fromBlocks E F G H) = 1) :
    (fromBlocks A B C D).det * H.det = A.det := by
  -- Right column of M * M⁻¹ = I gives A*F + B*H = 0 and C*F + D*H = 1.
  have hmul : (fromBlocks A B C D) * (fromBlocks (1 : Matrix (Fin n) (Fin n) R) F 0 H)
      = fromBlocks A 0 C 1 := by
    rw [fromBlocks_multiply]
    -- Now we need to derive: A*1 + B*0 = A, A*F + B*H = 0, C*1 + D*0 = C, C*F + D*H = 1.
    -- The middle two come from hM.
    -- Compare hM (which is M * M⁻¹ = I = fromBlocks 1 0 0 1).
    have h1 : fromBlocks (A * E + B * G) (A * F + B * H) (C * E + D * G) (C * F + D * H)
        = fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 1 := by
      rw [← fromBlocks_multiply]
      rw [hM]
      ext (i | i) (j | j) <;> simp [fromBlocks, one_apply]
    -- Extract the four block equalities from h1.
    have hAF : A * F + B * H = 0 := by
      have := (fromBlocks_inj.mp h1).2.1
      exact this
    have hCF : C * F + D * H = 1 := by
      have := (fromBlocks_inj.mp h1).2.2.2
      exact this
    -- Now simplify the LHS of the goal.
    rw [Matrix.mul_one, Matrix.mul_zero, Matrix.mul_zero, Matrix.mul_one,
        add_zero, add_zero, hAF, hCF]
  -- Take determinants of both sides.
  have hdet : ((fromBlocks A B C D) * (fromBlocks (1 : Matrix (Fin n) (Fin n) R) F 0 H)).det
      = (fromBlocks A 0 C (1 : Matrix (Fin n) (Fin n) R)).det := by
    rw [hmul]
  rw [Matrix.det_mul] at hdet
  -- det of upper-triangular block: det (fromBlocks 1 F 0 H) = det 1 * det H = det H.
  rw [show (fromBlocks (1 : Matrix (Fin n) (Fin n) R) F 0 H).det = H.det by
        rw [det_fromBlocks_zero₂₁, det_one, one_mul]] at hdet
  -- det of lower-triangular block: det (fromBlocks A 0 C 1) = det A * det 1 = det A.
  -- Use the symmetric version via transpose.
  rw [show (fromBlocks A (0 : Matrix (Fin n) (Fin n) R) C 1).det = A.det by
        rw [det_fromBlocks_zero₁₂, det_one, mul_one]] at hdet
  exact hdet


end Imc1997P8
