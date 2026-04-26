/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2003, Problem 7
(IMC 2003, Day 2, Problem 1)

Let `A` and `B` be real `n × n` matrices satisfying `A * B + A + B = 0`.
Prove that `A * B = B * A`.
-/

namespace Imc2003P7

open Matrix

snip begin

/-
Key identity: `(A + 1) * (B + 1) = A * B + A + B + 1`, so if
`A * B + A + B = 0`, then `(A + 1) * (B + 1) = 1`. Since the matrix
ring is Dedekind-finite, this implies `(B + 1) * (A + 1) = 1`, which
expands to `B * A + A + B + 1 = 1`, i.e. `B * A + A + B = 0`. Hence
`A * B = B * A`.
-/

snip end

problem imc2003_p7 {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (h : A * B + A + B = 0) :
    A * B = B * A := by
  -- Step 1: (A + 1) * (B + 1) = 1.
  have h1 : (A + 1) * (B + 1) = 1 := by
    have key : (A + 1) * (B + 1) = A * B + A + B + 1 := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_mul,
          Matrix.mul_one, Matrix.one_mul, Matrix.one_mul]
      abel
    rw [key, h, zero_add]
  -- Step 2: (B + 1) * (A + 1) = 1, by Dedekind-finiteness of the matrix ring.
  have h2 : (B + 1) * (A + 1) = 1 := mul_eq_one_comm.mp h1
  -- Step 3: Expand h2 to get B * A + A + B = 0.
  have key2 : (B + 1) * (A + 1) = B * A + A + B + 1 := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_mul,
        Matrix.mul_one, Matrix.one_mul, Matrix.one_mul]
    abel
  rw [key2] at h2
  -- h2 : B * A + A + B + 1 = 1, so B * A + A + B = 0.
  have h3 : B * A + A + B = 0 := by
    have h2' : B * A + A + B + 1 = 0 + 1 := by rw [zero_add]; exact h2
    exact add_right_cancel h2'
  -- Conclude A * B = B * A from h - h3.
  have h4 : A * B + A + B = B * A + A + B := h.trans h3.symm
  have h5 : A * B = B * A := by
    have := h4
    -- Cancel B on the right, then A on the right.
    have e1 : A * B + A = B * A + A := add_right_cancel this
    exact add_right_cancel e1
  exact h5

end Imc2003P7
