/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Normed

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2003, Problem 3
(IMC 2003, Day 1, Problem 3)

Let `A` be a real `n × n` matrix such that `3 * A^3 = A^2 + A + I`.
Prove that the sequence `A^k` converges to an idempotent matrix.
-/

namespace Imc2003P3

open Filter Topology Matrix

problem imc2003_p3 {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : (3 : ℝ) • A ^ 3 = A ^ 2 + A + 1) :
    ∃ P : Matrix n n ℝ, IsIdempotentElem P ∧
      Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 P) := by
  -- The minimal polynomial of A divides (x-1)(3x^2 + 2x + 1).
  -- By Bezout, there exist polynomials u, v with
  --   u(x) * (x - 1) + v(x) * (3x^2 + 2x + 1) = 1.
  -- Let P := v(A) * (3A^2 + 2A + I) and Q := u(A) * (A - I).
  -- Then P + Q = I, and P * Q = u(A) * v(A) * (3A^3 - A^2 - A - I) = 0,
  -- so P and Q are complementary idempotents.
  -- A * P = P (since (A - I) * P = 0), hence A^k * P = P for all k ≥ 1.
  -- On the image of Q, A satisfies 3A^2 + 2A + I = 0, whose roots have
  -- modulus 1/sqrt(3) < 1. Hence (A * Q)^k → 0.
  -- Therefore A^k = A^k * (P + Q) = P + (A * Q)^k → P.
  -- TODO: The full formalization requires spectral radius / power sequence
  -- analysis over matrices. This is left as future work.
  sorry

end Imc2003P3
