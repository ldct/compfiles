/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2021, Problem 1

Let `A` be a real `n × n` matrix such that `A^3 = 0`.

(a) Prove that there is a unique real `n × n` matrix `X` satisfying
    `X + A * X + X * A^2 = A`.

(b) Express `X` in terms of `A`.

Answer: `X = A - A^2`.
-/

namespace Imc2021P1

open Matrix

/-- The answer to part (b): `X = A - A^2`. -/
determine answer {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  A - A ^ 2

snip begin

/-- Uniqueness: If `X + A * X + X * A^2 = A` and `A^3 = 0`, then `X = A - A^2`. -/
lemma unique_of_eq {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℝ) (hA : A ^ 3 = 0)
    (hX : X + A * X + X * A ^ 2 = A) : X = A - A ^ 2 := by
  -- Useful powers of A vanishing.
  have hA4 : A ^ 4 = 0 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, hA, Matrix.zero_mul]
  -- Step 1: multiply hX on the right by A^2.
  -- X A^2 + A X A^2 + X A^4 = A^3 = 0. Since A^4 = 0, X A^2 + A X A^2 = 0.
  have s1 : X * A ^ 2 + A * X * A ^ 2 = 0 := by
    have h := congrArg (· * A ^ 2) hX
    simp only at h
    rw [Matrix.add_mul, Matrix.add_mul] at h
    have e : X * A ^ 2 * A ^ 2 = X * A ^ 4 := by
      rw [Matrix.mul_assoc, ← pow_add]
    rw [e, hA4, Matrix.mul_zero, add_zero] at h
    have e' : A * A ^ 2 = A ^ 3 := by rw [← pow_succ']
    rw [e', hA] at h
    exact h
  -- Step 2: multiply hX on the left by A.
  -- AX + A^2 X + A X A^2 = A^2.
  have s2 : A * X + A ^ 2 * X + A * X * A ^ 2 = A ^ 2 := by
    have h := congrArg (A * ·) hX
    simp only at h
    rw [Matrix.mul_add, Matrix.mul_add] at h
    have e1 : A * (A * X) = A ^ 2 * X := by rw [← Matrix.mul_assoc, ← sq]
    have e2 : A * (X * A ^ 2) = A * X * A ^ 2 := by rw [← Matrix.mul_assoc]
    have e3 : A * A = A ^ 2 := (sq A).symm
    rw [e1, e2, e3] at h
    exact h
  -- Step 3: multiply s2 on the left by A.
  -- A^2 X + A^3 X + A^2 X A^2 = A^3 = 0.
  -- Since A^3 = 0, this becomes A^2 X + A^2 X A^2 = 0.
  have s3 : A ^ 2 * X + A ^ 2 * X * A ^ 2 = 0 := by
    have h := congrArg (A * ·) s2
    simp only at h
    rw [Matrix.mul_add, Matrix.mul_add] at h
    have e1 : A * (A * X) = A ^ 2 * X := by rw [← Matrix.mul_assoc, ← sq]
    have e2 : A * (A ^ 2 * X) = A ^ 3 * X := by
      rw [← Matrix.mul_assoc, ← pow_succ']
    have e3 : A * (A * X * A ^ 2) = A ^ 2 * X * A ^ 2 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← sq]
    have e4 : A * A ^ 2 = A ^ 3 := by rw [← pow_succ']
    rw [e1, e2, e3, e4, hA, Matrix.zero_mul] at h
    -- h : A^2 * X + 0 + A^2 * X * A^2 = 0
    linear_combination (norm := abel) h
  -- Also, multiply s1 on the left by A: A X A^2 + A^2 X A^2 = 0.
  have s1A : A * X * A ^ 2 + A ^ 2 * X * A ^ 2 = 0 := by
    have h := congrArg (A * ·) s1
    simp only at h
    rw [Matrix.mul_add, Matrix.mul_zero] at h
    have e1 : A * (X * A ^ 2) = A * X * A ^ 2 := by rw [← Matrix.mul_assoc]
    have e2 : A * (A * X * A ^ 2) = A ^ 2 * X * A ^ 2 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← sq]
    rw [e1, e2] at h
    exact h
  -- From s3: A^2 X A^2 = - A^2 X.
  -- From s1A: A X A^2 = - A^2 X A^2 = A^2 X.
  -- Substitute into s2: AX + A^2 X + A^2 X = A^2, i.e., AX + 2 A^2 X = A^2.
  -- Hmm, that isn't directly what we want. Let me redo the approach following the solution.
  --
  -- Per the official solution:
  --   From hX, multiply by A^2 on right: since A^3 = 0, we get X A^2 = 0... but wait,
  --   that's not right either. Let's be careful.
  --   (X + AX + XA^2) A^2 = A A^2 = A^3 = 0.
  --   LHS = X A^2 + A X A^2 + X A^4 = X A^2 + A X A^2 + 0 = X A^2 + A X A^2.
  --   So X A^2 + A X A^2 = 0. (This is s1.)
  -- Now multiply s1 on the right by A:
  --   X A^3 + A X A^3 = 0, which gives 0 = 0. Not useful.
  -- Following the official solution more carefully:
  --   "Multiply by A^2 right: XA^2 = A^3 = 0" — this claim in solution looks wrong.
  -- Let's use a cleaner path. Note that
  --   hX ⟹ X = A - AX - XA^2.
  -- Multiply X on the right by A^2:
  --   XA^2 = (A - AX - XA^2) A^2 = A^3 - AXA^2 - XA^4 = 0 - AXA^2 - 0 = -AXA^2.   (*)
  -- Multiply X on the left by A:
  --   AX = A(A - AX - XA^2) = A^2 - A^2 X - AXA^2.   (**)
  -- Multiply X on the left by A^2:
  --   A^2 X = A^2(A - AX - XA^2) = A^3 - A^3 X - A^2 X A^2 = -A^2 X A^2.   (***)
  -- Multiply (*) on the left by A:
  --   AXA^2 = -A^2 X A^2.   (****)
  -- Combining (***) and (****): A^2 X = AXA^2.
  -- From (*): XA^2 = -AXA^2 = -A^2 X.
  -- So XA^2 + A^2 X = 0.
  -- Substitute into hX: X + AX + XA^2 = A, so X + AX - A^2 X = A.  (◊)
  -- From (**): AX = A^2 - A^2 X - AXA^2 = A^2 - A^2 X - A^2 X = A^2 - 2 A^2 X.
  -- So ◊ becomes: X + A^2 - 2 A^2 X - A^2 X = A, i.e., X - 3 A^2 X = A - A^2.
  -- Multiply by A^2 on left: A^2 X - 3 A^4 X = A^3 - A^4 = 0. So A^2 X = 0.
  -- Then from ◊: X + AX = A. From (**): AX = A^2 - A^2 X - AXA^2 = A^2 - 0 - AXA^2.
  -- From (*): XA^2 = -AXA^2, and from above XA^2 = -A^2 X = 0, so AXA^2 = 0.
  -- So AX = A^2. Thus X = A - AX = A - A^2.
  --
  -- Formalize:
  -- Goal: X = A - A^2.
  have hA3R : A * A ^ 2 = 0 := by rw [← pow_succ', hA]
  have hA3L : A ^ 2 * A = 0 := by rw [← pow_succ, hA]
  -- Derive XA^2 = -AXA^2 (equation *).
  have eq_star : X * A ^ 2 = - (A * X * A ^ 2) := eq_neg_of_add_eq_zero_left s1
  -- Derive AX = A^2 - A^2 X - AXA^2 (equation **).
  have eq_sstar : A * X = A ^ 2 - A ^ 2 * X - A * X * A ^ 2 := by
    have h : A * X + A ^ 2 * X + A * X * A ^ 2 = A ^ 2 := s2
    linear_combination (norm := abel) h
  -- Derive A^2 X = - A^2 X A^2 (equation ***).
  have eq_3star : A ^ 2 * X = - (A ^ 2 * X * A ^ 2) := eq_neg_of_add_eq_zero_left s3
  -- Derive AXA^2 = -A^2 X A^2 (equation ****).
  have eq_4star : A * X * A ^ 2 = - (A ^ 2 * X * A ^ 2) := eq_neg_of_add_eq_zero_left s1A
  -- So A^2 X = A X A^2 (combining *** and ****).
  have eq_A2X : A ^ 2 * X = A * X * A ^ 2 := by
    rw [eq_3star, eq_4star]
  -- So X A^2 = - A^2 X (from * and eq_A2X).
  have eq_XA2 : X * A ^ 2 = - (A ^ 2 * X) := by
    rw [eq_star, eq_A2X]
  -- Substitute into hX: X + AX - A^2 X = A.
  have eq_dia : X + A * X - A ^ 2 * X = A := by
    have h : X + A * X + X * A ^ 2 = A := hX
    rw [eq_XA2] at h
    linear_combination (norm := abel) h
  -- Also AX = A^2 - 2 A^2 X (using ** and A X A^2 = A^2 X).
  have eq_AX : A * X = A ^ 2 - 2 • (A ^ 2 * X) := by
    have h := eq_sstar
    rw [← eq_A2X] at h
    rw [h, two_smul]
    abel
  -- So X - 3 A^2 X = A - A^2.
  have eq_main : X - 3 • (A ^ 2 * X) = A - A ^ 2 := by
    have h := eq_dia
    rw [eq_AX] at h
    -- h : X + (A^2 - 2•(A^2 X)) - A^2 X = A
    -- Want : X - 3•(A^2 X) = A - A^2
    have h3 : (3 : ℕ) • (A ^ 2 * X) = 2 • (A ^ 2 * X) + A ^ 2 * X := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, add_smul, one_smul]
    linear_combination (norm := (rw [h3]; abel)) h
  -- Multiply eq_main on the left by A^2 to conclude A^2 X = 0.
  have eq_A2X_zero : A ^ 2 * X = 0 := by
    have h := congrArg (A ^ 2 * ·) eq_main
    simp only at h
    have l1 : A ^ 2 * (X - 3 • (A ^ 2 * X)) = A ^ 2 * X - 3 • (A ^ 4 * X) := by
      rw [Matrix.mul_sub]
      congr 1
      rw [Matrix.mul_smul]
      congr 1
      rw [← Matrix.mul_assoc]
      congr 1
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
    have l2 : A ^ 2 * (A - A ^ 2) = A ^ 3 - A ^ 4 := by
      rw [Matrix.mul_sub, ← pow_succ]
      congr 1
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
    rw [l1, l2, hA, hA4] at h
    -- h : A^2 * X - 3 • (0 * X) = 0 - 0.
    rw [Matrix.zero_mul, smul_zero, sub_zero, sub_zero] at h
    exact h
  -- Now from eq_main: X = A - A^2.
  have final : X = A - A ^ 2 := by
    have := eq_main
    rw [eq_A2X_zero, smul_zero, sub_zero] at this
    exact this
  exact final

/-- Existence: `X = A - A^2` satisfies the equation when `A^3 = 0`. -/
lemma answer_satisfies {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ^ 3 = 0) :
    (A - A ^ 2) + A * (A - A ^ 2) + (A - A ^ 2) * A ^ 2 = A := by
  have hA4 : A ^ 4 = 0 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, hA, Matrix.zero_mul]
  have e1 : A * (A - A ^ 2) = A ^ 2 - A ^ 3 := by
    rw [Matrix.mul_sub]
    congr 1
    · rw [← sq]
    · rw [← pow_succ']
  have e2 : (A - A ^ 2) * A ^ 2 = A ^ 3 - A ^ 4 := by
    rw [Matrix.sub_mul]
    congr 1
    · rw [← pow_succ']
    · rw [← pow_add]
  rw [e1, e2, hA, hA4]
  abel

snip end

problem imc2021_p1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ^ 3 = 0) :
    ∃! X : Matrix (Fin n) (Fin n) ℝ,
      X + A * X + X * A ^ 2 = A ∧ X = answer A := by
  refine ⟨answer A, ⟨?_, rfl⟩, ?_⟩
  · show (A - A ^ 2) + A * (A - A ^ 2) + (A - A ^ 2) * A ^ 2 = A
    exact answer_satisfies A hA
  · rintro Y ⟨hY, -⟩
    show Y = A - A ^ 2
    exact unique_of_eq A Y hA hY

end Imc2021P1
