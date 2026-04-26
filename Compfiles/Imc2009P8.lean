/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2009, Problem 8
(Day 2, Problem 3)

Let `A, B ∈ M_n(ℂ)` with `A^2 B + B A^2 = 2 A B A`. Prove that there exists a
positive integer `k` such that `(AB - BA)^k = 0`.
-/

namespace Imc2009P8

open Matrix

snip begin

/-- If `M` is a complex matrix with `trace (M^k) = 0` for all `k ≥ 1`, then `M` is
nilpotent. This uses Newton's identities connecting power sums to elementary symmetric
polynomials, then Cayley–Hamilton. -/
lemma isNilpotent_of_forall_trace_pow_eq_zero
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (htr : ∀ k : ℕ, 1 ≤ k → (M ^ k).trace = 0) :
    IsNilpotent M := by
  -- TODO: complete via Newton's identities on charpoly roots over ℂ.
  sorry

snip end

problem imc2009_p8
    {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hAB : A * A * B + B * (A * A) = 2 • (A * B * A)) :
    IsNilpotent (A * B - B * A) := by
  set X : Matrix (Fin n) (Fin n) ℂ := A * B - B * A with hX_def
  -- Step 1: A * X = X * A.
  have hAX : A * X = X * A := by
    have hexp : A * X - X * A = A * A * B + B * (A * A) - 2 • (A * B * A) := by
      simp only [hX_def, two_smul]
      rw [Matrix.mul_sub, Matrix.sub_mul]
      rw [show A * (A * B) = A * A * B from (Matrix.mul_assoc _ _ _).symm]
      rw [show B * A * A = B * (A * A) from Matrix.mul_assoc _ _ _]
      rw [show A * (B * A) = A * B * A from (Matrix.mul_assoc _ _ _).symm]
      abel
    have hzero : A * X - X * A = 0 := by rw [hexp, hAB]; abel
    exact sub_eq_zero.mp hzero
  -- Step 2: A * X^m = X^m * A for all m.
  have hAXm : ∀ m : ℕ, A * X ^ m = X ^ m * A := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, hAX, ← Matrix.mul_assoc]
  -- Step 3: trace (X^m) = 0 for all m ≥ 1.
  have htrX : ∀ m : ℕ, 1 ≤ m → (X ^ m).trace = 0 := by
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    -- X^(k+1) = X^k * X = X^k (AB - BA) = X^k A B - X^k B A = A X^k B - X^k B A.
    have h1 : X ^ (k + 1) = A * X ^ k * B - X ^ k * B * A := by
      rw [pow_succ, hX_def]
      rw [Matrix.mul_sub]
      congr 1
      · rw [show X ^ k * (A * B) = X ^ k * A * B from (Matrix.mul_assoc _ _ _).symm,
            hAXm k]
      · rw [show X ^ k * (B * A) = X ^ k * B * A from (Matrix.mul_assoc _ _ _).symm]
    rw [h1, Matrix.trace_sub]
    -- trace(A * X^k * B) = trace(B * A * X^k) = trace(X^k * B * A) by cyclicity.
    rw [Matrix.trace_mul_cycle A (X ^ k) B]
    -- Goal: (B * A * X ^ k).trace - (X ^ k * B * A).trace = 0
    -- (X^k * B * A).trace = (X^k * (B * A)).trace = ((B * A) * X^k).trace = (B * A * X^k).trace
    rw [show X ^ k * B * A = X ^ k * (B * A) from Matrix.mul_assoc _ _ _]
    rw [Matrix.trace_mul_comm (X ^ k) (B * A)]
    ring
  -- Step 4: X is nilpotent.
  exact isNilpotent_of_forall_trace_pow_eq_zero X htrX

end Imc2009P8
