/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2011, Problem 2

Does there exist a real `3 × 3` matrix `A` with `tr(A) = 0` and `A² + Aᵀ = I`?

Answer: No.

## Solution

Assume such `A` exists. Taking trace of `A² + Aᵀ = I` gives `tr(A²) = 3`. Transposing
yields `A = I - (Aᵀ)²`, and substituting `Aᵀ = I - A²` gives `A⁴ - 2A² + A = 0`, but
more directly one can compute `tr(A⁴) = 6` via `A⁴ = (I - Aᵀ)²`. On the other hand,
Cayley-Hamilton applied to `A` with `tr(A) = 0, tr(A²) = 3` yields
`tr(A⁴) = -e₂ · tr(A²) = (3/2) · 3 = 9/2`, a contradiction.
-/

namespace Imc2011P2

open Matrix Polynomial

snip begin

/-- Sum of the 2×2 principal minors of a 3×3 matrix. -/
private def e2 {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) : R :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0 +
    (M 0 0 * M 2 2 - M 0 2 * M 2 0) +
    (M 1 1 * M 2 2 - M 1 2 * M 2 1)

/-- The characteristic polynomial of a 3×3 matrix, explicitly. -/
private lemma charpoly_fin_three' {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) :
    M.charpoly = X ^ 3 - C M.trace * X ^ 2 + C (e2 M) * X - C M.det := by
  unfold Matrix.charpoly
  rw [det_fin_three]
  rw [show charmatrix M 0 0 = X - C (M 0 0) from charmatrix_apply_eq M 0,
      show charmatrix M 1 1 = X - C (M 1 1) from charmatrix_apply_eq M 1,
      show charmatrix M 2 2 = X - C (M 2 2) from charmatrix_apply_eq M 2,
      show charmatrix M 0 1 = - C (M 0 1) from charmatrix_apply_ne M _ _ (by decide),
      show charmatrix M 0 2 = - C (M 0 2) from charmatrix_apply_ne M _ _ (by decide),
      show charmatrix M 1 0 = - C (M 1 0) from charmatrix_apply_ne M _ _ (by decide),
      show charmatrix M 1 2 = - C (M 1 2) from charmatrix_apply_ne M _ _ (by decide),
      show charmatrix M 2 0 = - C (M 2 0) from charmatrix_apply_ne M _ _ (by decide),
      show charmatrix M 2 1 = - C (M 2 1) from charmatrix_apply_ne M _ _ (by decide)]
  rw [trace_fin_three, det_fin_three]
  simp only [e2, map_add, map_sub, map_mul]
  ring

/-- Cayley-Hamilton for a 3×3 matrix, in explicit form. -/
private lemma cayley_hamilton_fin_three' {R : Type*} [CommRing R]
    (M : Matrix (Fin 3) (Fin 3) R) :
    M ^ 3 - M.trace • M ^ 2 + e2 M • M - M.det • (1 : Matrix (Fin 3) (Fin 3) R) = 0 := by
  have h := Matrix.aeval_self_charpoly M
  rw [charpoly_fin_three'] at h
  -- aeval at M: X ↦ M, C r ↦ r • 1.
  simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one] at h
  -- h : M ^ 3 - M.trace • 1 * M ^ 2 + e2 M • 1 * M - M.det • 1 = 0
  have h1 : (M.trace • (1 : Matrix (Fin 3) (Fin 3) R)) * M ^ 2 = M.trace • M ^ 2 := by
    rw [Matrix.smul_mul, Matrix.one_mul]
  have h2 : (e2 M • (1 : Matrix (Fin 3) (Fin 3) R)) * M = e2 M • M := by
    rw [Matrix.smul_mul, Matrix.one_mul]
  rw [h1, h2] at h
  exact h

/-- Trace form of Cayley-Hamilton for 3×3: multiply by `M` and take trace. -/
private lemma trace_pow_four_fin_three {R : Type*} [CommRing R]
    (M : Matrix (Fin 3) (Fin 3) R) :
    (M ^ 4).trace = M.trace * (M ^ 3).trace - e2 M * (M ^ 2).trace + M.det * M.trace := by
  -- Multiply Cayley-Hamilton by M and take trace.
  have h := cayley_hamilton_fin_three' M
  have h' : M * (M ^ 3 - M.trace • M ^ 2 + e2 M • M - M.det • (1 : Matrix (Fin 3) (Fin 3) R))
              = M * 0 := by rw [h]
  rw [Matrix.mul_zero] at h'
  rw [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.mul_one] at h'
  -- h' : M * M ^ 3 - M.trace • (M * M ^ 2) + e2 M • (M * M) - M.det • M = 0
  have hpow4 : M * M ^ 3 = M ^ 4 := by rw [← pow_succ']
  have hpow3 : M * M ^ 2 = M ^ 3 := by rw [← pow_succ']
  have hpow2 : M * M = M ^ 2 := by rw [sq]
  rw [hpow4, hpow3, hpow2] at h'
  -- Take trace
  have ht := congrArg Matrix.trace h'
  rw [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
      Matrix.trace_smul, Matrix.trace_zero] at ht
  simp only [smul_eq_mul] at ht
  linear_combination ht

snip end

/-- The answer to the problem: No such matrix exists. -/
determine answer : Prop := False

problem imc2011_p2 :
    answer ↔
    ∃ A : Matrix (Fin 3) (Fin 3) ℝ, A.trace = 0 ∧ A ^ 2 + Aᵀ = 1 := by
  show False ↔ _
  refine ⟨False.elim, ?_⟩
  rintro ⟨A, htr, hA⟩
  have hcard : Fintype.card (Fin 3) = 3 := Fintype.card_fin 3
  -- Step 1: tr(A²) = 3.
  have hAsq_tr : (A ^ 2).trace = 3 := by
    have h1 := congrArg Matrix.trace hA
    rw [Matrix.trace_add, Matrix.trace_transpose, htr, add_zero, Matrix.trace_one, hcard] at h1
    exact_mod_cast h1
  -- Step 2: (Aᵀ)² = (A²)ᵀ, so tr((Aᵀ)²) = tr(A²) = 3.
  have hATsq_tr : ((Aᵀ) ^ 2).trace = 3 := by
    have h1 : (Aᵀ) ^ 2 = (A ^ 2)ᵀ := by
      rw [sq, sq, Matrix.transpose_mul]
    rw [h1, Matrix.trace_transpose]
    exact hAsq_tr
  -- Step 3: A² = 1 - Aᵀ (from hA).
  have hAsq : A ^ 2 = 1 - Aᵀ := by
    have := hA
    linear_combination (norm := noncomm_ring) this
  -- Step 4: A⁴ = (A²)² = (1 - Aᵀ)² = 1 - 2·Aᵀ + (Aᵀ)².
  have hA4 : A ^ 4 = 1 - 2 • (Aᵀ) + (Aᵀ) ^ 2 := by
    have h1 : A ^ 4 = (A ^ 2) * (A ^ 2) := by rw [← pow_add]
    rw [h1, hAsq]
    have h2 : (1 - Aᵀ) * (1 - Aᵀ) = 1 - Aᵀ - Aᵀ + Aᵀ * Aᵀ := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
          Matrix.one_mul]
      abel
    rw [h2, sq]
    rw [show (2 : ℕ) • (Aᵀ) = Aᵀ + Aᵀ from by
      rw [two_smul]]
    abel
  -- Step 5: tr(A⁴) = 3 - 0 + 3 = 6.
  have hA4_tr : (A ^ 4).trace = 6 := by
    have h := congrArg Matrix.trace hA4
    rw [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_one, hcard,
        Matrix.trace_smul, Matrix.trace_transpose, htr] at h
    rw [h, hATsq_tr]
    push_cast; ring
  -- Step 6: By Cayley-Hamilton applied to A with tr(A) = 0:
  -- tr(A⁴) = 0 - e₂(A) · tr(A²) + det(A) · 0 = -3 e₂(A).
  -- Newton: tr(A²) = tr(A)² - 2 e₂(A), so e₂(A) = -3/2. Hence tr(A⁴) = 9/2.
  have h_e2_eq : e2 A = -3 / 2 := by
    -- Using tr(A) = 0 and tr(A²) = 3.
    -- tr(A²) = Σ A_ij A_ji.
    -- Newton: 2 e₂ = tr(A)² - tr(A²).
    have htr_expand : A.trace = A 0 0 + A 1 1 + A 2 2 := trace_fin_three A
    have hAsq_expand : (A * A).trace = A 0 0 * A 0 0 + A 0 1 * A 1 0 + A 0 2 * A 2 0 +
        (A 1 0 * A 0 1 + A 1 1 * A 1 1 + A 1 2 * A 2 1) +
        (A 2 0 * A 0 2 + A 2 1 * A 1 2 + A 2 2 * A 2 2) := by
      simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_three]
    have h1 : A 0 0 + A 1 1 + A 2 2 = 0 := by rw [← htr_expand]; exact htr
    have h2 : (A ^ 2).trace = (A * A).trace := by rw [sq]
    have h3 : A 0 0 * A 0 0 + A 0 1 * A 1 0 + A 0 2 * A 2 0 +
        (A 1 0 * A 0 1 + A 1 1 * A 1 1 + A 1 2 * A 2 1) +
        (A 2 0 * A 0 2 + A 2 1 * A 1 2 + A 2 2 * A 2 2) = 3 := by
      rw [← hAsq_expand, ← h2]; exact hAsq_tr
    unfold e2
    nlinarith [h1, h3, sq_nonneg (A 0 0 + A 1 1 + A 2 2)]
  -- Apply trace_pow_four_fin_three.
  have hTr4 := trace_pow_four_fin_three A
  rw [htr, h_e2_eq, hAsq_tr, hA4_tr] at hTr4
  -- hTr4 : 6 = 0 * _ - (-3/2) * 3 + A.det * 0
  linarith

end Imc2011P2
