/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2004, Problem 7
(IMC 2004, Day 2, Problem 1)

Let `A` be a real `4 × 2` matrix and `B` a real `2 × 4` matrix such that
`A * B = ![![1, 0, -1, 0], ![0, 1, 0, -1], ![-1, 0, 1, 0], ![0, -1, 0, 1]]`.
Find `B * A`.

Answer: `B * A = !![2, 0; 0, 2] = 2 * I₂`.
-/

namespace Imc2004P7

open Matrix

/-- The given value of `A * B`. -/
def givenAB : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, -1, 0; 0, 1, 0, -1; -1, 0, 1, 0; 0, -1, 0, 1]

/-- The answer: `B * A = 2 • I₂`. -/
determine answer : Matrix (Fin 2) (Fin 2) ℝ := !![2, 0; 0, 2]

snip begin

/-
Strategy. Write `A = [[A₁],[A₂]]` (top and bottom `2 × 2` blocks) and
`B = [[B₁, B₂]]` (left and right `2 × 2` blocks).  The equation
`A * B = M` splits into:
  `A₁ B₁ = I₂`, `A₁ B₂ = -I₂`, `A₂ B₁ = -I₂`, `A₂ B₂ = I₂`.

From `A₁ B₁ = I₂` and Dedekind-finiteness of `2 × 2` matrices, `B₁ A₁ = I₂`.
Multiplying `A₂ B₁ = -I₂` on the right by `A₁` gives `A₂ = -A₁`; multiplying
`A₁ B₂ = -I₂` on the left by `B₁` gives `B₂ = -B₁`.  Then
`B * A = B₁ A₁ + B₂ A₂ = I₂ + B₁ A₁ = 2 I₂`.
-/

snip end

problem imc2004_p7
    (A : Matrix (Fin 4) (Fin 2) ℝ) (B : Matrix (Fin 2) (Fin 4) ℝ)
    (hAB : A * B = givenAB) :
    B * A = answer := by
  -- Define the four 2×2 blocks.
  let A₁ : Matrix (Fin 2) (Fin 2) ℝ := fun i j => A ⟨i.val, by omega⟩ j
  let A₂ : Matrix (Fin 2) (Fin 2) ℝ := fun i j => A ⟨i.val + 2, by omega⟩ j
  let B₁ : Matrix (Fin 2) (Fin 2) ℝ := fun i j => B i ⟨j.val, by omega⟩
  let B₂ : Matrix (Fin 2) (Fin 2) ℝ := fun i j => B i ⟨j.val + 2, by omega⟩
  -- Extract block equations from `A * B = givenAB`.
  have hA1B1 : A₁ * B₁ = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    have h : (A * B) ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ =
        givenAB ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ := by rw [hAB]
    have hprod : (A * B) ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ =
        (A₁ * B₁) i j := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, A₁, B₁]
    rw [hprod] at h
    rw [h]
    fin_cases i <;> fin_cases j <;>
      simp [givenAB]
  have hA1B2 : A₁ * B₂ = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    have h : (A * B) ⟨i.val, by omega⟩ ⟨j.val + 2, by omega⟩ =
        givenAB ⟨i.val, by omega⟩ ⟨j.val + 2, by omega⟩ := by rw [hAB]
    have hprod : (A * B) ⟨i.val, by omega⟩ ⟨j.val + 2, by omega⟩ =
        (A₁ * B₂) i j := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, A₁, B₂]
    rw [hprod] at h
    rw [h]
    fin_cases i <;> fin_cases j <;>
      simp [givenAB]
  have hA2B1 : A₂ * B₁ = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    have h : (A * B) ⟨i.val + 2, by omega⟩ ⟨j.val, by omega⟩ =
        givenAB ⟨i.val + 2, by omega⟩ ⟨j.val, by omega⟩ := by rw [hAB]
    have hprod : (A * B) ⟨i.val + 2, by omega⟩ ⟨j.val, by omega⟩ =
        (A₂ * B₁) i j := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, A₂, B₁]
    rw [hprod] at h
    rw [h]
    fin_cases i <;> fin_cases j <;>
      simp [givenAB]
  -- Dedekind-finiteness of `M₂(ℝ)`: from `A₁ B₁ = 1` we get `B₁ A₁ = 1`.
  have hB1A1 : B₁ * A₁ = (1 : Matrix (Fin 2) (Fin 2) ℝ) := mul_eq_one_comm.mp hA1B1
  -- Derive `A₂ = -A₁`: multiply `A₂ B₁ = -I` on the right by `A₁`.
  have hA2 : A₂ = -A₁ := by
    have h : A₂ * B₁ * A₁ = -A₁ := by rw [hA2B1]; simp
    rw [Matrix.mul_assoc, hB1A1, Matrix.mul_one] at h
    exact h
  -- Derive `B₂ = -B₁`: multiply `A₁ B₂ = -I` on the left by `B₁`.
  have hB2 : B₂ = -B₁ := by
    have h : B₁ * (A₁ * B₂) = -B₁ := by rw [hA1B2]; simp
    rw [← Matrix.mul_assoc, hB1A1, Matrix.one_mul] at h
    exact h
  -- Compute `B * A = B₁ * A₁ + B₂ * A₂ = 1 + B₁ * A₁ = 2 * 1`.
  have hBA : B * A = B₁ * A₁ + B₂ * A₂ := by
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_four, B₁, B₂, A₁, A₂]
    have h0 : (⟨0, by omega⟩ : Fin 4) = ⟨(0 : Fin 2).val, by omega⟩ := rfl
    have h1 : (⟨1, by omega⟩ : Fin 4) = ⟨(1 : Fin 2).val, by omega⟩ := rfl
    have h2 : (⟨2, by omega⟩ : Fin 4) = ⟨(0 : Fin 2).val + 2, by omega⟩ := rfl
    have h3 : (⟨3, by omega⟩ : Fin 4) = ⟨(1 : Fin 2).val + 2, by omega⟩ := rfl
    ring
  rw [hBA, hB2, hA2]
  have : (-B₁) * (-A₁) = B₁ * A₁ := by rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  rw [this, hB1A1]
  show (1 : Matrix (Fin 2) (Fin 2) ℝ) + 1 = !![2, 0; 0, 2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

end Imc2004P7
