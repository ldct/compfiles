/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2005, Problem 1

Let `A` be the `n × n` matrix with `(i, j)`-entry `i + j` (with `1`-based
indexing). Find `rank(A)`.

Answer: `min n 2`, which evaluates to `0` for `n = 0`, `1` for `n = 1`,
and `2` for `n ≥ 2`.
-/

namespace Imc2005P1

open Matrix

/-- The matrix `A : Matrix (Fin n) (Fin n) ℝ` with `(i,j)`-entry `(i+1)+(j+1)`
(matching `1`-based indexing of the original problem). -/
def matA (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ((i.val + 1 : ℕ) : ℝ) + ((j.val + 1 : ℕ) : ℝ)

/-- The answer: `min n 2`. -/
determine answer (n : ℕ) : ℕ := min n 2

snip begin

/-- The all-ones vector in `Fin n → ℝ`. -/
def onesVec (n : ℕ) : Fin n → ℝ := fun _ => 1

/-- The "index" vector `i ↦ i + 1`. -/
def idxVec (n : ℕ) : Fin n → ℝ := fun i => (i.val + 1 : ℕ)

/-- Each column of `matA n` equals `idxVec n + (j+1) • onesVec n`. -/
lemma matA_col (n : ℕ) (j : Fin n) :
    (matA n).col j = idxVec n + ((j.val + 1 : ℕ) : ℝ) • onesVec n := by
  ext i
  simp [matA, col_apply, idxVec, onesVec]

/-- The column span of `matA n` is contained in the span of `{onesVec n, idxVec n}`. -/
lemma col_span_le (n : ℕ) :
    Submodule.span ℝ (Set.range (matA n).col) ≤
      Submodule.span ℝ ({onesVec n, idxVec n} : Set (Fin n → ℝ)) := by
  rw [Submodule.span_le]
  rintro v ⟨j, rfl⟩
  rw [matA_col]
  refine Submodule.add_mem _ ?_ ?_
  · exact Submodule.subset_span (by simp)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/-- Rank of `matA n` is at most `2`. -/
lemma rank_matA_le_two (n : ℕ) : (matA n).rank ≤ 2 := by
  rw [rank_eq_finrank_span_cols]
  have h := col_span_le n
  classical
  -- span of 2 vectors has finrank ≤ 2
  have hfin_le : Module.finrank ℝ
      (Submodule.span ℝ ({onesVec n, idxVec n} : Set (Fin n → ℝ))) ≤ 2 := by
    have hspan_eq : (Submodule.span ℝ ({onesVec n, idxVec n} : Set (Fin n → ℝ))) =
        Submodule.span ℝ (({onesVec n, idxVec n} : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
      congr 1
      ext v; simp
    rw [hspan_eq]
    calc Module.finrank ℝ (Submodule.span ℝ
            (({onesVec n, idxVec n} : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)))
        ≤ ({onesVec n, idxVec n} : Finset (Fin n → ℝ)).card :=
          finrank_span_finset_le_card _
      _ ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  exact (Submodule.finrank_mono h).trans hfin_le

/-- The top-left `2 × 2` submatrix of `matA n` for `n ≥ 2` equals the matrix
`[[2, 3], [3, 4]]`. -/
lemma submatrix_2x2 (n : ℕ) (hn : 2 ≤ n) :
    (matA n).submatrix
      (fun k : Fin 2 => (⟨k.val, by omega⟩ : Fin n))
      (fun k : Fin 2 => (⟨k.val, by omega⟩ : Fin n)) =
    !![2, 3; 3, 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matA, Matrix.submatrix_apply] <;> norm_num

/-- Determinant of `!![2, 3; 3, 4]` is `-1`, hence nonzero. -/
lemma det_block : Matrix.det (!![(2 : ℝ), 3; 3, 4]) = -1 := by
  rw [Matrix.det_fin_two_of]
  ring

/-- Rank of `matA n` is at least `2` for `n ≥ 2`. -/
lemma rank_matA_ge_two (n : ℕ) (hn : 2 ≤ n) : 2 ≤ (matA n).rank := by
  -- Use that the submatrix has full rank 2.
  set r : Fin 2 → Fin n := fun k => ⟨k.val, by omega⟩ with hr
  set c : Fin 2 → Fin n := fun k => ⟨k.val, by omega⟩ with hc
  have hsub : (matA n).submatrix r c = !![(2 : ℝ), 3; 3, 4] := submatrix_2x2 n hn
  have hdet : ((matA n).submatrix r c).det ≠ 0 := by
    rw [hsub, det_block]; norm_num
  have hunit : IsUnit ((matA n).submatrix r c).det := by
    rw [hsub, det_block]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  have hmat_unit : IsUnit ((matA n).submatrix r c) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hunit
  have hsub_rank : ((matA n).submatrix r c).rank = 2 := by
    rw [Matrix.rank_of_isUnit _ hmat_unit, Fintype.card_fin]
  have hrank_le : ((matA n).submatrix r c).rank ≤ (matA n).rank :=
    Matrix.rank_submatrix_le _ r c
  omega

/-- For `n = 1`: The matrix is `[[2]]`, with rank 1. -/
lemma rank_matA_one : (matA 1).rank = 1 := by
  -- matA 1 has a single entry, value 2 ≠ 0.
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  -- Use det to verify rank via isUnit.
  have hdet : (matA 1).det = 2 := by
    rw [show matA 1 = !![(2 : ℝ)] from ?_]
    · rw [Matrix.det_fin_one]; simp
    · ext i j
      fin_cases i; fin_cases j
      simp [matA]; norm_num
  have hunit : IsUnit (matA 1).det := by rw [hdet]; exact isUnit_iff_ne_zero.mpr h2ne
  have hmat_unit : IsUnit (matA 1) := (Matrix.isUnit_iff_isUnit_det _).mpr hunit
  rw [Matrix.rank_of_isUnit _ hmat_unit, Fintype.card_fin]

/-- For `n = 0`: rank is 0. -/
lemma rank_matA_zero : (matA 0).rank = 0 := by
  have h : matA 0 = 0 := by ext i; exact i.elim0
  rw [h, Matrix.rank_zero]

snip end

problem imc2005_p1 (n : ℕ) : (matA n).rank = answer n := by
  rw [answer]
  match n, Nat.lt_or_ge n 2 with
  | 0, _ => simp [rank_matA_zero]
  | 1, _ => simp [rank_matA_one]
  | (k + 2), _ =>
    have hle := rank_matA_le_two (k + 2)
    have hge := rank_matA_ge_two (k + 2) (by omega)
    have : (matA (k + 2)).rank = 2 := le_antisymm hle hge
    rw [this]
    simp

end Imc2005P1
