/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.Mul

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2012, Problem 2

Let `n` be a fixed positive integer. Determine the smallest possible rank
of an `n × n` matrix that has zeros along the main diagonal and strictly
positive real numbers off the main diagonal.

Answer:
- `n = 1`: rank `0`.
- `n = 2`: rank `2`.
- `n ≥ 3`: rank `3`.
-/

namespace Imc2012P2

open Matrix

/-- The condition: zero along the main diagonal, strictly positive off the diagonal. -/
def IsZeroDiagPos {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i, M i i = 0) ∧ (∀ i j, i ≠ j → 0 < M i j)

determine answer (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else if n = 2 then 2 else 3

snip begin

/-- For `n = 0` or `n = 1`, the zero matrix has rank `0` and trivially satisfies the conditions
(off-diagonal entries are vacuously positive). -/
lemma example_zero (n : ℕ) (hn : n ≤ 1) :
    ∃ M : Matrix (Fin n) (Fin n) ℝ, IsZeroDiagPos M ∧ Matrix.rank M = 0 := by
  refine ⟨0, ⟨fun _ => rfl, ?_⟩, ?_⟩
  · intro i j hij
    interval_cases n
    · exact (Fin.elim0 i)
    · exact absurd (Subsingleton.elim i j) hij
  · exact Matrix.rank_zero

/-- For `n = 2`, take the matrix `![![0, 1], ![1, 0]]`. -/
lemma example_two : ∃ M : Matrix (Fin 2) (Fin 2) ℝ,
    IsZeroDiagPos M ∧ Matrix.rank M ≤ 2 := by
  refine ⟨!![0, 1; 1, 0], ⟨?_, ?_⟩, ?_⟩
  · intro i; fin_cases i <;> rfl
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · exact (Matrix.rank_le_card_width _).trans (by simp)

/-- For `n = 2`, lower bound. The 2×2 matrix `![![0, a], ![b, 0]]` with `a, b > 0`
has nonzero determinant `-ab`, so it has full rank `2`. -/
lemma rank_ge_of_two {M : Matrix (Fin 2) (Fin 2) ℝ} (h : IsZeroDiagPos M) :
    2 ≤ Matrix.rank M := by
  obtain ⟨hdiag, hpos⟩ := h
  -- The determinant is M 0 0 * M 1 1 - M 0 1 * M 1 0 = -M 0 1 * M 1 0 < 0.
  have h00 : M 0 0 = 0 := hdiag 0
  have h11 : M 1 1 = 0 := hdiag 1
  have h01 : 0 < M 0 1 := hpos 0 1 (by decide)
  have h10 : 0 < M 1 0 := hpos 1 0 (by decide)
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_fin_two, h00, h11]
    have : M 0 1 * M 1 0 > 0 := mul_pos h01 h10
    nlinarith
  have hunit : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hrank : Matrix.rank M = Fintype.card (Fin 2) := Matrix.rank_of_isUnit M hunit
  rw [hrank]; simp

/-- The first three rows of any matrix with zero diagonal and positive off-diagonal entries
are linearly independent.  Restrict a relation `c₀ r₀ + c₁ r₁ + c₂ r₂ = 0` to columns 0, 1, 2:
this gives three sign constraints implying all `cᵢ = 0`. -/
lemma three_rows_linearIndependent {n : ℕ} (hn : 3 ≤ n)
    (M : Matrix (Fin n) (Fin n) ℝ) (h : IsZeroDiagPos M) :
    LinearIndependent ℝ (fun i : Fin 3 => M ⟨i.val, by omega⟩) := by
  obtain ⟨hdiag, hpos⟩ := h
  rw [Fintype.linearIndependent_iff]
  intro c hsum
  -- For each j, ∑ i, c i * M ⟨i.val, _⟩ j = 0.
  have heq : ∀ j : Fin n, ∑ i : Fin 3, c i * M ⟨i.val, by omega⟩ j = 0 := by
    intro j
    have := congrFun hsum j
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
  -- Apply at columns 0, 1, 2.
  have h0 := heq ⟨0, by omega⟩
  have h1 := heq ⟨1, by omega⟩
  have h2 := heq ⟨2, by omega⟩
  -- Diagonal entries vanish.
  have d00 : M ⟨0, by omega⟩ ⟨0, by omega⟩ = 0 := hdiag _
  have d11 : M ⟨1, by omega⟩ ⟨1, by omega⟩ = 0 := hdiag _
  have d22 : M ⟨2, by omega⟩ ⟨2, by omega⟩ = 0 := hdiag _
  -- Positive off-diagonals.
  have p10 : 0 < M ⟨1, by omega⟩ ⟨0, by omega⟩ := hpos _ _ (by simp [Fin.ext_iff])
  have p20 : 0 < M ⟨2, by omega⟩ ⟨0, by omega⟩ := hpos _ _ (by simp [Fin.ext_iff])
  have p01 : 0 < M ⟨0, by omega⟩ ⟨1, by omega⟩ := hpos _ _ (by simp [Fin.ext_iff])
  have p21 : 0 < M ⟨2, by omega⟩ ⟨1, by omega⟩ := hpos _ _ (by simp [Fin.ext_iff])
  have p02 : 0 < M ⟨0, by omega⟩ ⟨2, by omega⟩ := hpos _ _ (by simp [Fin.ext_iff])
  have p12 : 0 < M ⟨1, by omega⟩ ⟨2, by omega⟩ := hpos _ _ (by simp [Fin.ext_iff])
  simp [Fin.sum_univ_three, d00, d11, d22] at h0 h1 h2
  set a01 := M ⟨0, by omega⟩ ⟨1, by omega⟩
  set a02 := M ⟨0, by omega⟩ ⟨2, by omega⟩
  set a10 := M ⟨1, by omega⟩ ⟨0, by omega⟩
  set a12 := M ⟨1, by omega⟩ ⟨2, by omega⟩
  set a20 := M ⟨2, by omega⟩ ⟨0, by omega⟩
  set a21 := M ⟨2, by omega⟩ ⟨1, by omega⟩
  -- After simp:
  -- h0: c 1 * a10 + c 2 * a20 = 0
  -- h1: c 0 * a01 + c 2 * a21 = 0
  -- h2: c 0 * a02 + c 1 * a12 = 0
  -- Show c 0 = c 1 = c 2 = 0.
  intro i
  fin_cases i
  · -- c 0 = 0
    by_contra hc0
    rcases lt_or_gt_of_ne hc0 with hneg | hpos'
    · -- c 0 < 0, so c 1 > 0 (from h2) and c 2 > 0 (from h1).
      -- Then h0 = c 1 * a10 + c 2 * a20 > 0 ≠ 0.
      have hc1 : 0 < c 1 := by
        by_contra hcon; push Not at hcon
        have hA : c 1 * a12 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon p12.le
        have hB : c 0 * a02 < 0 := mul_neg_of_neg_of_pos hneg p02
        linarith
      have hc2 : 0 < c 2 := by
        by_contra hcon; push Not at hcon
        have hA : c 2 * a21 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon p21.le
        have hB : c 0 * a01 < 0 := mul_neg_of_neg_of_pos hneg p01
        linarith
      have hA : 0 < c 1 * a10 := mul_pos hc1 p10
      have hB : 0 < c 2 * a20 := mul_pos hc2 p20
      linarith
    · have hc1 : c 1 < 0 := by
        by_contra hcon; push Not at hcon
        have hA : 0 ≤ c 1 * a12 := mul_nonneg hcon p12.le
        have hB : 0 < c 0 * a02 := mul_pos hpos' p02
        linarith
      have hc2 : c 2 < 0 := by
        by_contra hcon; push Not at hcon
        have hA : 0 ≤ c 2 * a21 := mul_nonneg hcon p21.le
        have hB : 0 < c 0 * a01 := mul_pos hpos' p01
        linarith
      have hA : c 1 * a10 < 0 := mul_neg_of_neg_of_pos hc1 p10
      have hB : c 2 * a20 < 0 := mul_neg_of_neg_of_pos hc2 p20
      linarith
  · -- c 1 = 0
    by_contra hc1
    rcases lt_or_gt_of_ne hc1 with hneg | hpos'
    · -- c 1 < 0
      have hc0 : 0 < c 0 := by
        by_contra hcon; push Not at hcon
        have hA : c 0 * a02 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon p02.le
        have hB : c 1 * a12 < 0 := mul_neg_of_neg_of_pos hneg p12
        linarith
      have hc2 : 0 < c 2 := by
        by_contra hcon; push Not at hcon
        have hA : c 2 * a20 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon p20.le
        have hB : c 1 * a10 < 0 := mul_neg_of_neg_of_pos hneg p10
        linarith
      have hA : 0 < c 0 * a01 := mul_pos hc0 p01
      have hB : 0 < c 2 * a21 := mul_pos hc2 p21
      linarith
    · have hc0 : c 0 < 0 := by
        by_contra hcon; push Not at hcon
        have hA : 0 ≤ c 0 * a02 := mul_nonneg hcon p02.le
        have hB : 0 < c 1 * a12 := mul_pos hpos' p12
        linarith
      have hc2 : c 2 < 0 := by
        by_contra hcon; push Not at hcon
        have hA : 0 ≤ c 2 * a20 := mul_nonneg hcon p20.le
        have hB : 0 < c 1 * a10 := mul_pos hpos' p10
        linarith
      have hA : c 0 * a01 < 0 := mul_neg_of_neg_of_pos hc0 p01
      have hB : c 2 * a21 < 0 := mul_neg_of_neg_of_pos hc2 p21
      linarith
  · -- c 2 = 0
    by_contra hc2
    rcases lt_or_gt_of_ne hc2 with hneg | hpos'
    · have hc0 : 0 < c 0 := by
        by_contra hcon
        push Not at hcon
        have h1' : c 0 * a01 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon p01.le
        have h2' : c 2 * a21 < 0 := mul_neg_of_neg_of_pos hneg p21
        linarith
      have hc1 : 0 < c 1 := by
        by_contra hcon
        push Not at hcon
        have h1' : c 1 * a10 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon p10.le
        have h2' : c 2 * a20 < 0 := mul_neg_of_neg_of_pos hneg p20
        linarith
      have h1' : 0 < c 0 * a02 := mul_pos hc0 p02
      have h2' : 0 < c 1 * a12 := mul_pos hc1 p12
      linarith
    · have hc0 : c 0 < 0 := by
        by_contra hcon
        push Not at hcon
        have h1 : 0 ≤ c 0 * a01 := mul_nonneg hcon p01.le
        have h2 : 0 < c 2 * a21 := mul_pos hpos' p21
        linarith
      have hc1 : c 1 < 0 := by
        by_contra hcon
        push Not at hcon
        have h1' : 0 ≤ c 1 * a10 := mul_nonneg hcon p10.le
        have h2' : 0 < c 2 * a20 := mul_pos hpos' p20
        linarith
      have h1' : c 0 * a02 < 0 := mul_neg_of_neg_of_pos hc0 p02
      have h2' : c 1 * a12 < 0 := mul_neg_of_neg_of_pos hc1 p12
      linarith

/-- For `n ≥ 3`, the rank is at least 3. -/
lemma rank_ge_three {n : ℕ} (hn : 3 ≤ n) {M : Matrix (Fin n) (Fin n) ℝ}
    (h : IsZeroDiagPos M) : 3 ≤ Matrix.rank M := by
  -- The first three rows are linearly independent. Hence rank ≥ 3.
  have hLI := three_rows_linearIndependent hn M h
  -- Matrix.rank M = finrank of row span.
  rw [Matrix.rank_eq_finrank_span_row]
  -- The 3 LI rows are in the row span.
  have hsubset : ∀ i : Fin 3, M ⟨i.val, by omega⟩ ∈
      Submodule.span ℝ (Set.range (fun i : Fin n => M i)) := by
    intro i
    exact Submodule.subset_span ⟨_, rfl⟩
  -- Number of LI vectors ≤ finrank.
  classical
  haveI : FiniteDimensional ℝ (Submodule.span ℝ (Set.range (fun i : Fin n => M i))) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  -- Lift the LI to elements of the submodule.
  let v : Fin 3 → Submodule.span ℝ (Set.range (fun i : Fin n => M i)) :=
    fun i => ⟨M ⟨i.val, by omega⟩, hsubset i⟩
  have hLIv : LinearIndependent ℝ v := by
    apply LinearIndependent.of_comp (Submodule.subtype _)
    exact hLI
  have := hLIv.fintype_card_le_finrank
  simpa using this

/-- Construction for the upper bound when `n ≥ 3`: `M i j = (i.val - j.val)^2` as a real number. -/
def upperMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ((i.val : ℝ) - (j.val : ℝ))^2

/-- Verifies the conditions for `upperMatrix`. -/
lemma upperMatrix_isZeroDiagPos {n : ℕ} :
    IsZeroDiagPos (upperMatrix n) := by
  refine ⟨?_, ?_⟩
  · intro i; simp [upperMatrix]
  · intro i j hij
    have hne : ((i.val : ℝ) - (j.val : ℝ)) ≠ 0 := by
      intro h
      apply hij
      have : (i.val : ℝ) = (j.val : ℝ) := by linarith
      have heq : i.val = j.val := by exact_mod_cast this
      exact Fin.ext heq
    simp only [upperMatrix]
    positivity

/-- The upper matrix has rank at most 3: `(i-j)^2 = i^2·1 - 2·i·j + 1·j^2`. -/
lemma upperMatrix_rank_le {n : ℕ} : Matrix.rank (upperMatrix n) ≤ 3 := by
  set u1 : Fin n → ℝ := fun i => (i.val : ℝ)^2
  set v1 : Fin n → ℝ := fun _ => 1
  set u2 : Fin n → ℝ := fun i => -2 * (i.val : ℝ)
  set v2 : Fin n → ℝ := fun j => (j.val : ℝ)
  set u3 : Fin n → ℝ := fun _ => 1
  set v3 : Fin n → ℝ := fun j => (j.val : ℝ)^2
  have hdec : upperMatrix n = vecMulVec u1 v1 + vecMulVec u2 v2 + vecMulVec u3 v3 := by
    ext i j
    simp only [upperMatrix, vecMulVec_apply, Matrix.add_apply, u1, v1, u2, v2, u3, v3]
    ring
  rw [hdec]
  have h1 : Matrix.rank (vecMulVec u1 v1) ≤ 1 := Matrix.rank_vecMulVec_le _ _
  have h2 : Matrix.rank (vecMulVec u2 v2) ≤ 1 := Matrix.rank_vecMulVec_le _ _
  have h3 : Matrix.rank (vecMulVec u3 v3) ≤ 1 := Matrix.rank_vecMulVec_le _ _
  have hrankadd : ∀ (A B : Matrix (Fin n) (Fin n) ℝ),
      Matrix.rank (A + B) ≤ Matrix.rank A + Matrix.rank B := by
    intro A B
    rw [Matrix.rank, Matrix.rank, Matrix.rank, Matrix.mulVecLin_add]
    have hle : LinearMap.range (A.mulVecLin + B.mulVecLin) ≤
        LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
      rintro x ⟨y, rfl⟩
      simp only [LinearMap.add_apply]
      exact Submodule.add_mem _
        (Submodule.mem_sup_left ⟨y, rfl⟩)
        (Submodule.mem_sup_right ⟨y, rfl⟩)
    calc Module.finrank ℝ (LinearMap.range (A.mulVecLin + B.mulVecLin))
        ≤ Module.finrank ℝ (LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin :
            Submodule ℝ _) := Submodule.finrank_mono hle
      _ ≤ Module.finrank ℝ (LinearMap.range A.mulVecLin) +
            Module.finrank ℝ (LinearMap.range B.mulVecLin) :=
            Submodule.finrank_add_le_finrank_add_finrank _ _
  calc Matrix.rank (vecMulVec u1 v1 + vecMulVec u2 v2 + vecMulVec u3 v3)
      ≤ Matrix.rank (vecMulVec u1 v1 + vecMulVec u2 v2) + Matrix.rank (vecMulVec u3 v3) :=
          hrankadd _ _
    _ ≤ (Matrix.rank (vecMulVec u1 v1) + Matrix.rank (vecMulVec u2 v2)) +
          Matrix.rank (vecMulVec u3 v3) := by gcongr; exact hrankadd _ _
    _ ≤ 1 + 1 + 1 := by gcongr
    _ = 3 := by norm_num

snip end

problem imc2012_p2 :
    ∀ n : ℕ,
      (∃ M : Matrix (Fin n) (Fin n) ℝ, IsZeroDiagPos M ∧ Matrix.rank M ≤ answer n) ∧
      (∀ M : Matrix (Fin n) (Fin n) ℝ, IsZeroDiagPos M → answer n ≤ Matrix.rank M) := by
  intro n
  by_cases h1 : n ≤ 1
  · refine ⟨?_, ?_⟩
    · obtain ⟨M, hM, hrank⟩ := example_zero n h1
      refine ⟨M, hM, ?_⟩
      simp [answer, h1, hrank]
    · intros M _
      simp [answer, h1]
  · by_cases h2 : n = 2
    · subst h2
      refine ⟨?_, ?_⟩
      · obtain ⟨M, hM, hrank⟩ := example_two
        refine ⟨M, hM, ?_⟩
        simp [answer, hrank]
      · intro M hM
        have := rank_ge_of_two hM
        simpa [answer] using this
    · have hn3 : 3 ≤ n := by omega
      refine ⟨?_, ?_⟩
      · refine ⟨upperMatrix n, upperMatrix_isZeroDiagPos, ?_⟩
        have := @upperMatrix_rank_le n
        simpa [answer, h1, h2] using this
      · intro M hM
        have := rank_ge_three hn3 hM
        simpa [answer, h1, h2] using this

end Imc2012P2
