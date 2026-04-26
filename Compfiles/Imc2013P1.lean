/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2013, Problem 1

Let `A` and `B` be real symmetric matrices with all eigenvalues strictly
greater than `1`. Let `λ` be a real eigenvalue of matrix `AB`.
Prove that `|λ| > 1`.

We encode "all eigenvalues `> 1`" for a real symmetric matrix `M` by the
(equivalent) quadratic-form condition: for every nonzero `v`,
`v ⬝ M v > v ⬝ v`.
-/

namespace Imc2013P1

open Matrix

snip begin

/-- Cauchy–Schwarz for the real dot product: `(v ⬝ w)² ≤ (v ⬝ v) * (w ⬝ w)`. -/
lemma dotProduct_sq_le {n : Type*} [Fintype n] (v w : n → ℝ) :
    (v ⬝ᵥ w) ^ 2 ≤ (v ⬝ᵥ v) * (w ⬝ᵥ w) := by
  have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset n) v w
  simpa [dotProduct, sq] using this

/-- For nonzero real vectors, `v ⬝ v > 0`. -/
lemma dotProduct_self_pos_of_ne_zero {n : Type*} [Fintype n] {v : n → ℝ}
    (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    ext i
    by_contra hvi
    exact h ⟨i, hvi⟩
  have hi_sq : 0 < v i * v i := mul_pos_of_ne_zero hi
  unfold dotProduct
  refine Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ _, hi_sq⟩
where
  mul_pos_of_ne_zero {a : ℝ} (ha : a ≠ 0) : 0 < a * a := by
    rcases lt_or_gt_of_ne ha with h | h
    · exact mul_pos_of_neg_of_neg h h
    · exact mul_pos h h

snip end

/-- IMC 2013, Problem 1.

For real symmetric matrices `A` and `B` (of the same square shape) whose
quadratic forms strictly exceed the identity's (`v ⬝ M v > v ⬝ v` for all
`v ≠ 0`), every real eigenvalue `λ` of `A * B` satisfies `1 < |λ|`. -/
problem imc2013_p1 {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (_hA : A.IsSymm) (hB : B.IsSymm)
    (hA1 : ∀ v : Fin n → ℝ, v ≠ 0 → v ⬝ᵥ (A *ᵥ v) > v ⬝ᵥ v)
    (hB1 : ∀ v : Fin n → ℝ, v ≠ 0 → v ⬝ᵥ (B *ᵥ v) > v ⬝ᵥ v)
    (lam : ℝ) (v : Fin n → ℝ) (hv : v ≠ 0)
    (hlam : (A * B) *ᵥ v = lam • v) :
    1 < |lam| := by
  set u : Fin n → ℝ := B *ᵥ v with hu_def
  -- Basic positivity: v ⬝ v > 0 since v ≠ 0.
  have hvv_pos : 0 < v ⬝ᵥ v := dotProduct_self_pos_of_ne_zero hv
  -- v ⬝ B v > v ⬝ v > 0.
  have hvBv_gt : v ⬝ᵥ (B *ᵥ v) > v ⬝ᵥ v := hB1 v hv
  have hvBv_pos : 0 < v ⬝ᵥ (B *ᵥ v) := lt_trans hvv_pos hvBv_gt
  -- u = B v is nonzero, else v ⬝ B v = 0, contradiction.
  have hu_ne : u ≠ 0 := by
    intro hu_zero
    have : v ⬝ᵥ (B *ᵥ v) = 0 := by
      show v ⬝ᵥ u = 0
      rw [hu_zero, dotProduct_zero]
    linarith
  -- A u = lam • v from (A * B) *ᵥ v = lam • v.
  have hAu : A *ᵥ u = lam • v := by
    show A *ᵥ (B *ᵥ v) = lam • v
    rw [mulVec_mulVec]; exact hlam
  -- u ⬝ v = v ⬝ B v: from symmetry and dotProduct_comm.
  have huv : u ⬝ᵥ v = v ⬝ᵥ (B *ᵥ v) := by
    show (B *ᵥ v) ⬝ᵥ v = v ⬝ᵥ (B *ᵥ v)
    exact dotProduct_comm _ _
  -- u ⬝ A u = lam * (v ⬝ B v).
  have huAu : u ⬝ᵥ (A *ᵥ u) = lam * (v ⬝ᵥ (B *ᵥ v)) := by
    rw [hAu, dotProduct_smul, smul_eq_mul, huv]
  -- u ⬝ u = v ⬝ (B (B v)): symmetry.
  have huu : u ⬝ᵥ u = v ⬝ᵥ (B *ᵥ u) := by
    show (B *ᵥ v) ⬝ᵥ (B *ᵥ v) = v ⬝ᵥ (B *ᵥ (B *ᵥ v))
    have hBT : Bᵀ = B := hB
    -- (B *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (Bᵀ *ᵥ w) via transpose_mulVec identity.
    calc (B *ᵥ v) ⬝ᵥ (B *ᵥ v)
        = (v ᵥ* Bᵀ) ⬝ᵥ (B *ᵥ v) := by rw [vecMul_transpose]
      _ = v ⬝ᵥ (Bᵀ *ᵥ (B *ᵥ v)) := by rw [← dotProduct_mulVec]
      _ = v ⬝ᵥ (B *ᵥ (B *ᵥ v)) := by rw [hBT]
  -- Cauchy–Schwarz: (v ⬝ B v)² ≤ (v ⬝ v) * (v ⬝ B (B v)).
  have hCS : (v ⬝ᵥ (B *ᵥ v)) ^ 2 ≤ (v ⬝ᵥ v) * (v ⬝ᵥ (B *ᵥ u)) := by
    have h := dotProduct_sq_le v u
    have h1 : v ⬝ᵥ u = v ⬝ᵥ (B *ᵥ v) := rfl
    rw [h1] at h
    rw [← huu]
    exact h
  -- Strict: u ⬝ A u > u ⬝ u.
  have hAu_gt : u ⬝ᵥ (A *ᵥ u) > u ⬝ᵥ u := hA1 u hu_ne
  -- Combine: lam * (v ⬝ B v) = u ⬝ A u > u ⬝ u ≥ (v ⬝ B v)² / (v ⬝ v).
  have hchain : lam * (v ⬝ᵥ (B *ᵥ v)) > (v ⬝ᵥ (B *ᵥ v)) ^ 2 / (v ⬝ᵥ v) := by
    have h1 : lam * (v ⬝ᵥ (B *ᵥ v)) > v ⬝ᵥ (B *ᵥ u) := by
      rw [← huAu, ← huu]; exact hAu_gt
    have h2 : v ⬝ᵥ (B *ᵥ u) ≥ (v ⬝ᵥ (B *ᵥ v)) ^ 2 / (v ⬝ᵥ v) := by
      rw [ge_iff_le, div_le_iff₀ hvv_pos]; linarith
    linarith
  -- Multiply through by v ⬝ v > 0 and cancel (v ⬝ B v) > 0.
  have hsq : (v ⬝ᵥ (B *ᵥ v)) ^ 2 = (v ⬝ᵥ (B *ᵥ v)) * (v ⬝ᵥ (B *ᵥ v)) := by ring
  have hmul : lam * (v ⬝ᵥ (B *ᵥ v)) * (v ⬝ᵥ v) > (v ⬝ᵥ (B *ᵥ v)) * (v ⬝ᵥ (B *ᵥ v)) := by
    have := (div_lt_iff₀ hvv_pos).mp hchain
    linarith [hsq]
  -- lam * (v ⬝ v) > v ⬝ B v, by dividing hmul by (v ⬝ B v) > 0.
  have hlam_bound : lam * (v ⬝ᵥ v) > v ⬝ᵥ (B *ᵥ v) := by
    -- lam * (v ⬝ B v) * (v ⬝ v) > (v ⬝ B v) * (v ⬝ B v)
    -- ⇒ (lam * (v ⬝ v)) * (v ⬝ B v) > (v ⬝ B v) * (v ⬝ B v)
    -- ⇒ lam * (v ⬝ v) > v ⬝ B v  (cancel v ⬝ B v > 0)
    nlinarith [hmul, hvBv_pos]
  -- So lam > (v ⬝ B v)/(v ⬝ v) > 1.
  have hlam_gt_1 : lam > 1 := by
    -- From lam * (v⬝v) > v⬝Bv > v⬝v and v⬝v > 0.
    nlinarith [hlam_bound, hvBv_gt, hvv_pos]
  rw [abs_of_pos (by linarith : (0:ℝ) < lam)]
  exact hlam_gt_1

end Imc2013P1
