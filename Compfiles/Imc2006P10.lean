/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2006, Problem 10

(Also listed as Day 2, Problem 4.)

Let `v₀ = 0` and let `v₁, …, v_{n+1}` be vectors in `ℝⁿ` such that the Euclidean
distance `‖vᵢ - vⱼ‖` is rational for all `0 ≤ i, j ≤ n+1`. Prove that
`v₁, …, v_{n+1}` are linearly dependent over `ℚ`.

## Proof sketch

Since `v₀ = 0`, we have `‖vᵢ‖ = ‖vᵢ - v₀‖ ∈ ℚ`, and by the polarisation identity
`⟨vᵢ, vⱼ⟩ = (‖vᵢ‖² + ‖vⱼ‖² - ‖vᵢ - vⱼ‖²) / 2`, all pairwise inner products
`⟨vᵢ, vⱼ⟩` are rational.

Consider the Gram matrix `G` of shape `(n+1) × (n+1)` with entries
`G i j = ⟨vᵢ₊₁, vⱼ₊₁⟩ ∈ ℚ`. Since the `n+1` vectors lie in the `n`-dimensional
space `ℝⁿ`, they are real-linearly dependent, so the real Gram matrix has a
nontrivial real kernel and hence determinant zero. Rational determinant is the
same (up to `ℚ → ℝ` cast), so the rational Gram matrix also has a nontrivial
rational kernel vector `c`. Interpreting `c` over `ℝ`, the vector
`s = ∑ᵢ cᵢ · vᵢ₊₁` satisfies `‖s‖² = cᵀ G c = 0`, so `s = 0`, giving a
nontrivial `ℚ`-linear relation.
-/

namespace Imc2006P10

open scoped BigOperators

open Matrix

snip begin

/-- The real Gram matrix of a finite family of vectors. -/
private noncomputable def gram {m n : ℕ} (w : Fin m → EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => inner ℝ (w i) (w j)

/-- For every real `c`, we have `cᵀ G c = ‖∑ cᵢ wᵢ‖²`. -/
private lemma gram_quadratic_form
    {m n : ℕ} (w : Fin m → EuclideanSpace ℝ (Fin n)) (c : Fin m → ℝ) :
    ∑ i : Fin m, ∑ j : Fin m, c i * c j * gram w i j
      = ‖∑ i : Fin m, c i • w i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  apply Finset.sum_congr rfl; intro i _
  rw [inner_sum]
  apply Finset.sum_congr rfl; intro j _
  rw [real_inner_smul_left, real_inner_smul_right]
  simp [gram, Matrix.of_apply]
  ring

/-- If the Gram matrix `G` has a real kernel vector `c` (i.e., `G *ᵥ c = 0`),
then the corresponding linear combination `∑ cᵢ wᵢ` is zero. -/
private lemma sum_smul_eq_zero_of_mulVec_zero
    {m n : ℕ} (w : Fin m → EuclideanSpace ℝ (Fin n)) (c : Fin m → ℝ)
    (h : gram w *ᵥ c = 0) :
    ∑ i : Fin m, c i • w i = 0 := by
  -- (G c)_i = ∑ⱼ G_{ij} c_j = 0.
  have h_rows_zero : ∀ i, (∑ j : Fin m, gram w i j * c j) = 0 := by
    intro i
    have hi := congr_fun h i
    -- hi : (gram w *ᵥ c) i = 0, which is defeq to ∑ j, gram w i j * c j = 0
    exact hi
  -- cᵀ G c = ∑ᵢ cᵢ (∑ⱼ G_{ij} cⱼ) = 0.
  have h_qf : ∑ i : Fin m, ∑ j : Fin m, c i * c j * gram w i j = 0 := by
    calc ∑ i : Fin m, ∑ j : Fin m, c i * c j * gram w i j
        = ∑ i : Fin m, c i * (∑ j : Fin m, gram w i j * c j) := by
          apply Finset.sum_congr rfl; intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j _; ring
      _ = 0 := by simp [h_rows_zero]
  have h_norm_sq_zero : ‖∑ i : Fin m, c i • w i‖ ^ 2 = 0 := by
    rw [← gram_quadratic_form]; exact h_qf
  have : ‖∑ i : Fin m, c i • w i‖ = 0 := by
    have hpos : (0 : ℝ) ≤ ‖∑ i : Fin m, c i • w i‖ := norm_nonneg _
    nlinarith [sq_nonneg ‖∑ i : Fin m, c i • w i‖]
  exact norm_eq_zero.mp this

/-- Gram matrix entries are rational when all norms and pairwise distances are rational. -/
private lemma gram_entry_rational
    {m n : ℕ} (v : Fin m → EuclideanSpace ℝ (Fin n))
    (hnorm : ∀ i : Fin m, ∃ q : ℚ, ‖v i‖ = (q : ℝ))
    (hdist : ∀ i j : Fin m, ∃ q : ℚ, ‖v i - v j‖ = (q : ℝ))
    (i j : Fin m) :
    ∃ q : ℚ, inner ℝ (v i) (v j) = (q : ℝ) := by
  obtain ⟨qi, hqi⟩ := hnorm i
  obtain ⟨qj, hqj⟩ := hnorm j
  obtain ⟨qd, hqd⟩ := hdist i j
  refine ⟨(qi^2 + qj^2 - qd^2) / 2, ?_⟩
  have h_identity : inner ℝ (v i) (v j) =
      (‖v i‖^2 + ‖v j‖^2 - ‖v i - v j‖^2) / 2 := by
    have hsub : ‖v i - v j‖^2 =
        ‖v i‖^2 - 2 * inner ℝ (v i) (v j) + ‖v j‖^2 := @norm_sub_sq_real _ _ _ _ _
    linarith
  rw [h_identity, hqi, hqj, hqd]
  push_cast
  ring

snip end

/--
Statement: `v₀ = 0` and `v₁, …, v_{n+1}` are vectors in `ℝⁿ` with all pairwise
distances rational. Then the vectors `v 1, …, v (n+1)` are not linearly
independent over `ℚ`.
-/
problem imc2006_p10
    (n : ℕ)
    (v : Fin (n + 2) → EuclideanSpace ℝ (Fin n))
    (hv0 : v 0 = 0)
    (hdist : ∀ i j : Fin (n + 2), ∃ q : ℚ, ‖v i - v j‖ = (q : ℝ)) :
    ¬ LinearIndependent ℚ (fun k : Fin (n + 1) => v k.succ) := by
  -- Set w k = v k.succ, for k : Fin (n+1).
  set w : Fin (n + 1) → EuclideanSpace ℝ (Fin n) := fun k => v k.succ with hw_def
  -- All ‖w i‖ ∈ ℚ (using v 0 = 0).
  have h_norm : ∀ k : Fin (n + 1), ∃ q : ℚ, ‖w k‖ = (q : ℝ) := by
    intro k
    obtain ⟨q, hq⟩ := hdist 0 k.succ
    refine ⟨q, ?_⟩
    have : ‖v 0 - v k.succ‖ = ‖v k.succ‖ := by rw [hv0]; simp
    show ‖v k.succ‖ = (q : ℝ)
    rw [← this]; exact hq
  have h_wdist : ∀ i j : Fin (n + 1), ∃ q : ℚ, ‖w i - w j‖ = (q : ℝ) := by
    intro i j
    exact hdist i.succ j.succ
  -- Gram entries are rational.
  have h_gram_rat : ∀ i j : Fin (n + 1), ∃ q : ℚ, inner ℝ (w i) (w j) = (q : ℝ) :=
    gram_entry_rational w h_norm h_wdist
  -- Choose representatives.
  choose GQ hGQ using h_gram_rat
  -- The real Gram matrix is the cast of the rational one.
  have h_cast_eq : (Matrix.of GQ).map ((↑) : ℚ → ℝ) = gram w := by
    ext i j
    simp [Matrix.map, Matrix.of_apply, gram, hGQ i j]
  -- The w's are ℝ-dependent: n+1 vectors in n-dimensional space.
  have h_dep : ¬ LinearIndependent ℝ w := by
    intro h_indep
    have hcard := h_indep.fintype_card_le_finrank (R := ℝ)
    simp at hcard
  -- Extract nonzero real kernel vector.
  rw [not_linearIndependent_iff] at h_dep
  obtain ⟨s, g, hg_sum, i₀, hi₀s, hi₀⟩ := h_dep
  let cR : Fin (n + 1) → ℝ := fun k => if k ∈ s then g k else 0
  have hcR_sum : ∑ k : Fin (n + 1), cR k • w k = 0 := by
    rw [← hg_sum]
    rw [show (∑ i ∈ s, g i • w i : EuclideanSpace ℝ (Fin n)) =
          ∑ i ∈ s, cR i • w i from ?_]
    · rw [← Finset.sum_subset (Finset.subset_univ s)]
      intro x _ hx
      simp [cR, hx]
    · apply Finset.sum_congr rfl
      intro i hi
      simp [cR, hi]
  have hcR_ne : cR ≠ 0 := by
    intro heq
    have hi0 : cR i₀ = 0 := by rw [heq]; rfl
    simp [cR, hi₀s] at hi0
    exact hi₀ hi0
  -- Hence real Gram kills cR: (gram w) *ᵥ cR = 0.
  have h_gram_cR_zero : (gram w) *ᵥ cR = 0 := by
    funext i
    show (∑ j : Fin (n + 1), gram w i j * cR j) = 0
    have h_inner_zero : inner ℝ (w i) (∑ j : Fin (n + 1), cR j • w j) = (0 : ℝ) := by
      rw [hcR_sum]; simp
    have h_step : (∑ j : Fin (n + 1), gram w i j * cR j)
        = inner ℝ (w i) (∑ j : Fin (n + 1), cR j • w j) := by
      rw [inner_sum]
      apply Finset.sum_congr rfl; intro j _
      rw [real_inner_smul_right]
      simp [gram, Matrix.of_apply]
      ring
    rw [h_step, h_inner_zero]
  -- Real Gram has determinant zero.
  have h_det_real_zero : (gram w).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    exact ⟨cR, hcR_ne, h_gram_cR_zero⟩
  -- Hence rational Gram has determinant zero (using RingHom.map_det).
  have h_det_rat_zero : (Matrix.of GQ).det = 0 := by
    have h1 : ((Matrix.of GQ).det : ℝ) = ((Matrix.of GQ).map ((↑) : ℚ → ℝ)).det := by
      exact RingHom.map_det (Rat.castHom ℝ) (Matrix.of GQ)
    rw [h_cast_eq] at h1
    have : ((Matrix.of GQ).det : ℝ) = 0 := by rw [h1]; exact h_det_real_zero
    exact_mod_cast this
  -- Extract nonzero rational kernel vector.
  obtain ⟨c, hc_ne, hc_kernel⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr h_det_rat_zero
  -- Cast c to ℝ, check Gram kernel.
  let cReal : Fin (n + 1) → ℝ := fun k => (c k : ℝ)
  have h_gram_cReal : (gram w) *ᵥ cReal = 0 := by
    funext i
    show (∑ j : Fin (n + 1), gram w i j * cReal j) = 0
    have h_rat_i : (∑ j : Fin (n + 1), GQ i j * c j : ℚ) = 0 := by
      have hki := congr_fun hc_kernel i
      -- hki : (Matrix.of GQ *ᵥ c) i = 0, defeq to ∑ j, GQ i j * c j = 0
      exact hki
    have h_step : ∑ j : Fin (n + 1), gram w i j * cReal j
        = ((∑ j : Fin (n + 1), GQ i j * c j : ℚ) : ℝ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro j _
      simp [gram, Matrix.of_apply, hGQ i j, cReal]
    rw [h_step, h_rat_i]; push_cast; rfl
  -- So ∑ cReal i • w i = 0.
  have h_sum_zero : ∑ i : Fin (n + 1), cReal i • w i = 0 :=
    sum_smul_eq_zero_of_mulVec_zero w cReal h_gram_cReal
  -- Now derive contradiction with ℚ-linear independence.
  intro h_indep
  rw [linearIndependent_iff'] at h_indep
  obtain ⟨i₀', hi₀'⟩ : ∃ i, c i ≠ 0 := by
    by_contra h
    apply hc_ne
    funext i
    exact not_not.mp (fun hne => h ⟨i, hne⟩)
  have h_all_zero := h_indep Finset.univ c (by
    -- Need: ∑ᵢ (c i : ℚ) • w i = 0 in the ℚ-module.
    -- The ℚ-action equals ℝ-action via Rat.cast.
    have hsmul : ∀ i, (c i : ℚ) • w i = cReal i • w i := by
      intro i
      exact (Rat.cast_smul_eq_qsmul ℝ (c i) (w i)).symm
    simp only [hsmul]
    exact h_sum_zero
    ) i₀' (Finset.mem_univ _)
  exact hi₀' h_all_zero

end Imc2006P10
