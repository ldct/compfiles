/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2025, Problem 8

For an `n × n` real matrix `A ∈ M_n(ℝ)`, denote by `A^R` its counter-clockwise
`90°` rotation. For example,

  `⎡1 2 3⎤^R   ⎡3 6 9⎤`
  `⎢4 5 6⎥   = ⎢2 5 8⎥`.
  `⎣7 8 9⎦     ⎣1 4 7⎦`

Formally, `(A^R)_{i,j} = A_{j, n+1-i}`.

Prove that if `A = A^R` then for any eigenvalue `λ` of `A` (as a complex
matrix), we have `Re λ = 0` or `Im λ = 0`.
-/

namespace Imc2025P8

open Matrix
open scoped ComplexOrder

/-- The counter-clockwise 90° rotation of a square matrix: sending position
  `(i, j)` to `(n + 1 - j, i)`. Equivalently, `(A^R)_{i,j} = A_{j, n+1-i}`.
  We encode `n+1-i` using `Fin.rev`. -/
def rot90 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => A j i.rev

snip begin

/-- The reversal permutation matrix `J` with `J i j = 1` iff `i.rev = j`. -/
def Jrev (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i.rev = j then 1 else 0

lemma Jrev_apply {n : ℕ} (i j : Fin n) : Jrev n i j = if i.rev = j then 1 else 0 := rfl

lemma Jrev_transpose {n : ℕ} : (Jrev n)ᵀ = Jrev n := by
  ext i j
  simp only [Matrix.transpose_apply, Jrev_apply]
  by_cases h : j.rev = i
  · have h' : i.rev = j := by rw [← h, Fin.rev_rev]
    rw [if_pos h, if_pos h']
  · rw [if_neg h, if_neg]
    intro h2
    apply h
    rw [← h2, Fin.rev_rev]

lemma Jrev_mul_Jrev {n : ℕ} : Jrev n * Jrev n = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Jrev_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single i.rev]
  · rw [if_pos rfl, one_mul]
    by_cases h : i = j
    · subst h
      simp [Fin.rev_rev]
    · rw [if_neg, if_neg h]
      intro h2
      apply h
      rw [← h2, Fin.rev_rev]
  · intro k _ hk
    rw [if_neg (Ne.symm hk), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma rot90_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    rot90 A = Jrev n * Aᵀ := by
  ext i j
  simp only [rot90, Matrix.mul_apply, Matrix.transpose_apply, Jrev_apply]
  rw [Finset.sum_eq_single i.rev]
  · rw [if_pos rfl, one_mul]
  · intro k _ hk
    rw [if_neg (Ne.symm hk), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Key identity: if `A = rot90 A`, then `Jrev n * A = Aᵀ`. -/
lemma JA_eq_AT {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A = rot90 A) :
    Jrev n * A = Aᵀ := by
  have h1 : A = Jrev n * Aᵀ := by
    conv_lhs => rw [hA]
    exact rot90_eq A
  have h2 : Jrev n * A = Jrev n * (Jrev n * Aᵀ) := by rw [← h1]
  rw [← Matrix.mul_assoc, Jrev_mul_Jrev, Matrix.one_mul] at h2
  exact h2

/-- If `μ² ∈ ℝ` then either `μ.re = 0` or `μ.im = 0`. -/
lemma re_or_im_eq_zero_of_sq_real {μ : ℂ} (hsq : (μ ^ 2).im = 0) :
    μ.re = 0 ∨ μ.im = 0 := by
  have : 2 * μ.re * μ.im = 0 := by
    have := hsq
    simp [pow_two, Complex.mul_im] at this
    linarith
  rcases mul_eq_zero.mp this with h | h
  · rcases mul_eq_zero.mp h with h | h
    · norm_num at h
    · left; exact h
  · right; exact h

snip end

/-- The statement: if `A = A^R`, then every complex eigenvalue `λ` of `A`
satisfies `Re λ = 0` or `Im λ = 0`. -/
problem imc2025_p8 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A = rot90 A)
    (lam : ℂ) (hlam : ∃ v : Fin n → ℂ, v ≠ 0 ∧
      (A.map (fun r => (r : ℂ))) *ᵥ v = lam • v) :
    lam.re = 0 ∨ lam.im = 0 := by
  -- We'll work with a map induced by the ring hom Complex.ofRealHom.
  have hmap_mul : ∀ (M N : Matrix (Fin n) (Fin n) ℝ),
      (M * N).map (fun r : ℝ => (r : ℂ)) =
        M.map (fun r : ℝ => (r : ℂ)) * N.map (fun r : ℝ => (r : ℂ)) := by
    intro M N
    exact (Matrix.map_mul (f := Complex.ofRealHom))
  set Aℂ : Matrix (Fin n) (Fin n) ℂ := A.map (fun r => (r : ℂ)) with hAℂdef
  set Jℂ : Matrix (Fin n) (Fin n) ℂ := (Jrev n).map (fun r => (r : ℂ)) with hJℂdef
  -- Jℂ Aℂ = Aℂᵀ
  have hJA_AT_ℂ : Jℂ * Aℂ = Aℂᵀ := by
    have hh : Jrev n * A = Aᵀ := JA_eq_AT A hA
    have hmap := (hmap_mul (Jrev n) A).symm
    rw [hh] at hmap
    rw [hmap]
    rw [Matrix.transpose_map]
  -- Jℂ is symmetric
  have hJℂ_symm : Jℂᵀ = Jℂ := by
    rw [hJℂdef]
    rw [← Matrix.transpose_map, Jrev_transpose]
  -- Each entry of Aℂ has star equal to itself (since A is real)
  have hA_star_entry : ∀ i j, star (Aℂ i j) = Aℂ i j := by
    intro i j
    simp [hAℂdef, Matrix.map_apply]
  have hJ_star_entry : ∀ i j, star (Jℂ i j) = Jℂ i j := by
    intro i j
    simp [hJℂdef, Matrix.map_apply]
  -- star (Aℂ *ᵥ v) = Aℂ *ᵥ (star v)
  have hstarMulVec_A : ∀ v : Fin n → ℂ, star (Aℂ *ᵥ v) = Aℂ *ᵥ (star v) := by
    intro v
    funext i
    show star ((Aℂ *ᵥ v) i) = (Aℂ *ᵥ star v) i
    simp only [Matrix.mulVec, dotProduct, star_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [star_mul', hA_star_entry]
    rfl
  have hstarMulVec_J : ∀ v : Fin n → ℂ, star (Jℂ *ᵥ v) = Jℂ *ᵥ (star v) := by
    intro v
    funext i
    show star ((Jℂ *ᵥ v) i) = (Jℂ *ᵥ star v) i
    simp only [Matrix.mulVec, dotProduct, star_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [star_mul', hJ_star_entry]
    rfl
  obtain ⟨v, hv_ne, hvEig⟩ := hlam
  -- LHS: star(Aℂv) ⬝ᵥ (Aℂv) = |lam|² * (star v ⬝ᵥ v)
  have hLHS : star (Aℂ *ᵥ v) ⬝ᵥ (Aℂ *ᵥ v) =
      (starRingEnd ℂ lam) * lam * (star v ⬝ᵥ v) := by
    rw [hvEig]
    have hstar_smul : star (lam • v) = (starRingEnd ℂ lam) • star v := by
      funext i
      show star ((lam • v) i) = (starRingEnd ℂ lam * star (v i))
      change star (lam * v i) = _
      rw [star_mul', starRingEnd_apply, mul_comm]
    rw [hstar_smul, smul_dotProduct, dotProduct_smul,
        smul_eq_mul, smul_eq_mul]
    ring
  -- RHS: star(Aℂv) ⬝ᵥ (Aℂv) = star v ⬝ᵥ (Aℂᵀ *ᵥ Aℂ *ᵥ v)
  have hRHS1 : star (Aℂ *ᵥ v) ⬝ᵥ (Aℂ *ᵥ v) =
      star v ⬝ᵥ (Aℂᵀ *ᵥ (Aℂ *ᵥ v)) := by
    rw [hstarMulVec_A]
    -- (Aℂ *ᵥ star v) ⬝ᵥ (Aℂ *ᵥ v) = (Aℂ *ᵥ v) ⬝ᵥ (Aℂ *ᵥ star v) (comm)
    rw [dotProduct_comm (Aℂ *ᵥ star v) (Aℂ *ᵥ v)]
    -- = (Aℂ *ᵥ v) ᵥ* Aℂ ⬝ᵥ star v  (dotProduct_mulVec)
    rw [dotProduct_mulVec]
    -- = Aℂᵀ *ᵥ (Aℂ *ᵥ v) ⬝ᵥ star v  (mulVec_transpose in reverse)
    rw [← Matrix.mulVec_transpose]
    -- = star v ⬝ᵥ Aℂᵀ *ᵥ (Aℂ *ᵥ v)  (comm)
    rw [dotProduct_comm]
  -- Aℂᵀ *ᵥ (Aℂ *ᵥ v) = lam² • (Jℂ *ᵥ v)
  have hATAv : Aℂᵀ *ᵥ (Aℂ *ᵥ v) = lam ^ 2 • (Jℂ *ᵥ v) := by
    have h1 : Aℂᵀ *ᵥ (Aℂ *ᵥ v) = (Jℂ * Aℂ) *ᵥ (Aℂ *ᵥ v) := by rw [hJA_AT_ℂ]
    rw [h1]
    -- (Jℂ * Aℂ) *ᵥ (Aℂ *ᵥ v) = Jℂ *ᵥ (Aℂ *ᵥ (Aℂ *ᵥ v))
    rw [show (Jℂ * Aℂ) *ᵥ (Aℂ *ᵥ v) = Jℂ *ᵥ (Aℂ *ᵥ (Aℂ *ᵥ v))
        from (Matrix.mulVec_mulVec (Aℂ *ᵥ v) Jℂ Aℂ).symm]
    rw [hvEig, Matrix.mulVec_smul, hvEig, smul_smul, Matrix.mulVec_smul, sq]
  rw [hATAv, dotProduct_smul, smul_eq_mul] at hRHS1
  have hIdent : (starRingEnd ℂ lam) * lam * (star v ⬝ᵥ v) =
      lam ^ 2 * (star v ⬝ᵥ (Jℂ *ᵥ v)) := by
    rw [← hLHS, hRHS1]
  -- ⟨v,v⟩ ≠ 0
  have hvv_ne : (star v ⬝ᵥ v : ℂ) ≠ 0 := by
    rw [ne_eq, dotProduct_star_self_eq_zero]
    exact hv_ne
  -- ⟨v, Jℂ v⟩ is real
  have hJvv_real : star (star v ⬝ᵥ (Jℂ *ᵥ v)) = star v ⬝ᵥ (Jℂ *ᵥ v) := by
    -- star(star v ⬝ᵥ w) = star w ⬝ᵥ v, so star(star v ⬝ᵥ Jℂv) = star(Jℂv) ⬝ᵥ v = (Jℂ * star v) ⬝ᵥ v
    have h1 : star (star v ⬝ᵥ (Jℂ *ᵥ v)) = star (Jℂ *ᵥ v) ⬝ᵥ v := by
      rw [star_dotProduct, star_star]
    rw [h1, hstarMulVec_J]
    -- goal: (Jℂ *ᵥ star v) ⬝ᵥ v = star v ⬝ᵥ (Jℂ *ᵥ v)
    rw [dotProduct_comm (Jℂ *ᵥ star v) v]
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hJℂ_symm]
    rw [dotProduct_comm]
  -- ⟨v, v⟩ is real (its star equals itself)
  have hvv_real : star (star v ⬝ᵥ v) = star v ⬝ᵥ v := by
    have h1 : star (star v ⬝ᵥ v) = v ⬝ᵥ star v := by
      simp [star_dotProduct, star_star, dotProduct]
    rw [h1]; exact (dotProduct_comm (star v) v).symm
  -- Apply star to hIdent.
  by_cases hd : (star v ⬝ᵥ (Jℂ *ᵥ v)) = 0
  · rw [hd, mul_zero] at hIdent
    -- hIdent : star lam * lam * <v,v> = 0, <v,v> ≠ 0, so star lam * lam = 0, so lam = 0.
    have hmod_zero : (starRingEnd ℂ lam) * lam = 0 := by
      rcases mul_eq_zero.mp hIdent with h | h
      · exact h
      · exact absurd h hvv_ne
    have hlam_zero : lam = 0 := by
      have h0 : (lam.normSq : ℂ) = (starRingEnd ℂ) lam * lam := by
        rw [starRingEnd_apply]
        exact Complex.normSq_eq_conj_mul_self
      have hns : (lam.normSq : ℂ) = 0 := h0.trans hmod_zero
      have h1 : lam.normSq = 0 := by exact_mod_cast hns
      exact Complex.normSq_eq_zero.mp h1
    subst hlam_zero
    right; rfl
  · -- Apply star to hIdent to get: star lam * lam * <v,v> = (star lam)² * <v, Jv>
    -- Then divide by <v, Jv> = d to conclude lam² = (star lam)².
    have hId_star : (starRingEnd ℂ lam) * lam * (star v ⬝ᵥ v) =
        (starRingEnd ℂ lam) ^ 2 * (star v ⬝ᵥ (Jℂ *ᵥ v)) := by
      have hstar := congr_arg (starRingEnd ℂ) hIdent
      simp only [map_mul, map_pow, starRingEnd_apply, star_star] at hstar
      rw [hvv_real, hJvv_real] at hstar
      -- hstar : lam * star lam * <v,v> = (star lam)² * <v,Jv>
      rw [starRingEnd_apply]
      rw [show lam * star lam = star lam * lam from mul_comm _ _] at hstar
      exact hstar
    have heq_sq : lam ^ 2 = (starRingEnd ℂ lam) ^ 2 := by
      have hmul : lam ^ 2 * (star v ⬝ᵥ (Jℂ *ᵥ v)) =
          (starRingEnd ℂ lam) ^ 2 * (star v ⬝ᵥ (Jℂ *ᵥ v)) := by
        rw [← hIdent, hId_star]
      exact mul_right_cancel₀ hd hmul
    -- lam² = (star lam)² ⇒ star (lam²) = lam², so lam² is real
    have hlam_sq_real : (lam ^ 2).im = 0 := by
      have hfix : starRingEnd ℂ (lam ^ 2) = lam ^ 2 := by
        rw [map_pow]; exact heq_sq.symm
      have him := congr_arg Complex.im hfix
      rw [starRingEnd_apply, Complex.star_def, Complex.conj_im] at him
      -- him : -(lam^2).im = (lam^2).im
      linarith
    exact re_or_im_eq_zero_of_sq_real hlam_sq_real

end Imc2025P8
