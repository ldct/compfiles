/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2017, Problem 1

Determine all complex numbers `λ` for which there exist a positive integer `n`
and a real `n × n` matrix `A` such that `A² = Aᵀ` and `λ` is an eigenvalue of `A`.

Answer: the complex numbers `λ` with `λ⁴ = λ`, i.e.
`0, 1, (-1 + i√3)/2, (-1 - i√3)/2`.
-/

namespace Imc2017P1

open Matrix

/-- The answer: the set of complex `μ` with `μ⁴ = μ`. -/
determine answer : Set ℂ := {μ | μ ^ 4 = μ}

snip begin

/-- The 2×2 real matrix realizing the primitive cube roots of unity as eigenvalues:
rotation by `2π/3`. -/
noncomputable def A2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-1/2, Real.sqrt 3 / 2; -(Real.sqrt 3 / 2), -1/2]

lemma sqrt3_sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- `A2² = A2ᵀ`. -/
lemma A2_sq_eq_transpose : A2 ^ 2 = A2.transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A2, Matrix.transpose, pow_two, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    nlinarith [sqrt3_sq, Real.sqrt_nonneg 3]

/-- The complex-valued version of `A2`: applying `algebraMap ℝ ℂ` entrywise. -/
noncomputable def A2C : Matrix (Fin 2) (Fin 2) ℂ := A2.map ((algebraMap ℝ ℂ))

/-- Explicit entries of `A2C`. -/
lemma A2C_eq : A2C = !![((-1 / 2 : ℝ) : ℂ), ((Real.sqrt 3 / 2 : ℝ) : ℂ);
                         ((-(Real.sqrt 3 / 2) : ℝ) : ℂ), ((-1/2 : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A2C, A2, Matrix.map_apply]

/-- `A2C *ᵥ ![1, i] = ((-1 + i√3)/2) • ![1, i]`. -/
lemma A2C_mulVec_pos :
    A2C *ᵥ ![(1 : ℂ), Complex.I] =
      ((-1 + Complex.I * Real.sqrt 3) / 2) • ![1, Complex.I] := by
  rw [A2C_eq]
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons] <;>
    ring_nf <;>
    rw [Complex.I_sq] <;>
    ring

/-- `A2C *ᵥ ![1, -i] = ((-1 - i√3)/2) • ![1, -i]`. -/
lemma A2C_mulVec_neg :
    A2C *ᵥ ![(1 : ℂ), -Complex.I] =
      ((-1 - Complex.I * Real.sqrt 3) / 2) • ![1, -Complex.I] := by
  rw [A2C_eq]
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons] <;>
    ring_nf <;>
    rw [Complex.I_sq] <;>
    ring

/-- `![1, I] ≠ 0`. -/
lemma ne_zero_1_I : (![1, Complex.I] : Fin 2 → ℂ) ≠ 0 := by
  intro h
  have : (![1, Complex.I] : Fin 2 → ℂ) 0 = 0 := by rw [h]; rfl
  simp at this

/-- `![1, -I] ≠ 0`. -/
lemma ne_zero_1_negI : (![1, -Complex.I] : Fin 2 → ℂ) ≠ 0 := by
  intro h
  have : (![1, -Complex.I] : Fin 2 → ℂ) 0 = 0 := by rw [h]; rfl
  simp at this

/-- `λ = (-1 + i√3)/2` is an eigenvalue of `A2` over `ℂ`. -/
lemma hasEigenvalue_A2_pos :
    Module.End.HasEigenvalue (Matrix.toLin' A2C) ((-1 + Complex.I * Real.sqrt 3) / 2) := by
  apply Module.End.hasEigenvalue_of_hasEigenvector
  refine ⟨?_, ne_zero_1_I⟩
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  exact A2C_mulVec_pos

/-- `λ = (-1 - i√3)/2` is an eigenvalue of `A2` over `ℂ`. -/
lemma hasEigenvalue_A2_neg :
    Module.End.HasEigenvalue (Matrix.toLin' A2C) ((-1 - Complex.I * Real.sqrt 3) / 2) := by
  apply Module.End.hasEigenvalue_of_hasEigenvector
  refine ⟨?_, ne_zero_1_negI⟩
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  exact A2C_mulVec_neg

snip end

problem imc2017_p1 (lam : ℂ) :
    lam ∈ answer ↔
    ∃ (n : ℕ) (_ : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ),
      A ^ 2 = A.transpose ∧
      Module.End.HasEigenvalue
        (Matrix.toLin' (A.map ((algebraMap ℝ ℂ)))) lam := by
  constructor
  · -- Forward: if λ⁴ = λ, exhibit a suitable A.
    intro h
    change lam ^ 4 = lam at h
    -- Factor: λ⁴ - λ = λ(λ - 1)(λ² + λ + 1) = 0.
    have hfact : lam * (lam - 1) * (lam ^ 2 + lam + 1) = 0 := by
      have : lam * (lam - 1) * (lam ^ 2 + lam + 1) = lam ^ 4 - lam := by ring
      rw [this, h, sub_self]
    rcases mul_eq_zero.mp hfact with h01 | hquad
    · rcases mul_eq_zero.mp h01 with h0 | h1
      · -- lam = 0.
        refine ⟨1, Nat.one_pos, 0, ?_, ?_⟩
        · simp
        · rw [h0]
          apply Module.End.hasEigenvalue_of_hasEigenvector (x := ![1])
          refine ⟨?_, ?_⟩
          · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
            simp
          · intro hc
            have : (![(1 : ℂ)] : Fin 1 → ℂ) 0 = 0 := by rw [hc]; rfl
            simp at this
      · -- lam = 1.
        have hlam : lam = 1 := sub_eq_zero.mp h1
        refine ⟨1, Nat.one_pos, 1, ?_, ?_⟩
        · ext i j
          fin_cases i; fin_cases j
          simp [pow_two, Matrix.mul_apply, Matrix.transpose, Fin.sum_univ_succ]
        · rw [hlam]
          apply Module.End.hasEigenvalue_of_hasEigenvector (x := ![1])
          refine ⟨?_, ?_⟩
          · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
            ext i
            fin_cases i
            simp [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.one_apply,
                  Fin.sum_univ_succ]
          · intro hc
            have : (![(1 : ℂ)] : Fin 1 → ℂ) 0 = 0 := by rw [hc]; rfl
            simp at this
    · -- λ² + λ + 1 = 0. Roots are (-1 ± i√3)/2.
      have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
        have : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
        exact_mod_cast this
      have hprod : (lam - (-1 + Complex.I * Real.sqrt 3) / 2) *
                   (lam - (-1 - Complex.I * Real.sqrt 3) / 2) = 0 := by
        have hexp : (lam - (-1 + Complex.I * Real.sqrt 3) / 2) *
               (lam - (-1 - Complex.I * Real.sqrt 3) / 2) =
               lam ^ 2 + lam + (1 - Complex.I ^ 2 * (Real.sqrt 3 : ℂ) ^ 2) / 4 := by ring
        rw [hexp, Complex.I_sq, h3]
        have : ((1 - (-1 : ℂ) * 3) / 4 : ℂ) = 1 := by ring
        rw [this]
        exact hquad
      rcases mul_eq_zero.mp hprod with h | h
      · refine ⟨2, by omega, A2, A2_sq_eq_transpose, ?_⟩
        have hlam : lam = (-1 + Complex.I * Real.sqrt 3) / 2 := sub_eq_zero.mp h
        rw [hlam]
        exact hasEigenvalue_A2_pos
      · refine ⟨2, by omega, A2, A2_sq_eq_transpose, ?_⟩
        have hlam : lam = (-1 - Complex.I * Real.sqrt 3) / 2 := sub_eq_zero.mp h
        rw [hlam]
        exact hasEigenvalue_A2_neg
  · -- Reverse: if λ is eigenvalue of some real A with A²=Aᵀ, then λ⁴ = λ.
    rintro ⟨n, hn, A, hEq, hev⟩
    change lam ^ 4 = lam
    -- A⁴ = A over ℝ.
    have hA4 : A ^ 4 = A := by
      have h1 : A ^ 4 = (A ^ 2) ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
      rw [h1, hEq]
      rw [show (Aᵀ)^2 = (A^2).transpose from (Matrix.transpose_pow A 2).symm]
      rw [hEq, Matrix.transpose_transpose]
    set ι : ℝ →+* ℂ := algebraMap ℝ ℂ
    set A_C : Matrix (Fin n) (Fin n) ℂ := A.map ι with hA_C
    have hA_C4 : A_C ^ 4 = A_C := by
      have := congrArg ι.mapMatrix hA4
      simp only [map_pow, RingHom.mapMatrix_apply] at this
      simpa [A_C] using this
    set φ : Module.End ℂ (Fin n → ℂ) := A_C.toLin' with hφ_def
    -- Use `aeval A_C p = 0` for `p = X^4 - X` and transport to `φ`.
    let p : Polynomial ℂ := Polynomial.X ^ 4 - Polynomial.X
    have hp_A_C : (Polynomial.aeval A_C) p = 0 := by
      simp only [p, map_sub, map_pow, Polynomial.aeval_X]
      rw [hA_C4]
      exact sub_self A_C
    have hp_phi : (Polynomial.aeval φ) p = 0 := by
      let f : Matrix (Fin n) (Fin n) ℂ →ₐ[ℂ] Module.End ℂ (Fin n → ℂ) :=
        Matrix.toLinAlgEquiv'.toAlgHom
      have hφ : f A_C = φ := by
        apply LinearMap.ext
        intro v
        simp [f, φ, Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]
      calc (Polynomial.aeval φ) p = (Polynomial.aeval (f A_C)) p := by rw [hφ]
        _ = f ((Polynomial.aeval A_C) p) := Polynomial.aeval_algHom_apply f A_C p
        _ = f 0 := by rw [hp_A_C]
        _ = 0 := map_zero _
    obtain ⟨x, hx_mem, hx_ne⟩ := hev.exists_hasEigenvector
    have hp_lam : p.eval lam = 0 := by
      have haeval : (Polynomial.aeval φ p) x = p.eval lam • x :=
        Module.End.aeval_apply_of_hasEigenvector ⟨hx_mem, hx_ne⟩
      rw [hp_phi, LinearMap.zero_apply] at haeval
      exact (smul_eq_zero.mp haeval.symm).resolve_right hx_ne
    have hp_eval : p.eval lam = lam ^ 4 - lam := by simp [p]
    linear_combination hp_lam - hp_eval


end Imc2017P1
