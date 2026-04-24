/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2004, Problem 10
(IMC 2004, Day 2, Problem 4)

For `n ≥ 1`, let `M` be an `n × n` complex matrix with distinct eigenvalues
`λ₁, …, λ_k` of multiplicities `m₁, …, m_k`.  Consider the linear operator
`L_M(X) = M X + X Mᵀ` on complex `n × n` matrices.  Find its eigenvalues and
their multiplicities.

Answer: for every pair `(r, s)`, the number `λ_r + λ_s` is an eigenvalue of
`L_M`; with multiplicities `m_r²` for `2 λ_r` and `2 m_r m_s` for
`λ_r + λ_s` with `r < s`.

We formalize the key part of the problem: for every pair `(r, s)` of
eigenvalues of `M`, the sum `λ_r + λ_s` is an eigenvalue of `L_M`, via the
explicit eigenmatrix `v_r v_sᵀ` (the outer product of an eigenvector of `M`
for `λ_r` with one for `λ_s`).
-/

namespace Imc2004P10

open Matrix

/-- The Lyapunov-type operator `L_M(X) = M X + X Mᵀ` on `n × n` complex
matrices, realised as a `ℂ`-linear endomorphism. -/
noncomputable def L {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    Module.End ℂ (Matrix (Fin n) (Fin n) ℂ) where
  toFun X := M * X + X * Mᵀ
  map_add' X Y := by
    simp [Matrix.mul_add, Matrix.add_mul]; abel
  map_smul' c X := by
    dsimp
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_add]

@[simp] lemma L_apply {n : ℕ} (M X : Matrix (Fin n) (Fin n) ℂ) :
    L M X = M * X + X * Mᵀ := rfl

snip begin

/-
Special case first.  If `M v_r = λ_r v_r` and `M v_s = λ_s v_s`, then the
outer product `X := v_r v_sᵀ = vecMulVec v_r v_s` satisfies
  `M * X           = vecMulVec (M *ᵥ v_r) v_s = λ_r • X`,
  `X * Mᵀ          = vecMulVec v_r (v_s ᵥ* Mᵀ) = vecMulVec v_r (M *ᵥ v_s)
                                               = λ_s • X`,
so `L_M X = (λ_r + λ_s) • X`.  Since `v_r, v_s ≠ 0`, also `X ≠ 0`, so
`λ_r + λ_s` is an eigenvalue of `L_M`.

The full multiplicity statement follows by continuity of eigenvalues from the
generic case where all sums `λ_r + λ_s` are distinct; we do not formalize
that refinement.
-/

snip end

/-- Key lemma: if `v_r` is a `λ_r`-eigenvector of `M` and `v_s` is a
`λ_s`-eigenvector of `M`, then `v_r v_sᵀ` is a `(λ_r + λ_s)`-eigenmatrix
of `L_M`. -/
lemma L_apply_vecMulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    {lr ls : ℂ} {vr vs : Fin n → ℂ}
    (hvr : M *ᵥ vr = lr • vr) (hvs : M *ᵥ vs = ls • vs) :
    L M (vecMulVec vr vs) = (lr + ls) • vecMulVec vr vs := by
  rw [L_apply]
  rw [mul_vecMulVec, hvr, Matrix.smul_vecMulVec]
  rw [vecMulVec_mul, vecMul_transpose, hvs, Matrix.vecMulVec_smul]
  rw [add_smul]

/-- The main result (easy direction): for every pair of eigenvalues
`lr, ls` of a complex `n × n` matrix `M`, the sum `lr + ls` is an
eigenvalue of the operator `L_M`. -/
problem imc2004_p10 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (lr ls : ℂ)
    (hr : Module.End.HasEigenvalue (Matrix.toLin' M) lr)
    (hs : Module.End.HasEigenvalue (Matrix.toLin' M) ls) :
    Module.End.HasEigenvalue (L M) (lr + ls) := by
  obtain ⟨vr, hvr_mem, hvr_ne⟩ := hr.exists_hasEigenvector
  obtain ⟨vs, hvs_mem, hvs_ne⟩ := hs.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hvr_mem hvs_mem
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := vecMulVec vr vs)
  refine ⟨?_, vecMulVec_ne_zero hvr_ne hvs_ne⟩
  rw [Module.End.mem_eigenspace_iff]
  exact L_apply_vecMulVec M hvr_mem hvs_mem

end Imc2004P10
