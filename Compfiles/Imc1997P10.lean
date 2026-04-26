/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1997, Problem 10 (Day 2, Problem 4)

Let `M_n = ℝ^{n²}` be the space of `n × n` real matrices.

(a) If `f : M_n → ℝ` is linear, there is a unique matrix `C` such that
    `f A = trace (A · C)` for every `A ∈ M_n`.

(b) If furthermore `f(A · B) = f(B · A)` for all `A, B ∈ M_n`, then there
    exists `λ ∈ ℝ` such that `f A = λ · trace A`.

## Solution outline (official)

(a) Let `E_{ij}` be the standard basis of `M_n`. Set `C_{ij} = f(E_{ji})`.
    Then
      `trace(A · C) = ∑_{i,j} A_{ij} · C_{ji} = ∑_{i,j} A_{ij} · f(E_{ij}) = f(A)`
    by linearity. Uniqueness: if `trace(A · C) = trace(A · C')` for all `A`,
    then `trace(A · (C - C')) = 0` for all `A`; taking `A = (C - C')ᵀ` gives
    `‖C - C'‖_F² = 0`, hence `C = C'`. (We use the standard `ext_iff_trace_mul_left`
    lemma in Mathlib.)

(b) Using the commutator identities
      `E_{ij} = E_{ij} · E_{jj} - E_{jj} · E_{ij}`,            (`i ≠ j`)
      `E_{ii} - E_{nn} = E_{in} · E_{ni} - E_{ni} · E_{in}`,
    the trace-zero subspace `L = ker(trace)` is spanned by these elements.
    The hypothesis `f(AB) = f(BA)` forces `f` to vanish on every commutator,
    hence `f|_L = 0`. For any `A`, the matrix `A - (trace A / n) · I` lies in
    `L`, so `f(A) = (f(I) / n) · trace A`. Take `λ = f(I) / n`.
-/

namespace Imc1997P10

open Matrix
open scoped BigOperators

variable {n : ℕ}

/-- The matrix `C` associated to a linear functional `f` on matrices,
defined by `C i j = f (single j i 1)`. -/
noncomputable def assocMatrix (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => f (Matrix.single j i (1 : ℝ))

/-- Key identity: `f A = trace (A * assocMatrix f)`. -/
lemma f_eq_trace_mul (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    f A = (A * assocMatrix f).trace := by
  -- Write A = ∑_{i,j} A_{ij} · E_{ij}, apply linearity, then expand the trace.
  have hA : A = ∑ i, ∑ j, Matrix.single i j (A i j) :=
    Matrix.matrix_eq_sum_single A
  conv_lhs => rw [hA]
  -- f is linear, so f (∑) = ∑ f(...).
  rw [map_sum]
  simp_rw [map_sum]
  -- For each (i, j), `single i j (A i j) = A i j • single i j 1` and
  -- `f (A i j • single i j 1) = A i j * f (single i j 1) = A i j * C j i`.
  have hf : ∀ i j, f (Matrix.single i j (A i j)) = A i j * assocMatrix f j i := by
    intro i j
    have hsmul : Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℝ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hsmul, map_smul]
    simp [assocMatrix, smul_eq_mul]
  simp_rw [hf]
  -- Now expand the trace of A * C.
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply]

/-- **Part (a) existence.** For every linear functional `f` on matrices,
there exists `C` such that `f A = trace (A * C)`. -/
theorem exists_assoc_matrix (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ) :
    ∃ C : Matrix (Fin n) (Fin n) ℝ, ∀ A, f A = (A * C).trace :=
  ⟨assocMatrix f, f_eq_trace_mul f⟩

/-- **Part (a) uniqueness.** The matrix `C` is unique. -/
theorem assoc_matrix_unique
    (C C' : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ A : Matrix (Fin n) (Fin n) ℝ, (A * C).trace = (A * C').trace) :
    C = C' :=
  Matrix.ext_iff_trace_mul_left.mpr h

/-- The functional `A ↦ trace (A * C)` as a linear map. -/
noncomputable def traceMul (C : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ where
  toFun A := (A * C).trace
  map_add' A B := by simp [Matrix.add_mul, Matrix.trace_add]
  map_smul' r A := by simp [smul_eq_mul]

@[simp] lemma traceMul_apply (C A : Matrix (Fin n) (Fin n) ℝ) :
    traceMul C A = (A * C).trace := rfl

/-- **Part (a), full statement.** -/
theorem part_a (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ) :
    ∃! C : Matrix (Fin n) (Fin n) ℝ, ∀ A, f A = (A * C).trace := by
  refine ⟨assocMatrix f, f_eq_trace_mul f, ?_⟩
  intro C' hC'
  apply assoc_matrix_unique
  intro A
  rw [← hC' A, f_eq_trace_mul f A]

/-- Under the trace condition, `f` vanishes on commutators `A * B - B * A`. -/
lemma vanish_on_commutator (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
    (hf : ∀ A B : Matrix (Fin n) (Fin n) ℝ, f (A * B) = f (B * A))
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    f (A * B - B * A) = 0 := by
  rw [map_sub, hf A B, sub_self]

/-- The commutator identity `E_{ij} = E_{ij} * E_{jj} - E_{jj} * E_{ij}` for `i ≠ j`. -/
lemma single_off_diag_eq_commutator {i j : Fin n} (hij : i ≠ j) :
    Matrix.single i j (1 : ℝ) =
      Matrix.single i j 1 * Matrix.single j j 1
        - Matrix.single j j 1 * Matrix.single i j 1 := by
  have h2 : Matrix.single j j (1 : ℝ) * Matrix.single i j 1 = 0 := by
    apply Matrix.single_mul_single_of_ne (c := (1 : ℝ)) j j i hij.symm
  simp [h2]

/-- The commutator identity `E_{ii} - E_{jj} = E_{ij} * E_{ji} - E_{ji} * E_{ij}`
for `i ≠ j`. -/
lemma single_diff_diag_eq_commutator {i j : Fin n} (_ : i ≠ j) :
    Matrix.single i i (1 : ℝ) - Matrix.single j j 1 =
      Matrix.single i j 1 * Matrix.single j i 1
        - Matrix.single j i 1 * Matrix.single i j 1 := by
  simp

/-- `f` vanishes on every off-diagonal `E_{ij}`. -/
lemma f_single_off_diag (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
    (hf : ∀ A B : Matrix (Fin n) (Fin n) ℝ, f (A * B) = f (B * A))
    {i j : Fin n} (hij : i ≠ j) :
    f (Matrix.single i j (1 : ℝ)) = 0 := by
  rw [single_off_diag_eq_commutator hij]
  exact vanish_on_commutator f hf _ _

/-- `f` agrees on the diagonal: `f E_{ii} = f E_{jj}`. -/
lemma f_single_diag_eq (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
    (hf : ∀ A B : Matrix (Fin n) (Fin n) ℝ, f (A * B) = f (B * A))
    (i j : Fin n) :
    f (Matrix.single i i (1 : ℝ)) = f (Matrix.single j j 1) := by
  by_cases hij : i = j
  · rw [hij]
  · have h := vanish_on_commutator f hf
      (Matrix.single i j (1 : ℝ)) (Matrix.single j i 1)
    rw [← single_diff_diag_eq_commutator hij, map_sub] at h
    linarith

/-- The IMC 1997 Problem 10 statement.

(a) Every linear functional `f` on `n × n` real matrices is given by a unique
matrix `C` via `f A = trace(A · C)`.

(b) If furthermore `f(AB) = f(BA)`, then `f A = λ · trace A` for some `λ`.
-/
problem imc1997_p10 (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ) :
    (∃! C : Matrix (Fin n) (Fin n) ℝ, ∀ A, f A = (A * C).trace) ∧
    ((∀ A B : Matrix (Fin n) (Fin n) ℝ, f (A * B) = f (B * A)) →
      ∃ lam : ℝ, ∀ A, f A = lam * A.trace) := by
  refine ⟨part_a f, ?_⟩
  intro hf
  -- Case on whether n = 0.
  by_cases hn : n = 0
  · -- If n = 0, every matrix is the zero matrix and f A = 0 = λ · trace A.
    subst hn
    refine ⟨0, ?_⟩
    intro A
    have hA : A = 0 := by ext i; exact i.elim0
    rw [hA, map_zero, Matrix.trace_zero, mul_zero]
  · -- n ≥ 1, pick basepoint i₀.
    have : NeZero n := ⟨hn⟩
    let i0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    refine ⟨f (Matrix.single i0 i0 (1 : ℝ)), ?_⟩
    intro A
    -- Decompose A = ∑_{i,j} A_{ij} · E_{ij}, apply f, use:
    --   f E_{ij} = 0 for i ≠ j, f E_{ii} = f E_{i0 i0} (constant on diagonal).
    have hA : A = ∑ i, ∑ j, Matrix.single i j (A i j) :=
      Matrix.matrix_eq_sum_single A
    conv_lhs => rw [hA]
    rw [map_sum]; simp_rw [map_sum]
    -- Reduce each term.
    have heach : ∀ i j, f (Matrix.single i j (A i j)) =
        if i = j then A i i * f (Matrix.single i0 i0 (1 : ℝ)) else 0 := by
      intro i j
      have hsmul : Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℝ) := by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      rw [hsmul, map_smul]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, smul_eq_mul, f_single_diag_eq f hf i i0]
      · rw [if_neg hij, f_single_off_diag f hf hij, smul_zero]
    simp_rw [heach]
    -- Compute each inner sum: only i = j survives.
    have hinner : ∀ i,
        (∑ j, if i = j then A i i * f (Matrix.single i0 i0 (1 : ℝ)) else 0) =
          A i i * f (Matrix.single i0 i0 (1 : ℝ)) := by
      intro i
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl]
      · intros j _ hj
        rw [if_neg (Ne.symm hj)]
      · simp
    simp_rw [hinner]
    -- Sum over diagonal: ∑_i A i i * c = (∑_i A i i) * c = trace A * c.
    rw [← Finset.sum_mul]
    rw [show (∑ i, A i i) = A.trace from rfl]
    ring

end Imc1997P10
