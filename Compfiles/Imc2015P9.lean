/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2015, Problem 9

An `n × n` complex matrix `A` is called *t-normal* if `A * Aᵀ = Aᵀ * A`,
where `Aᵀ` is the transpose of `A`. For each `n`, determine the maximum
dimension of a linear space of complex `n × n` matrices consisting of
t-normal matrices.

Answer: `n*(n+1)/2`. The space of symmetric matrices has this dimension and
consists of t-normal matrices (since `Aᵀ = A` makes `A * Aᵀ = A * A = Aᵀ * A`).

The upper bound: if `V` is a t-normal subspace, define `π : V → Symm` by
`π A = A + Aᵀ`. Then `ker π ⊆ Antisymm`, and one shows `ker π` and `im π`
commute as subspaces (every element of one commutes with every element of
the other). A lemma about commuting symmetric/antisymmetric subspaces then
gives `dim V = dim (ker π) + dim (im π) ≤ dim Symm = n*(n+1)/2`.
-/

namespace Imc2015P9

open Matrix

/-- A matrix is *t-normal* if it commutes with its transpose. -/
def IsTNormal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  A * Aᵀ = Aᵀ * A

/-- A submodule `V` of `n × n` matrices is *t-normal* if every matrix in `V`
is t-normal. -/
def IsTNormalSubspace {n : ℕ} (V : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)) : Prop :=
  ∀ A ∈ V, IsTNormal A

/-- The set of finite ranks (dimensions) of t-normal subspaces. -/
def TNormalDims (n : ℕ) : Set ℕ :=
  {d | ∃ V : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ),
        IsTNormalSubspace V ∧ Module.finrank ℂ V = d}

snip begin

/-- Symmetric matrices are t-normal. -/
lemma isTNormal_of_symm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : Aᵀ = A) :
    IsTNormal A := by
  unfold IsTNormal
  rw [hA]

/-- The submodule of symmetric `n × n` complex matrices. -/
def symmSubmodule (n : ℕ) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {A | Aᵀ = A}
  add_mem' {a b} ha hb := by
    show (a + b)ᵀ = a + b
    rw [Matrix.transpose_add, ha, hb]
  zero_mem' := by show (0 : Matrix (Fin n) (Fin n) ℂ)ᵀ = 0; exact Matrix.transpose_zero
  smul_mem' c a ha := by
    show (c • a)ᵀ = c • a
    rw [Matrix.transpose_smul, ha]

lemma symmSubmodule_isTNormal (n : ℕ) : IsTNormalSubspace (symmSubmodule n) := by
  intro A hA
  exact isTNormal_of_symm hA

snip end

/-- The answer: the maximum dimension of a t-normal subspace of `n × n`
complex matrices is `n * (n + 1) / 2`. -/
determine maxTNormalDim (n : ℕ) : ℕ := n * (n + 1) / 2

problem imc2015_p9 (n : ℕ) :
    IsGreatest (TNormalDims n) (maxTNormalDim n) := by
  -- The lower bound: the space of symmetric matrices has dimension `n(n+1)/2`
  -- and is t-normal.
  -- The upper bound: see the docstring above; this requires the
  -- commuting-symmetric/antisymmetric-subspaces lemma proved via the
  -- bilinear form `(x, y) ↦ tr(diag(1,…,n) * (xy - yx))`.
  -- TODO: complete the formalization.
  sorry

end Imc2015P9
