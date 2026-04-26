/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1995, Problem 7 (Day 2 Problem 1)

Let `A` be a `3 × 3` real matrix such that `Au ⟂ u` for every `u ∈ ℝ^3`. Prove:

(a) `Aᵀ = -A`;

(b) there exists `v ∈ ℝ^3` such that `Au = v ⨯₃ u` for every `u`.

## Proof outline

(a) Polarize the identity `(Au) ⬝ u = 0`. Setting `u = e_k` gives `a_{kk} = 0`.
    Setting `u = e_k + e_m` gives `a_{km} + a_{mk} = 0`, so `Aᵀ = -A`.

(b) Take `v = (-a_{23}, a_{13}, -a_{12})` and check the components.
-/

namespace Imc1995P7

open scoped Matrix
open Matrix

/-- The hypothesis: `(A *ᵥ u) ⬝ u = 0` for all `u`. -/
private lemma diag_zero (A : Matrix (Fin 3) (Fin 3) ℝ)
    (h : ∀ u : Fin 3 → ℝ, (A *ᵥ u) ⬝ᵥ u = 0) (k : Fin 3) :
    A k k = 0 := by
  have hk := h (Pi.single k 1)
  -- Compute (A *ᵥ Pi.single k 1) ⬝ᵥ Pi.single k 1 = A k k.
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq'] at hk
  exact hk

/-- Polarization identity from `(A *ᵥ u) ⬝ᵥ u = 0`. -/
private lemma offdiag_anti (A : Matrix (Fin 3) (Fin 3) ℝ)
    (h : ∀ u : Fin 3 → ℝ, (A *ᵥ u) ⬝ᵥ u = 0) (k m : Fin 3) :
    A k m + A m k = 0 := by
  have hkm := h (Pi.single k 1 + Pi.single m 1)
  have hk := diag_zero A h k
  have hm := diag_zero A h m
  -- Expand:
  -- (A *ᵥ (e_k + e_m)) ⬝ (e_k + e_m)
  --   = (A *ᵥ e_k) ⬝ e_k + (A *ᵥ e_k) ⬝ e_m + (A *ᵥ e_m) ⬝ e_k + (A *ᵥ e_m) ⬝ e_m
  --   = a_{kk} + a_{mk} + a_{km} + a_{mm}
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, Pi.add_apply,
        Finset.sum_add_distrib, Finset.sum_ite_eq', mul_add] at hkm
  -- After simp, `hkm` should reduce to `A k m + A m k + (A k k + A m m) = 0` or similar.
  -- We have hk : A k k = 0 and hm : A m m = 0.
  linarith [hk, hm, hkm]

/-- Part (a): `Aᵀ = -A`. -/
private lemma transpose_eq_neg (A : Matrix (Fin 3) (Fin 3) ℝ)
    (h : ∀ u : Fin 3 → ℝ, (A *ᵥ u) ⬝ᵥ u = 0) :
    Aᵀ = -A := by
  ext i j
  by_cases hij : i = j
  · subst hij
    have := diag_zero A h i
    simp [Matrix.transpose_apply, this]
  · have := offdiag_anti A h j i
    simp [Matrix.transpose_apply]
    linarith

/-- The candidate vector `v = (-a_{23}, a_{13}, -a_{12})`. -/
private def vCand (A : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → ℝ :=
  ![-A 1 2, A 0 2, -A 0 1]

/-- Part (b): cross product representation. -/
private lemma cross_repr (A : Matrix (Fin 3) (Fin 3) ℝ)
    (h : ∀ u : Fin 3 → ℝ, (A *ᵥ u) ⬝ᵥ u = 0) (u : Fin 3 → ℝ) :
    A *ᵥ u = (vCand A) ⨯₃ u := by
  -- Use part (a) to relate diagonals to 0 and a_{ji} = -a_{ij}.
  have hd : ∀ k, A k k = 0 := diag_zero A h
  have ha : ∀ k m, A k m + A m k = 0 := offdiag_anti A h
  have h01 : A 1 0 = - A 0 1 := by linarith [ha 0 1]
  have h02 : A 2 0 = - A 0 2 := by linarith [ha 0 2]
  have h12 : A 2 1 = - A 1 2 := by linarith [ha 1 2]
  ext i
  fin_cases i <;>
    (simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, vCand, crossProduct,
           LinearMap.mk₂_apply, Matrix.cons_val, hd 0, hd 1, hd 2,
           h01, h02, h12]
     try ring)

/-- The main statement. -/
problem imc1995_p7 (A : Matrix (Fin 3) (Fin 3) ℝ)
    (h : ∀ u : Fin 3 → ℝ, (A *ᵥ u) ⬝ᵥ u = 0) :
    Aᵀ = -A ∧ ∃ v : Fin 3 → ℝ, ∀ u : Fin 3 → ℝ, A *ᵥ u = v ⨯₃ u :=
  ⟨transpose_eq_neg A h, ⟨vCand A, cross_repr A h⟩⟩

end Imc1995P7
