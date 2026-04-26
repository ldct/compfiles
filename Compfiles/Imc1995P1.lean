/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Matrix.ToLin

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1995, Problem 1 (Day 1)

Let `X` be a nonsingular `(n+1) × (n+1)` matrix with columns `X₀, X₁, …, X_n`.
Let `Y` be the matrix with columns `X₁, X₂, …, X_n, 0`. Show that
`A = Y X⁻¹` and `B = X⁻¹ Y` have rank `n` and only zero eigenvalues.

## Proof outline

Let `J : Matrix (Fin (n+1)) (Fin (n+1)) ℝ` be the subdiagonal shift,
`J k j = if (k : ℕ) = (j : ℕ) + 1 then 1 else 0`. Then `Y = X * J`.

Hence `B = X⁻¹ * Y = J` and `A = Y * X⁻¹ = X * J * X⁻¹` is conjugate to `J`.

* Rank `n`: rank is preserved by left/right multiplication by invertible
  matrices, so it suffices to show `J` has rank `n`. The column space of `J`
  is the codimension-1 subspace `{w : w 0 = 0}` of `ℝ^{n+1}`, which has
  dimension `n`. Linear independence is shown via the family of standard
  basis vectors at indices `1, …, n`, each of which is a column of `J`.
* Only zero eigenvalues: `J^{n+1} = 0`, so `J` (and `A`, similar to `J`) is
  nilpotent, and any eigenvalue must satisfy `μ^{n+1} = 0`.
-/

namespace Imc1995P1

open scoped Matrix
open Matrix

/-- The subdiagonal shift matrix on `Fin (n+1)`. -/
def J (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun k j => if (k : ℕ) = (j : ℕ) + 1 then 1 else 0

/-- The "shifted-column" matrix `Y` from a matrix `X`: column `j` of `Y` is
column `j+1` of `X` if `j+1 ≤ n`, and zero if `j = n`. -/
def shiftColumns {n : ℕ} (X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => if h : (j : ℕ) + 1 < n + 1 then X i ⟨(j : ℕ) + 1, h⟩ else 0

snip begin

/-- `Y = X * J`. -/
lemma shiftColumns_eq_mul_J {n : ℕ} (X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    shiftColumns X = X * J n := by
  ext i j
  simp only [shiftColumns, J, Matrix.mul_apply]
  by_cases hj : (j : ℕ) + 1 < n + 1
  · rw [dif_pos hj]
    rw [Finset.sum_eq_single (⟨(j : ℕ) + 1, hj⟩ : Fin (n+1))]
    · simp
    · intro k _ hk
      have hkne : (k : ℕ) ≠ (j : ℕ) + 1 := fun h => hk (Fin.ext h)
      simp [hkne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [dif_neg hj]
    symm
    apply Finset.sum_eq_zero
    intro k _
    have hkne : (k : ℕ) ≠ (j : ℕ) + 1 := by
      intro h
      apply hj
      rw [← h]
      exact k.isLt
    simp [hkne]

/-- For all `m`, `(J n)^m k j = 1` iff `(k : ℕ) = (j : ℕ) + m`, else `0`. -/
lemma J_pow_apply (n m : ℕ) (k j : Fin (n+1)) :
    ((J n) ^ m) k j = if (k : ℕ) = (j : ℕ) + m then (1 : ℝ) else 0 := by
  induction m generalizing k j with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, Nat.add_zero]
    by_cases h : k = j
    · simp [h]
    · simp [h]
      intro hkj
      exact h (Fin.ext hkj)
  | succ m ih =>
    rw [pow_succ, Matrix.mul_apply]
    -- ∑ l, ((J n)^m) k l * J n l j
    -- = ∑ l, [(k : ℕ) = (l : ℕ) + m] * [(l : ℕ) = (j : ℕ) + 1]
    by_cases hk : (k : ℕ) = (j : ℕ) + (m + 1)
    · rw [if_pos hk]
      by_cases hjsucc : (j : ℕ) + 1 < n + 1
      · let l : Fin (n+1) := ⟨(j : ℕ) + 1, hjsucc⟩
        rw [Finset.sum_eq_single l]
        · rw [ih]
          have : (k : ℕ) = ((l : Fin (n+1)) : ℕ) + m := by
            show (k : ℕ) = (j : ℕ) + 1 + m
            omega
          rw [if_pos this]
          show (1 : ℝ) * (J n) l j = 1
          simp [J, l]
        · intro b _ hbl
          have hbne : (b : ℕ) ≠ (j : ℕ) + 1 := fun heq => hbl (Fin.ext heq)
          show ((J n)^m) k b * J n b j = 0
          simp [J, hbne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · exfalso
        have : (k : ℕ) < n + 1 := k.isLt
        omega
    · rw [if_neg hk]
      apply Finset.sum_eq_zero
      intro l _
      show ((J n)^m) k l * J n l j = 0
      rw [ih]
      simp only [J]
      by_cases hlj : (l : ℕ) = (j : ℕ) + 1
      · rw [if_pos hlj]
        by_cases hkl : (k : ℕ) = (l : ℕ) + m
        · exfalso; apply hk; omega
        · rw [if_neg hkl]; ring
      · rw [if_neg hlj]; ring

/-- `J^{n+1} = 0`. -/
lemma J_pow_succ_eq_zero (n : ℕ) : (J n) ^ (n + 1) = 0 := by
  ext k j
  rw [J_pow_apply]
  have : (k : ℕ) ≠ (j : ℕ) + (n + 1) := by
    have hk : (k : ℕ) < n + 1 := k.isLt
    omega
  simp [this]

/-- `J` is nilpotent. -/
lemma J_isNilpotent (n : ℕ) : IsNilpotent (J n) :=
  ⟨n + 1, J_pow_succ_eq_zero n⟩

/-- Column `i.castSucc` of `J n` is the standard basis vector `e_{i.succ}`. -/
lemma J_mulVec_single_castSucc (n : ℕ) (i : Fin n) :
    (J n) *ᵥ (Pi.single (i.castSucc : Fin (n+1)) (1 : ℝ)) =
      Pi.single (i.succ : Fin (n+1)) 1 := by
  ext k
  simp only [Matrix.mulVec, dotProduct, J]
  rw [Finset.sum_eq_single (i.castSucc : Fin (n+1))]
  · -- Term at b = i.castSucc.
    -- (if k = (i.castSucc) + 1 then 1 else 0) * (Pi.single i.castSucc 1) i.castSucc
    rw [Pi.single_eq_same]
    by_cases hk : (k : ℕ) = (i.castSucc : ℕ) + 1
    · rw [if_pos hk, mul_one]
      have hkeq : k = i.succ := by
        apply Fin.ext
        rw [hk, Fin.val_castSucc, Fin.val_succ]
      rw [hkeq, Pi.single_eq_same]
    · rw [if_neg hk, zero_mul]
      have hkne : k ≠ i.succ := by
        intro heq
        apply hk
        rw [heq, Fin.val_succ, Fin.val_castSucc]
      rw [Pi.single_apply, if_neg hkne]
  · intro b _ hb
    have hzero : (Pi.single (i.castSucc : Fin (n+1)) (1 : ℝ) : Fin (n+1) → ℝ) b = 0 := by
      rw [Pi.single_apply]; rw [if_neg hb]
    rw [hzero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Rank of `J n` is `n`. -/
lemma J_rank (n : ℕ) : (J n).rank = n := by
  apply le_antisymm
  · -- rank ≤ n: column space ⊆ ker (proj 0)
    have hsub : LinearMap.range (J n).mulVecLin ≤
        (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (n+1) => ℝ) 0).ker := by
      rintro w ⟨v, rfl⟩
      simp only [LinearMap.mem_ker, LinearMap.proj_apply]
      show ((J n) *ᵥ v) 0 = 0
      simp only [Matrix.mulVec, dotProduct, J]
      apply Finset.sum_eq_zero
      intro j _
      have hne : ((0 : Fin (n+1)) : ℕ) ≠ (j : ℕ) + 1 := by
        show (0 : ℕ) ≠ (j : ℕ) + 1
        omega
      rw [if_neg hne, zero_mul]
    -- rank-nullity for `proj 0`
    have hker_finrank :
        Module.finrank ℝ
          (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (n+1) => ℝ) 0).ker = n := by
      have hsurj : Function.Surjective
          (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (n+1) => ℝ) 0) := fun y =>
        ⟨fun i => if i = 0 then y else 0, by simp [LinearMap.proj_apply]⟩
      have hrange : LinearMap.range
          (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (n+1) => ℝ) 0) = ⊤ :=
        LinearMap.range_eq_top.mpr hsurj
      have hrank :=
        (LinearMap.proj (R := ℝ)
          (φ := fun _ : Fin (n+1) => ℝ) 0).finrank_range_add_finrank_ker
      rw [hrange] at hrank
      have : Module.finrank ℝ (Fin (n+1) → ℝ) = n + 1 := by
        rw [Module.finrank_pi]; simp
      rw [this] at hrank
      have h_top : Module.finrank ℝ
          (⊤ : Submodule ℝ ℝ) = 1 := by
        rw [finrank_top]; exact Module.finrank_self ℝ
      rw [h_top] at hrank
      omega
    calc (J n).rank
        = Module.finrank ℝ (LinearMap.range (J n).mulVecLin) := rfl
      _ ≤ Module.finrank ℝ
          (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (n+1) => ℝ) 0).ker :=
          Submodule.finrank_mono hsub
      _ = n := hker_finrank
  · -- rank ≥ n: standard basis vectors `e_{i.succ}` for `i : Fin n` are in range and
    -- linearly independent.
    have hin : ∀ i : Fin n,
        (Pi.single (i.succ : Fin (n+1)) (1 : ℝ) : Fin (n+1) → ℝ) ∈
          LinearMap.range (J n).mulVecLin := by
      intro i
      exact ⟨Pi.single (i.castSucc : Fin (n+1)) 1, J_mulVec_single_castSucc n i⟩
    let f : Fin n → LinearMap.range (J n).mulVecLin :=
      fun i => ⟨Pi.single (i.succ : Fin (n+1)) 1, hin i⟩
    have hli : LinearIndependent ℝ f := by
      apply LinearIndependent.of_comp
        (LinearMap.range (J n).mulVecLin).subtype
      -- Subtype.subtype ∘ f = i ↦ Pi.single i.succ 1.
      -- This is linearly independent because Pi.single is.
      have := (Pi.basisFun ℝ (Fin (n+1))).linearIndependent
      have hcomp : (LinearMap.range (J n).mulVecLin).subtype ∘ f =
          fun i : Fin n =>
            ((Pi.basisFun ℝ (Fin (n+1))) (i.succ : Fin (n+1))) := by
        funext i
        simp [f, Pi.basisFun_apply]
      rw [hcomp]
      exact this.comp _ (Fin.succ_injective _)
    have hcard : Fintype.card (Fin n) ≤ Module.finrank ℝ
        (LinearMap.range (J n).mulVecLin) := hli.fintype_card_le_finrank
    simp at hcard
    exact hcard

snip end

/-- The main problem: Statement (a) — `Y * X⁻¹` and `X⁻¹ * Y` have rank `n`
when `X` is nonsingular and `Y` is the column-shift of `X`. -/
problem imc1995_p1_rank (n : ℕ) (X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hX : IsUnit X.det) :
    (shiftColumns X * X⁻¹).rank = n ∧ (X⁻¹ * shiftColumns X).rank = n := by
  refine ⟨?_, ?_⟩
  · -- A = Y * X⁻¹ = X * J * X⁻¹
    rw [shiftColumns_eq_mul_J]
    have hXinv : IsUnit X⁻¹.det := by
      rw [Matrix.det_nonsing_inv]
      exact hX.ringInverse
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hXinv]
    rw [Matrix.rank_mul_eq_right_of_isUnit_det _ _ hX]
    exact J_rank n
  · -- B = X⁻¹ * X * J = J.
    rw [shiftColumns_eq_mul_J]
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hX, Matrix.one_mul]
    exact J_rank n

/-- The main problem: Statement (b) — every eigenvalue of `Y * X⁻¹` and
`X⁻¹ * Y` is zero. -/
problem imc1995_p1_eigenvalues (n : ℕ) (X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hX : IsUnit X.det) :
    (∀ (μ : ℝ) (v : Fin (n+1) → ℝ), v ≠ 0 →
        (shiftColumns X * X⁻¹) *ᵥ v = μ • v → μ = 0) ∧
    (∀ (μ : ℝ) (v : Fin (n+1) → ℝ), v ≠ 0 →
        (X⁻¹ * shiftColumns X) *ᵥ v = μ • v → μ = 0) := by
  -- General lemma: if `M` is nilpotent with `M^k = 0`, every eigenvalue of `M` is zero.
  have key : ∀ (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (k : ℕ),
      M ^ (k + 1) = 0 →
      ∀ (μ : ℝ) (v : Fin (n+1) → ℝ), v ≠ 0 → M *ᵥ v = μ • v → μ = 0 := by
    intro M k hM μ v hv hmul
    have hpow : ∀ p, (M ^ p) *ᵥ v = μ ^ p • v := by
      intro p
      induction p with
      | zero => simp
      | succ p ih =>
        rw [pow_succ]
        rw [show ((M ^ p * M) *ᵥ v) = M ^ p *ᵥ (M *ᵥ v) from
          (Matrix.mulVec_mulVec v (M^p) M).symm]
        rw [hmul, Matrix.mulVec_smul, ih, smul_smul, mul_comm, ← pow_succ]
    have h0 : (M ^ (k + 1)) *ᵥ v = 0 := by
      rw [hM, Matrix.zero_mulVec]
    rw [hpow] at h0
    have hμk : μ ^ (k + 1) = 0 := by
      by_contra hne
      apply hv
      rcases smul_eq_zero.mp h0 with h | h
      · exact absurd h hne
      · exact h
    exact pow_eq_zero_iff (Nat.succ_ne_zero k) |>.mp hμk
  refine ⟨?_, ?_⟩
  · intro μ v hv hmul
    rw [shiftColumns_eq_mul_J] at hmul
    -- A = X * J * X⁻¹ is nilpotent: A^{n+1} = X * J^{n+1} * X⁻¹ = 0.
    apply key (X * J n * X⁻¹) n _ μ v hv hmul
    -- Need: (X * J n * X⁻¹)^{n+1} = 0.
    -- Use induction: (X * J n * X⁻¹)^k = X * J n^k * X⁻¹.
    have hconj : ∀ k, (X * J n * X⁻¹) ^ k = X * (J n) ^ k * X⁻¹ := by
      intro k
      induction k with
      | zero =>
        simp only [pow_zero]
        rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ hX]
      | succ k ih =>
        rw [pow_succ, ih, pow_succ]
        -- Goal: X * J^k * X⁻¹ * (X * J n * X⁻¹) = X * (J^k * J n) * X⁻¹
        rw [show X * (J n)^k * X⁻¹ * (X * J n * X⁻¹)
              = X * (J n)^k * (X⁻¹ * X) * J n * X⁻¹ by
          simp only [Matrix.mul_assoc]]
        rw [Matrix.nonsing_inv_mul _ hX, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    rw [hconj, J_pow_succ_eq_zero]
    simp
  · intro μ v hv hmul
    rw [shiftColumns_eq_mul_J] at hmul
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hX, Matrix.one_mul] at hmul
    exact key (J n) n (J_pow_succ_eq_zero n) μ v hv hmul

end Imc1995P1
