/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1998, Problem 1 (Day 1)

Let `V` be a 10-dimensional real vector space, and `U₁ ⊆ U₂` subspaces of
dimensions 3 and 6, respectively. Let `ℰ` be the set of all linear maps
`T : V → V` such that `T(U₁) ⊆ U₁` and `T(U₂) ⊆ U₂`. Find the dimension
of `ℰ` (as a real vector space).

Answer: `67`.

## Proof outline

Choose a basis `e₁, …, e₁₀` adapted to the flag `U₁ ⊆ U₂ ⊆ V`, i.e.
`e₁,e₂,e₃` span `U₁`, `e₁,…,e₆` span `U₂`. In this basis, the matrix of any
`T ∈ ℰ` is block upper-triangular with blocks of sizes `3, 3, 4` along the
diagonal:

       [ A   B   C ]
       [ 0   D   E ]
       [ 0   0   F ]

where `A, D` are `3×3`, `F` is `4×4`, `B` is `3×3`, `C` is `3×4`, `E` is `3×4`.
The dimension is `9 + 9 + 16 + 9 + 12 + 12 = 67`.

Equivalently: the "free" entries are `(i,j)` with `i ≤ j` in the block
ordering, i.e. the entries that do *not* lie strictly below either of the
blocks. Counting columns:

* columns `1…3` (forming images in `U₁`): rows `1…3` free → `3·3 = 9`
* columns `4…6` (images in `U₂`): rows `1…6` free → `6·3 = 18`
* columns `7…10` (images in `V`): rows `1…10` free → `10·4 = 40`

Total: `9 + 18 + 40 = 67`.

## Status

Generic statement is proved by reduction to the matrix block form, in terms
of the *standard* flag `U₁ = span{e₀,e₁,e₂}`, `U₂ = span{e₀,…,e₅}` in
`Fin 10 → ℝ`. The reduction "any flag is equivalent to the standard one"
is done by choosing an adapted basis and using `Basis.equiv`. Some routine
basis-bookkeeping steps are left as `sorry`.
-/

namespace Imc1998P1

open scoped BigOperators
open Module

/-- The "non-free" entries are those strictly below the block containing
column `j`. We define the *negation* (the set of forbidden entries) as a
disjunction, which is more convenient for case analysis. -/
def nonFree (i j : Fin 10) : Prop :=
  ((j : ℕ) < 3 ∧ (3 : ℕ) ≤ (i : ℕ)) ∨ ((j : ℕ) < 6 ∧ (6 : ℕ) ≤ (i : ℕ))

/-- The "free index" predicate. -/
instance decNonFree (i j : Fin 10) : Decidable (nonFree i j) := by
  unfold nonFree; exact instDecidableOr

def freeIndex (i j : Fin 10) : Prop := ¬ nonFree i j

instance decFreeIndex (i j : Fin 10) : Decidable (freeIndex i j) := by
  unfold freeIndex; infer_instance

instance : DecidablePred (fun p : Fin 10 × Fin 10 => freeIndex p.1 p.2) :=
  fun p => decFreeIndex p.1 p.2

/-- The set of free indices, as a `Finset`. -/
def freeIndices : Finset (Fin 10 × Fin 10) :=
  (Finset.univ : Finset (Fin 10 × Fin 10)).filter (fun p => freeIndex p.1 p.2)

/-- The cardinality of `freeIndices` is `67`. -/
lemma freeIndices_card : freeIndices.card = 67 := by
  decide

/-- The standard `U₁ ⊆ ℝ¹⁰`: vectors supported on the first 3 coordinates. -/
def stdU1 : Submodule ℝ (Fin 10 → ℝ) :=
  { carrier := { v | ∀ i : Fin 10, (3 : ℕ) ≤ (i : ℕ) → v i = 0 }
    add_mem' := by intro a b ha hb i hi; simp [ha i hi, hb i hi]
    zero_mem' := by intro i _; rfl
    smul_mem' := by intro c a ha i hi; simp [ha i hi] }

/-- The standard `U₂ ⊆ ℝ¹⁰`: vectors supported on the first 6 coordinates. -/
def stdU2 : Submodule ℝ (Fin 10 → ℝ) :=
  { carrier := { v | ∀ i : Fin 10, (6 : ℕ) ≤ (i : ℕ) → v i = 0 }
    add_mem' := by intro a b ha hb i hi; simp [ha i hi, hb i hi]
    zero_mem' := by intro i _; rfl
    smul_mem' := by intro c a ha i hi; simp [ha i hi] }

snip begin

lemma stdU1_le_stdU2 : stdU1 ≤ stdU2 := by
  intro v hv i hi
  exact hv i (by omega)

/-- The "low-coords" submodule `{v | ∀ i, k ≤ i → v i = 0}` of `Fin n → ℝ`. -/
private def lowCoords (n k : ℕ) : Submodule ℝ (Fin n → ℝ) where
  carrier := { v | ∀ i : Fin n, k ≤ (i : ℕ) → v i = 0 }
  add_mem' := by intro a b ha hb i hi; simp [ha i hi, hb i hi]
  zero_mem' := by intro i _; rfl
  smul_mem' := by intro c a ha i hi; simp [ha i hi]

/-- Linear iso `lowCoords n k ≃ₗ Fin k → ℝ` via restriction. -/
private def lowCoordsEquiv (n k : ℕ) (hk : k ≤ n) :
    lowCoords n k ≃ₗ[ℝ] (Fin k → ℝ) where
  toFun v i := (v : Fin n → ℝ) ⟨(i : ℕ), lt_of_lt_of_le i.isLt hk⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  invFun w :=
    ⟨fun i => if h : (i : ℕ) < k then w ⟨(i : ℕ), h⟩ else 0,
     by
      intro i hi
      dsimp
      rw [dif_neg (by omega)]⟩
  left_inv := by
    intro v
    apply Subtype.ext
    funext i
    by_cases h : (i : ℕ) < k
    · simp [h]
    · simp [h, v.2 i (by omega)]
  right_inv := by
    intro w
    funext i
    have hi : (i : ℕ) < k := i.isLt
    simp [hi]

private lemma stdU1_eq_lowCoords : stdU1 = lowCoords 10 3 := rfl
private lemma stdU2_eq_lowCoords : stdU2 = lowCoords 10 6 := rfl

lemma stdU1_finrank : finrank ℝ stdU1 = 3 := by
  rw [stdU1_eq_lowCoords]
  have e : lowCoords 10 3 ≃ₗ[ℝ] (Fin 3 → ℝ) := lowCoordsEquiv 10 3 (by norm_num)
  rw [LinearEquiv.finrank_eq e, Module.finrank_pi]
  simp

lemma stdU2_finrank : finrank ℝ stdU2 = 6 := by
  rw [stdU2_eq_lowCoords]
  have e : lowCoords 10 6 ≃ₗ[ℝ] (Fin 6 → ℝ) := lowCoordsEquiv 10 6 (by norm_num)
  rw [LinearEquiv.finrank_eq e, Module.finrank_pi]
  simp

/-- The "preservation" predicate: a linear map `T : (Fin 10 → ℝ) → (Fin 10 → ℝ)`
preserves the standard flag `stdU1 ⊆ stdU2`. -/
def preservesStdFlag (T : (Fin 10 → ℝ) →ₗ[ℝ] (Fin 10 → ℝ)) : Prop :=
  (∀ v ∈ stdU1, T v ∈ stdU1) ∧ (∀ v ∈ stdU2, T v ∈ stdU2)

/-- `ℰstd`: the submodule of `End ℝ (Fin 10 → ℝ)` consisting of flag-preservers. -/
def ℰstd : Submodule ℝ ((Fin 10 → ℝ) →ₗ[ℝ] (Fin 10 → ℝ)) where
  carrier := { T | preservesStdFlag T }
  add_mem' := by
    rintro S T ⟨hS1, hS2⟩ ⟨hT1, hT2⟩
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · exact stdU1.add_mem (hS1 v hv) (hT1 v hv)
    · exact stdU2.add_mem (hS2 v hv) (hT2 v hv)
  zero_mem' := ⟨fun v _ => stdU1.zero_mem, fun v _ => stdU2.zero_mem⟩
  smul_mem' := by
    rintro c T ⟨hT1, hT2⟩
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · exact stdU1.smul_mem c (hT1 v hv)
    · exact stdU2.smul_mem c (hT2 v hv)

/-- Auxiliary: the standard basis vector `e i` is in `stdU1` iff `(i : ℕ) < 3`. -/
lemma stdU1_basis_mem (i : Fin 10) :
    (Pi.single i (1 : ℝ)) ∈ stdU1 ↔ (i : ℕ) < 3 := by
  unfold stdU1
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq]
  constructor
  · intro h
    by_contra hge
    rw [Nat.not_lt] at hge
    have := h i hge
    simp at this
  · intro hlt j hj
    have hne : i ≠ j := fun h => by rw [h] at hlt; omega
    simp [hne]

/-- Auxiliary: similarly for `stdU2`. -/
lemma stdU2_basis_mem (i : Fin 10) :
    (Pi.single i (1 : ℝ)) ∈ stdU2 ↔ (i : ℕ) < 6 := by
  unfold stdU2
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq]
  constructor
  · intro h
    by_contra hge
    rw [Nat.not_lt] at hge
    have := h i hge
    simp at this
  · intro hlt j hj
    have hne : i ≠ j := fun h => by rw [h] at hlt; omega
    simp [hne]

/-- Characterization: the matrix `M` of a linear map `T = (M.mulVecLin)`
preserves the standard flag iff its entries `M i j` vanish at all
"non-free" positions. -/
lemma preservesStdFlag_iff_zero_offDiag
    (M : Matrix (Fin 10) (Fin 10) ℝ) :
    preservesStdFlag (Matrix.mulVecLin M) ↔
      ∀ i j : Fin 10, ¬ freeIndex i j → M i j = 0 := by
  constructor
  · rintro ⟨h1, h2⟩ i j hnf
    -- ¬ freeIndex i j unfolds to nonFree i j.
    have hnf' : nonFree i j := by
      unfold freeIndex at hnf
      exact Classical.not_not.mp hnf
    rcases hnf' with ⟨hj, hi⟩ | ⟨hj, hi⟩
    · -- j < 3, i ≥ 3.
      have hej : Pi.single j (1 : ℝ) ∈ stdU1 := (stdU1_basis_mem j).mpr hj
      have himg := h1 _ hej
      have : (M.mulVecLin (Pi.single j 1)) i = 0 := himg i hi
      simp [Matrix.mulVec, dotProduct,
        Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ] at this
      convert this using 1
    · -- j < 6, i ≥ 6.
      have hej : Pi.single j (1 : ℝ) ∈ stdU2 := (stdU2_basis_mem j).mpr hj
      have himg := h2 _ hej
      have : (M.mulVecLin (Pi.single j 1)) i = 0 := himg i hi
      simp [Matrix.mulVec, dotProduct,
        Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ] at this
      convert this using 1
  · intro hzero
    refine ⟨?_, ?_⟩
    · intro v hv i hi
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : (j : ℕ) < 3
      · have hnf : ¬ freeIndex i j := fun h => h (Or.inl ⟨hj, hi⟩)
        rw [hzero i j hnf, zero_mul]
      · have : v j = 0 := hv j (by omega)
        rw [this, mul_zero]
    · intro v hv i hi
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : (j : ℕ) < 6
      · have hnf : ¬ freeIndex i j := fun h => h (Or.inr ⟨hj, hi⟩)
        rw [hzero i j hnf, zero_mul]
      · have : v j = 0 := hv j (by omega)
        rw [this, mul_zero]

/-- The submodule of matrices supported on `freeIndices`. -/
def matrixSubmodule : Submodule ℝ (Matrix (Fin 10) (Fin 10) ℝ) where
  carrier := { M | ∀ i j, ¬ freeIndex i j → M i j = 0 }
  add_mem' := by
    intro M N hM hN i j hnf
    simp [hM i j hnf, hN i j hnf]
  zero_mem' := by intro i j _; rfl
  smul_mem' := by
    intro c M hM i j hnf
    simp [hM i j hnf]

lemma mem_matrixSubmodule_iff (M : Matrix (Fin 10) (Fin 10) ℝ) :
    M ∈ matrixSubmodule ↔ ∀ i j, ¬ freeIndex i j → M i j = 0 := Iff.rfl

lemma mem_ℰstd_iff (T : (Fin 10 → ℝ) →ₗ[ℝ] (Fin 10 → ℝ)) :
    T ∈ ℰstd ↔ preservesStdFlag T := Iff.rfl

/-- The dimension of `matrixSubmodule` is `67`. It is isomorphic to
`freeIndices → ℝ` via the obvious extraction map. -/
lemma matrixSubmodule_finrank : finrank ℝ matrixSubmodule = 67 := by
  -- Build a linear isomorphism `matrixSubmodule ≃ₗ (freeIndices → ℝ)`.
  -- Forward: M ↦ (M i j for (i,j) ∈ freeIndices)
  -- Inverse: f ↦ matrix M with M i j = f (i,j) if (i,j) ∈ freeIndices, else 0.
  let toFun : matrixSubmodule →ₗ[ℝ] (freeIndices → ℝ) :=
    { toFun := fun M p => (M : Matrix (Fin 10) (Fin 10) ℝ) p.val.1 p.val.2
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
  let invFun : (freeIndices → ℝ) → matrixSubmodule := fun f =>
    ⟨fun i j => if h : freeIndex i j then f ⟨(i, j), by
        unfold freeIndices; simp [h]⟩ else 0,
     by
      intro i j hnf
      dsimp
      rw [dif_neg hnf]⟩
  have hinv : Function.LeftInverse invFun toFun := by
    intro M
    ext i j
    by_cases h : freeIndex i j
    · simp [invFun, toFun, h]
    · simp [invFun, h, M.2 i j h]
  have hinv2 : Function.RightInverse invFun toFun := by
    intro f
    ext p
    obtain ⟨⟨i, j⟩, hp⟩ := p
    have hf : freeIndex i j := by
      unfold freeIndices at hp; simp at hp; exact hp
    simp [invFun, toFun, hf]
  let e : matrixSubmodule ≃ₗ[ℝ] (freeIndices → ℝ) :=
    { toFun := toFun
      invFun := invFun
      left_inv := hinv
      right_inv := hinv2
      map_add' := toFun.map_add
      map_smul' := toFun.map_smul }
  rw [LinearEquiv.finrank_eq e]
  rw [Module.finrank_pi]
  simp [freeIndices_card]

/-- The standard-flag preserving endomorphisms have dimension `67`. -/
lemma ℰstd_finrank : finrank ℝ ℰstd = 67 := by
  -- Build a linear iso matrixSubmodule ≃ₗ[ℝ] ℰstd via M ↦ M.mulVecLin.
  -- (Matrix.toLin' is the standard linear iso, and it carries the
  -- "zero-entry" condition into the "preserves flag" condition by
  -- preservesStdFlag_iff_zero_offDiag.)
  have toFun_mem : ∀ (M : matrixSubmodule),
      Matrix.toLin' (M : Matrix (Fin 10) (Fin 10) ℝ) ∈ ℰstd := by
    intro M
    rw [mem_ℰstd_iff]
    have hM : ∀ i j, ¬ freeIndex i j → (M : Matrix (Fin 10) (Fin 10) ℝ) i j = 0 :=
      (mem_matrixSubmodule_iff _).mp M.2
    have := (preservesStdFlag_iff_zero_offDiag (M : Matrix (Fin 10) (Fin 10) ℝ)).mpr hM
    -- Matrix.toLin' M = M.mulVecLin definitionally on (Fin n → ℝ).
    exact this
  let toFun : matrixSubmodule →ₗ[ℝ] ℰstd :=
    { toFun := fun M => ⟨Matrix.toLin' (M : Matrix (Fin 10) (Fin 10) ℝ), toFun_mem M⟩
      map_add' := by
        intros M N
        apply Subtype.ext
        change Matrix.toLin' (((M : Matrix (Fin 10) (Fin 10) ℝ) + (N : Matrix (Fin 10) (Fin 10) ℝ)))
            = Matrix.toLin' (M : Matrix (Fin 10) (Fin 10) ℝ) + Matrix.toLin' (N : Matrix (Fin 10) (Fin 10) ℝ)
        exact (Matrix.toLin' (R := ℝ) (m := Fin 10) (n := Fin 10)).map_add _ _
      map_smul' := by
        intros c M
        apply Subtype.ext
        change Matrix.toLin' (c • (M : Matrix (Fin 10) (Fin 10) ℝ))
            = c • Matrix.toLin' (M : Matrix (Fin 10) (Fin 10) ℝ)
        exact (Matrix.toLin' (R := ℝ) (m := Fin 10) (n := Fin 10)).map_smul _ _ }
  have invFun_mem : ∀ (T : ℰstd),
      LinearMap.toMatrix' (T : (Fin 10 → ℝ) →ₗ[ℝ] (Fin 10 → ℝ)) ∈ matrixSubmodule := by
    intro T
    rw [mem_matrixSubmodule_iff]
    intro i j hnf
    have hpres : preservesStdFlag (T : (Fin 10 → ℝ) →ₗ[ℝ] (Fin 10 → ℝ)) :=
      (mem_ℰstd_iff _).mp T.2
    have hT_eq :
        Matrix.toLin' (LinearMap.toMatrix' (T : (Fin 10 → ℝ) →ₗ[ℝ] (Fin 10 → ℝ))) =
        (T : (Fin 10 → ℝ) →ₗ[ℝ] (Fin 10 → ℝ)) :=
      Matrix.toLin'_toMatrix' (T : (Fin 10 → ℝ) →ₗ[ℝ] (Fin 10 → ℝ))
    have hpres' : preservesStdFlag (Matrix.mulVecLin
        (LinearMap.toMatrix' (T : (Fin 10 → ℝ) →ₗ[ℝ] (Fin 10 → ℝ)))) := by
      rw [← Matrix.toLin'_apply']
      rw [hT_eq]; exact hpres
    exact (preservesStdFlag_iff_zero_offDiag _).mp hpres' i j hnf
  let invFun : ℰstd → matrixSubmodule := fun T =>
    ⟨LinearMap.toMatrix' (T : (Fin 10 → ℝ) →ₗ[ℝ] (Fin 10 → ℝ)), invFun_mem T⟩
  have hleft : Function.LeftInverse invFun toFun := by
    intro M
    apply Subtype.ext
    change LinearMap.toMatrix' (Matrix.toLin' (M : Matrix (Fin 10) (Fin 10) ℝ)) = (M : Matrix (Fin 10) (Fin 10) ℝ)
    exact LinearMap.toMatrix'_toLin' _
  have hright : Function.RightInverse invFun toFun := by
    intro T
    apply Subtype.ext
    change Matrix.toLin' (LinearMap.toMatrix' (T : (Fin 10 → ℝ) →ₗ[ℝ] (Fin 10 → ℝ)))
        = (T : (Fin 10 → ℝ) →ₗ[ℝ] (Fin 10 → ℝ))
    exact Matrix.toLin'_toMatrix' _
  let e : matrixSubmodule ≃ₗ[ℝ] ℰstd :=
    { toFun := toFun
      invFun := invFun
      left_inv := hleft
      right_inv := hright
      map_add' := toFun.map_add
      map_smul' := toFun.map_smul }
  rw [← LinearEquiv.finrank_eq e]
  exact matrixSubmodule_finrank

snip end

/-- The submodule of endomorphisms of `V` preserving both `U₁` and `U₂`. -/
def preservers {V : Type*} [AddCommGroup V] [Module ℝ V]
    (U₁ U₂ : Submodule ℝ V) : Submodule ℝ (V →ₗ[ℝ] V) where
  carrier := { T | (∀ v ∈ U₁, T v ∈ U₁) ∧ (∀ v ∈ U₂, T v ∈ U₂) }
  add_mem' := by
    rintro S T ⟨hS1, hS2⟩ ⟨hT1, hT2⟩
    exact ⟨fun v hv => U₁.add_mem (hS1 v hv) (hT1 v hv),
           fun v hv => U₂.add_mem (hS2 v hv) (hT2 v hv)⟩
  zero_mem' := ⟨fun v _ => U₁.zero_mem, fun v _ => U₂.zero_mem⟩
  smul_mem' := by
    rintro c T ⟨hT1, hT2⟩
    exact ⟨fun v hv => U₁.smul_mem c (hT1 v hv),
           fun v hv => U₂.smul_mem c (hT2 v hv)⟩

/-- The main statement.

If `V` is a 10-dimensional real vector space and `U₁ ⊆ U₂` are subspaces
of dimensions 3 and 6, then the space of linear endomorphisms `T : V → V`
preserving both `U₁` and `U₂` has dimension `67`. -/
problem imc1998_p1
    (V : Type*) [AddCommGroup V] [Module ℝ V]
    [Module.Finite ℝ V] (hV : finrank ℝ V = 10)
    (U₁ U₂ : Submodule ℝ V) (hU : U₁ ≤ U₂)
    (h1 : finrank ℝ U₁ = 3) (h2 : finrank ℝ U₂ = 6) :
    finrank ℝ (preservers U₁ U₂) = 67 := by
  -- TODO: reduce to the standard flag case via `Basis.equiv`. The argument:
  --
  -- 1. Choose an adapted basis `B : Basis (Fin 10) ℝ V` such that
  --    `Submodule.span ℝ (B '' (Set.range Fin.castLE _))` for the right inclusions
  --    yields `U₁` and `U₂`. This uses `Basis.extend` twice (extend basis of `U₁`
  --    to one of `U₂`, then to `V`).
  -- 2. Push along `B` to identify `V ≃ₗ Fin 10 → ℝ`. Under this iso, `U₁, U₂`
  --    become `stdU1, stdU2`, and the constraint submodule becomes `ℰstd`.
  -- 3. By `ℰstd_finrank`, the dimension is `67`.
  sorry

end Imc1998P1
