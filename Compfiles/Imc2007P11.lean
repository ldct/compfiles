/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2007, Problem 11
(IMC 2007, Day 2, Problem 5)

Find the smallest positive integer `n_k` such that there exist real `n_k × n_k`
matrices `A_1, …, A_k` with
* `A_i^2 = 0` for all `i`,
* `A_i * A_j = A_j * A_i` for all `i, j`, and
* `A_1 * A_2 * ⋯ * A_k ≠ 0`.

Answer: `n_k = 2^k`.
-/

namespace Imc2007P11

open Matrix Finset

/-- The set of positive integers `n` such that there exist `n × n` real matrices
`A_1, …, A_k` with `A_i^2 = 0`, pairwise commuting, and with nonzero product. -/
def goodN (k : ℕ) : Set ℕ :=
  { n | 0 < n ∧ ∃ A : Fin k → Matrix (Fin n) (Fin n) ℝ,
        (∀ i, A i * A i = 0) ∧
        (∀ i j, A i * A j = A j * A i) ∧
        (List.ofFn A).prod ≠ 0 }

snip begin

/-! ### Construction: `2^k` works.

Index basis vectors by `Finset (Fin k)`. Define `A_i` by `A_i e_S = e_{S ∪ {i}}`
if `i ∉ S`, else `0`. Then `A_i^2 = 0`, `A_i A_j = A_j A_i`, and
`A_1 ⋯ A_k e_∅ = e_{Fin k}`, which is nonzero.
-/

/-- The "subset add" matrix on `Finset (Fin k) × Finset (Fin k)`: sends `e_S` to
`e_{S ∪ {i}}` if `i ∉ S`, else to `0`. -/
noncomputable def subsetAddMat (k : ℕ) (i : Fin k) :
    Matrix (Finset (Fin k)) (Finset (Fin k)) ℝ :=
  fun T S => if i ∉ S ∧ T = insert i S then (1 : ℝ) else 0

/-- `(subsetAddMat k i)^2 = 0`. -/
lemma subsetAddMat_sq (k : ℕ) (i : Fin k) :
    subsetAddMat k i * subsetAddMat k i = 0 := by
  ext U S
  simp only [Matrix.mul_apply, subsetAddMat, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro T _
  by_cases h1 : i ∉ S ∧ T = insert i S
  · rw [if_pos h1]
    have hT := h1.2
    have hiT : i ∈ T := by rw [hT]; exact mem_insert_self _ _
    have hcond : ¬ (i ∉ T ∧ U = insert i T) := fun ⟨h, _⟩ => h hiT
    rw [if_neg hcond]; ring
  · rw [if_neg h1]; ring

/-- The two matrices commute. -/
lemma subsetAddMat_comm (k : ℕ) (i j : Fin k) :
    subsetAddMat k i * subsetAddMat k j = subsetAddMat k j * subsetAddMat k i := by
  ext U S
  simp only [Matrix.mul_apply, subsetAddMat]
  by_cases hij : i = j
  · subst hij; rfl
  -- Helper: each summand reduces to a form we can analyze.
  have hLHS : ∑ T, (if i ∉ T ∧ U = insert i T then (1 : ℝ) else 0) *
                    (if j ∉ S ∧ T = insert j S then 1 else 0) =
              if i ∉ S ∧ j ∉ S ∧ U = insert i (insert j S) then (1 : ℝ) else 0 := by
    by_cases hjS : j ∈ S
    · -- Then second factor is always 0.
      have hRHS_zero : ¬ (i ∉ S ∧ j ∉ S ∧ U = insert i (insert j S)) := by
        rintro ⟨_, hj, _⟩; exact hj hjS
      rw [if_neg hRHS_zero]
      apply Finset.sum_eq_zero
      intro T _
      have : ¬ (j ∉ S ∧ T = insert j S) := fun ⟨h, _⟩ => h hjS
      rw [if_neg this]; ring
    · -- j ∉ S. Sum is concentrated at T = insert j S.
      rw [Finset.sum_eq_single (insert j S)]
      · -- Term at T = insert j S.
        have hcond2 : (j ∉ S ∧ insert j S = insert j S) := ⟨hjS, rfl⟩
        rw [if_pos hcond2, mul_one]
        have h_iff : (i ∉ insert j S) ↔ (i ∉ S) := by
          simp only [mem_insert, not_or]
          exact ⟨fun h => h.2, fun h => ⟨hij, h⟩⟩
        by_cases hIf : i ∉ insert j S ∧ U = insert i (insert j S)
        · rw [if_pos hIf, if_pos]
          exact ⟨h_iff.mp hIf.1, hjS, hIf.2⟩
        · rw [if_neg hIf, if_neg]
          rintro ⟨hiS, _, hU⟩
          exact hIf ⟨h_iff.mpr hiS, hU⟩
      · intro T _ hT
        have hne : ¬ (j ∉ S ∧ T = insert j S) := by
          rintro ⟨_, hT'⟩; exact hT hT'
        rw [if_neg hne]; ring
      · intro h; exact (h (mem_univ _)).elim
  have hRHS : ∑ T, (if j ∉ T ∧ U = insert j T then (1 : ℝ) else 0) *
                    (if i ∉ S ∧ T = insert i S then 1 else 0) =
              if j ∉ S ∧ i ∉ S ∧ U = insert j (insert i S) then (1 : ℝ) else 0 := by
    by_cases hiS : i ∈ S
    · have hRHS_zero : ¬ (j ∉ S ∧ i ∉ S ∧ U = insert j (insert i S)) := by
        rintro ⟨_, hi, _⟩; exact hi hiS
      rw [if_neg hRHS_zero]
      apply Finset.sum_eq_zero
      intro T _
      have : ¬ (i ∉ S ∧ T = insert i S) := fun ⟨h, _⟩ => h hiS
      rw [if_neg this]; ring
    · rw [Finset.sum_eq_single (insert i S)]
      · have hcond2 : (i ∉ S ∧ insert i S = insert i S) := ⟨hiS, rfl⟩
        rw [if_pos hcond2, mul_one]
        have h_iff : (j ∉ insert i S) ↔ (j ∉ S) := by
          simp only [mem_insert, not_or]
          exact ⟨fun h => h.2, fun h => ⟨Ne.symm hij, h⟩⟩
        by_cases hIf : j ∉ insert i S ∧ U = insert j (insert i S)
        · rw [if_pos hIf, if_pos]
          exact ⟨h_iff.mp hIf.1, hiS, hIf.2⟩
        · rw [if_neg hIf, if_neg]
          rintro ⟨hjS, _, hU⟩
          exact hIf ⟨h_iff.mpr hjS, hU⟩
      · intro T _ hT
        have hne : ¬ (i ∉ S ∧ T = insert i S) := by
          rintro ⟨_, hT'⟩; exact hT hT'
        rw [if_neg hne]; ring
      · intro h; exact (h (mem_univ _)).elim
  rw [hLHS, hRHS]
  have hcomm : insert i (insert j S) = insert j (insert i S) := Finset.insert_comm i j S
  congr 1
  apply propext
  constructor
  · rintro ⟨hi, hj, hU⟩; exact ⟨hj, hi, hcomm ▸ hU⟩
  · rintro ⟨hj, hi, hU⟩; exact ⟨hi, hj, hcomm.symm ▸ hU⟩

/-- The product `A_1 * A_2 * ⋯ * A_k` of `subsetAddMat`s, evaluated at the
matrix entry `(univ, ∅)`, is `1`. -/
lemma list_prod_subsetAddMat_univ_empty (k : ℕ) :
    (List.ofFn (subsetAddMat k)).prod (Finset.univ) ∅ = 1 := by
  -- Generalize over a list of matrices A_{i_1}, ..., A_{i_m} where the i's are
  -- distinct, and the corresponding subset is the set of these indices.
  -- We prove: for any list `L : List (Fin k)` with distinct entries, and any
  -- subset `T = L.toFinset`, we have `(L.map (subsetAddMat k)).prod T ∅ = 1`.
  -- Then specialize to L = (List.finRange k), giving T = univ.
  suffices h : ∀ (L : List (Fin k)), L.Nodup →
      (L.map (subsetAddMat k)).prod L.toFinset ∅ = 1 by
    have := h (List.finRange k) (List.nodup_finRange k)
    rw [List.ofFn_eq_map]
    have htf : (List.finRange k).toFinset = (Finset.univ : Finset (Fin k)) := by
      ext x; simp
    rw [htf] at this
    exact this
  intro L hL
  induction L with
  | nil =>
    simp [List.toFinset]
  | cons i L ih =>
    have hi_notin : i ∉ L := List.Nodup.notMem hL
    have hL_nodup : L.Nodup := hL.of_cons
    have ih' := ih hL_nodup
    have h_toFinset : (i :: L).toFinset = insert i L.toFinset := by
      simp [List.toFinset_cons]
    rw [h_toFinset]
    -- (i :: L).map (subsetAddMat k) = subsetAddMat k i :: L.map (subsetAddMat k)
    rw [List.map_cons, List.prod_cons]
    -- The product is (subsetAddMat k i) * (L.map (subsetAddMat k)).prod
    -- evaluated at (insert i L.toFinset, ∅).
    -- Matrix multiplication: sum over T of (subsetAddMat k i) (insert i L.toFinset) T *
    --                                       (L.map ...).prod T ∅.
    -- (subsetAddMat k i) (insert i L.toFinset) T = 1 iff i ∉ T ∧ insert i L.toFinset = insert i T.
    -- Choose T = L.toFinset; then i ∉ T (since i ∉ L), and insert i L.toFinset = insert i T trivially.
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single L.toFinset]
    · have h_iL : i ∉ L.toFinset := by simp [hi_notin]
      have : (subsetAddMat k i) (insert i L.toFinset) L.toFinset = 1 := by
        simp [subsetAddMat, h_iL]
      rw [this, one_mul, ih']
    · intro T _ hT
      simp only [subsetAddMat]
      by_cases h : i ∉ T ∧ insert i L.toFinset = insert i T
      · -- We need T = L.toFinset, which means h.2 implies T = L.toFinset.
        have h_iL : i ∉ L.toFinset := by simp [hi_notin]
        have hTeq : T = L.toFinset := by
          have h1 := congrArg (fun s => Finset.erase s i) h.2
          simp only at h1
          rw [Finset.erase_insert h_iL, Finset.erase_insert h.1] at h1
          exact h1.symm
        exact absurd hTeq hT
      · rw [if_neg h, zero_mul]
    · intro h; exact (h (mem_univ _)).elim

lemma list_prod_subsetAddMat_ne_zero (k : ℕ) :
    (List.ofFn (subsetAddMat k)).prod ≠ 0 := by
  intro h
  have h1 := list_prod_subsetAddMat_univ_empty k
  rw [h] at h1
  simp at h1

snip end

/-- The answer: the minimum `n` is `2^k`. -/
determine answer (k : ℕ) : ℕ := 2 ^ k

problem imc2007_p11 (k : ℕ) (hk : 0 < k) :
    IsLeast (goodN k) (answer k) := by
  refine ⟨?_, ?_⟩
  · -- `2^k ∈ goodN k`: provided by the construction.
    refine ⟨Nat.pos_of_ne_zero (fun h => ?_), ?_⟩
    · exact absurd (Nat.pow_eq_zero.mp h).1 (by norm_num)
    have hcard : Fintype.card (Finset (Fin k)) = 2 ^ k := by
      rw [Fintype.card_finset]; simp
    set e : Finset (Fin k) ≃ Fin (2 ^ k) := (Fintype.equivFinOfCardEq hcard) with he_def
    refine ⟨fun i => Matrix.reindex e e (subsetAddMat k i), ?_, ?_, ?_⟩
    · -- A_i^2 = 0
      intro i
      change (subsetAddMat k i).submatrix e.symm e.symm *
             (subsetAddMat k i).submatrix e.symm e.symm = 0
      rw [(Matrix.submatrix_mul_equiv (subsetAddMat k i) (subsetAddMat k i)
            e.symm e.symm e.symm)]
      rw [subsetAddMat_sq]
      ext; simp
    · -- commute
      intro i j
      change (subsetAddMat k i).submatrix e.symm e.symm *
             (subsetAddMat k j).submatrix e.symm e.symm =
             (subsetAddMat k j).submatrix e.symm e.symm *
             (subsetAddMat k i).submatrix e.symm e.symm
      rw [Matrix.submatrix_mul_equiv (subsetAddMat k i) (subsetAddMat k j)
            e.symm e.symm e.symm]
      rw [Matrix.submatrix_mul_equiv (subsetAddMat k j) (subsetAddMat k i)
            e.symm e.symm e.symm]
      rw [subsetAddMat_comm]
    · -- product is nonzero
      have hP : (List.ofFn (fun i => Matrix.reindex e e (subsetAddMat k i))).prod =
                Matrix.reindex e e (List.ofFn (subsetAddMat k)).prod := by
        rw [List.ofFn_eq_map, List.ofFn_eq_map]
        induction (List.finRange k) with
        | nil =>
          simp only [List.map_nil, List.prod_nil]
          ext a b
          simp [Matrix.reindex, Matrix.submatrix, Matrix.one_apply, e.symm.injective.eq_iff]
        | cons i L ih =>
          simp only [List.map_cons, List.prod_cons]
          rw [ih]
          show (subsetAddMat k i).submatrix e.symm e.symm *
                 (List.map (subsetAddMat k) L).prod.submatrix e.symm e.symm =
                 ((subsetAddMat k i) * (List.map (subsetAddMat k) L).prod).submatrix
                    e.symm e.symm
          rw [Matrix.submatrix_mul_equiv]
      rw [hP]
      intro hcontra
      apply list_prod_subsetAddMat_ne_zero k
      -- Reindex of zero is zero, so we can pull back.
      ext S T
      have h1 : Matrix.reindex e e (List.ofFn (subsetAddMat k)).prod (e S) (e T) = 0 := by
        rw [hcontra]; rfl
      simpa [Matrix.reindex, Matrix.submatrix] using h1
  · -- lower bound: every n in goodN is ≥ 2^k.
    -- TODO: full formalization of the linear-independence argument.
    sorry

end Imc2007P11
