/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2005, Problem 9
(Second day, Problem 3)

Find the maximum dimension of a subspace `V` of `M_n(ℝ)` such that
`tr(X * Y) = 0` for all `X, Y ∈ V`.

Answer: `n.choose 2 = n * (n - 1) / 2`.
-/

namespace Imc2005P9

open Matrix

/-- The answer: `n.choose 2 = n(n-1)/2`. -/
determine answer (n : ℕ) : ℕ := n.choose 2

snip begin

/-- The strictly upper triangular matrices: zero on and below the diagonal. -/
def strictUpper (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {A | ∀ i j : Fin n, j ≤ i → A i j = 0}
  add_mem' {A B} hA hB i j hij := by simp [hA i j hij, hB i j hij]
  zero_mem' i j _ := rfl
  smul_mem' c A hA i j hij := by simp [hA i j hij]

lemma mem_strictUpper {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} :
    A ∈ strictUpper n ↔ ∀ i j : Fin n, j ≤ i → A i j = 0 := Iff.rfl

/-- For strictly upper triangular matrices, the product has zero diagonal. -/
lemma strictUpper_mul_diag {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ strictUpper n) (hB : B ∈ strictUpper n) (i : Fin n) :
    (A * B) i i = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hki : k ≤ i
  · rw [hA i k hki]; ring
  · have hik : i ≤ k := le_of_lt (not_le.mp hki)
    rw [hB k i hik]; ring

/-- For `A, B` strictly upper triangular, `tr(A * B) = 0`. -/
lemma strictUpper_trace {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ strictUpper n) (hB : B ∈ strictUpper n) :
    (A * B).trace = 0 := by
  simp [Matrix.trace, strictUpper_mul_diag hA hB]

/-- The index set `{(i,j) : Fin n × Fin n // i < j}` has cardinality `n.choose 2`. -/
lemma card_pairs_lt (n : ℕ) :
    Fintype.card {p : Fin n × Fin n // p.1 < p.2} = n.choose 2 := by
  classical
  rw [Fintype.card_subtype]
  -- Goal: (univ.filter fun p => p.1 < p.2).card = n.choose 2
  -- Sum over the second coordinate: card = Σ_j |{i : i < j}| = Σ_j j.val.
  -- Convert the filter-card to a double sum.
  have h1 : (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card =
      ∑ j : Fin n, (Finset.univ.filter fun i : Fin n => i < j).card := by
    -- Use sum_boole: card filter = ∑ boole
    simp only [Finset.card_filter]
    rw [show (Finset.univ : Finset (Fin n × Fin n)) = Finset.univ ×ˢ Finset.univ from rfl]
    rw [Finset.sum_product_right]
  rw [h1]
  -- |{i : Fin n | i < j}| = j.val
  have h2 : ∀ j : Fin n, (Finset.univ.filter fun i : Fin n => i < j).card = j.val := by
    intro j
    have : (Finset.univ.filter fun i : Fin n => i < j) = Finset.Iio j := by
      ext i; simp [Finset.mem_Iio]
    rw [this, Fin.card_Iio]
  simp only [h2]
  rw [Fin.sum_univ_eq_sum_range (fun i => i), Finset.sum_range_id, Nat.choose_two_right]

/-- The injective linear map `V ↦ (pairs with i < j → ℝ)` sending `X` to
the function `(i,j) ↦ X i j - X j i`. -/
noncomputable def antisymPart (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ]
      ({p : Fin n × Fin n // p.1 < p.2} → ℝ) where
  toFun X := fun p => X p.val.1 p.val.2 - X p.val.2 p.val.1
  map_add' X Y := by ext p; simp; ring
  map_smul' c X := by ext p; simp; ring

/-- If `X` is in the kernel of `antisymPart`, then `X` is symmetric. -/
lemma antisymPart_ker {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : antisymPart n X = 0) (i j : Fin n) (hij : i < j) :
    X i j = X j i := by
  have := congrFun hX ⟨(i, j), hij⟩
  simp [antisymPart] at this
  linarith

/-- If `X * X` has zero trace and `X` is symmetric, then `X = 0`. -/
lemma symm_zero_of_trace_sq_zero {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (hsymm : ∀ i j, X i j = X j i) (htr : (X * X).trace = 0) : X = 0 := by
  -- tr(X * X) = Σ_i (X * X) i i = Σ_i Σ_j X i j * X j i = Σ_{i,j} (X i j)^2.
  have hdiag : ∀ i : Fin n, (X * X) i i = ∑ j : Fin n, (X i j) ^ 2 := by
    intro i
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hsymm i j]; ring
  have hsum : (X * X).trace = ∑ i : Fin n, ∑ j : Fin n, (X i j) ^ 2 := by
    unfold Matrix.trace
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.diag_apply]
    exact hdiag i
  rw [hsum] at htr
  have hnn : ∀ i j : Fin n, 0 ≤ (X i j) ^ 2 := fun i j => sq_nonneg _
  have h1 : ∀ i : Fin n, ∑ j : Fin n, (X i j) ^ 2 = 0 := by
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg (fun j _ => hnn i j))).mp htr
    exact this i (Finset.mem_univ _)
  ext i j
  have h2 : (X i j) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn i j)).mp (h1 i) j (Finset.mem_univ _)
  have hXij : X i j = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num : (2:ℕ) ≠ 0) |>.mp h2
    exact this
  simp [hXij]

/-- For a subspace `V` satisfying the trace condition,
the map `antisymPart` restricted to `V` is injective. -/
lemma antisymPart_injOn (n : ℕ) (V : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : ∀ X ∈ V, ∀ Y ∈ V, (X * Y).trace = 0) :
    Set.InjOn (antisymPart n) V := by
  intro X hX Y hY hXY
  have hdiff : antisymPart n (X - Y) = 0 := by
    rw [map_sub]; simp [hXY]
  have hsym : ∀ i j, (X - Y) i j = (X - Y) j i := by
    intro i j
    rcases lt_trichotomy i j with hij | hij | hij
    · exact antisymPart_ker hdiff i j hij
    · rw [hij]
    · exact (antisymPart_ker hdiff j i hij).symm
  have htr : ((X - Y) * (X - Y)).trace = 0 :=
    hV _ (Submodule.sub_mem V hX hY) _ (Submodule.sub_mem V hX hY)
  have hzero := symm_zero_of_trace_sq_zero (X - Y) hsym htr
  exact sub_eq_zero.mp hzero

/-- The injective construction map: `f : pairs → matrices` sending a function
to the strictly upper triangular matrix with those entries. -/
noncomputable def upperFromPairs (n : ℕ) :
    ({p : Fin n × Fin n // p.1 < p.2} → ℝ) →ₗ[ℝ]
      Matrix (Fin n) (Fin n) ℝ where
  toFun f := fun i j => if h : i < j then f ⟨(i, j), h⟩ else 0
  map_add' f g := by
    ext i j
    by_cases h : i < j
    · simp [h]
    · simp [h]
  map_smul' c f := by
    ext i j
    by_cases h : i < j
    · simp [h]
    · simp [h]

lemma upperFromPairs_injective (n : ℕ) : Function.Injective (upperFromPairs n) := by
  intro f g hfg
  ext ⟨⟨i, j⟩, hij⟩
  have := congrFun (congrFun hfg i) j
  simp [upperFromPairs, hij] at this
  exact this

lemma upperFromPairs_mem (n : ℕ) (f) :
    upperFromPairs n f ∈ strictUpper n := by
  intro i j hji
  have hnij : ¬ (i < j) := by
    intro h; exact absurd (lt_of_le_of_lt hji h) (lt_irrefl _)
  simp [upperFromPairs, hnij]

lemma upperFromPairs_surjective_onto_strictUpper (n : ℕ) :
    ∀ A ∈ strictUpper n, ∃ f, upperFromPairs n f = A := by
  intro A hA
  refine ⟨fun ⟨⟨i, j⟩, hij⟩ => A i j, ?_⟩
  ext i j
  unfold upperFromPairs
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hij : i < j
  · simp [hij]
  · simp [hij]
    exact (hA i j (not_lt.mp hij)).symm

snip end

problem imc2005_p9 (n : ℕ) :
    IsGreatest
      { d : ℕ | ∃ V : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ),
        (∀ X ∈ V, ∀ Y ∈ V, (X * Y).trace = 0) ∧
        Module.finrank ℝ V = d }
      (answer n) := by
  rw [answer]
  refine ⟨?_, ?_⟩
  · -- Lower bound: V = strict upper triangular has dim n.choose 2.
    refine ⟨strictUpper n, ?_, ?_⟩
    · intro X hX Y hY
      exact strictUpper_trace hX hY
    · -- finrank = n.choose 2: image of upperFromPairs = strictUpper.
      have himg : LinearMap.range (upperFromPairs n) = strictUpper n := by
        apply le_antisymm
        · rintro A ⟨f, rfl⟩; exact upperFromPairs_mem n f
        · intro A hA
          obtain ⟨f, hf⟩ := upperFromPairs_surjective_onto_strictUpper n A hA
          exact ⟨f, hf⟩
      rw [← himg]
      rw [LinearMap.finrank_range_of_inj (upperFromPairs_injective n)]
      rw [Module.finrank_fintype_fun_eq_card]
      exact card_pairs_lt n
  · -- Upper bound.
    rintro d ⟨V, hV, rfl⟩
    -- antisymPart : V → pairs → ℝ is injective.
    have hinj : Function.Injective ((antisymPart n).domRestrict V) := by
      intro x y hxy
      rw [Subtype.ext_iff]
      apply antisymPart_injOn n V hV x.2 y.2
      have : (antisymPart n).domRestrict V x = (antisymPart n).domRestrict V y := hxy
      simpa [LinearMap.domRestrict_apply] using this
    have hle : Module.finrank ℝ V ≤
        Module.finrank ℝ ({p : Fin n × Fin n // p.1 < p.2} → ℝ) :=
      LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_fintype_fun_eq_card, card_pairs_lt] at hle
    exact hle

end Imc2005P9
