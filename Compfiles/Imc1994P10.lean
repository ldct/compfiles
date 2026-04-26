/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1994, Problem 10 (Day 2 Problem 4)

Let `A` be a diagonal `n × n` matrix with characteristic polynomial
`(x - c₁)^{d₁} ⋯ (x - c_k)^{d_k}` (`c_i` distinct, `∑ dᵢ = n`).
Let `V = {B : A * B = B * A}`. Prove that `dim V = ∑ dᵢ²`.

## Proof outline

Write `A = Matrix.diagonal δ` for a function `δ : Fin n → ℝ`.

For a matrix `B`, `(A·B)ᵢⱼ = δᵢ Bᵢⱼ` while `(B·A)ᵢⱼ = δⱼ Bᵢⱼ`. So `A * B = B * A`
iff `Bᵢⱼ = 0` whenever `δᵢ ≠ δⱼ`.

Hence `V` has a basis indexed by `S := {(i,j) : δᵢ = δⱼ}`, given by the matrix
units `single i j 1`. Therefore `dim V = #S`.

If we group indices by their `δ`-value (so the value `c_m` is achieved exactly
`d_m` times), then `#S = ∑_m d_m²`.
-/

namespace Imc1994P10

open scoped Matrix

/-- The commutant of `Matrix.diagonal δ` as a submodule of all matrices. -/
def commutant {R : Type*} [CommRing R] {n : ℕ} (δ : Fin n → R) :
    Submodule R (Matrix (Fin n) (Fin n) R) where
  carrier := { B | Matrix.diagonal δ * B = B * Matrix.diagonal δ }
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [mul_add, add_mul, hx, hy]
  smul_mem' c x hx := by
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [Matrix.mul_smul, Matrix.smul_mul, hx]

/-- Index set of the canonical basis of the commutant. -/
def diagSet {n : ℕ} {R : Type*} [DecidableEq R] (δ : Fin n → R) :
    Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => δ p.1 = δ p.2)

@[simp] lemma mem_diagSet {n : ℕ} {R : Type*} [DecidableEq R] (δ : Fin n → R)
    (p : Fin n × Fin n) : p ∈ diagSet δ ↔ δ p.1 = δ p.2 := by
  simp [diagSet]

snip begin

variable {R : Type*} [CommRing R] {n : ℕ}

/-- A matrix `B` lies in the commutant of `diagonal δ` iff `Bᵢⱼ = 0` whenever
`δ i ≠ δ j`. -/
lemma mem_commutant_iff [NoZeroDivisors R] (δ : Fin n → R)
    (B : Matrix (Fin n) (Fin n) R) :
    B ∈ commutant δ ↔ ∀ i j, δ i ≠ δ j → B i j = 0 := by
  show Matrix.diagonal δ * B = B * Matrix.diagonal δ ↔ _
  constructor
  · intro h i j hij
    have hij_apply := congrArg (fun M : Matrix _ _ _ => M i j) h
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at hij_apply
    -- hij_apply : δ i * B i j = B i j * δ j
    rw [mul_comm (B i j) (δ j)] at hij_apply
    have hzero : (δ i - δ j) * B i j = 0 := by linear_combination hij_apply
    rcases mul_eq_zero.mp hzero with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) hij
    · exact h1
  · intro h
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : δ i = δ j
    · rw [hij, mul_comm]
    · rw [h i j hij, zero_mul, mul_zero]

variable [DecidableEq R]

/-- The element of `diagSet` for `(i, j)` when `δ i = δ j`. -/
def diagSetMk (δ : Fin n → R) (i j : Fin n) (h : δ i = δ j) : diagSet δ :=
  ⟨(i, j), by simp [h]⟩

/-- The linear equivalence between functions on `diagSet δ` and the commutant. -/
noncomputable def commutantEquiv [NoZeroDivisors R] (δ : Fin n → R) :
    (diagSet δ → R) ≃ₗ[R] commutant δ where
  toFun f := ⟨∑ p ∈ (diagSet δ).attach, f p • Matrix.single p.val.1 p.val.2 1, by
    rw [mem_commutant_iff]
    intro i j hij
    rw [Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro p _
    rw [Matrix.smul_apply]
    by_cases hp : p.val.1 = i ∧ p.val.2 = j
    · obtain ⟨hp1, hp2⟩ := hp
      have hp_eq : δ p.val.1 = δ p.val.2 := (mem_diagSet δ p.val).mp p.property
      rw [hp1, hp2] at hp_eq
      exact absurd hp_eq hij
    · rw [Matrix.single_apply, if_neg hp, smul_zero]⟩
  map_add' f g := by
    apply Subtype.ext
    show (∑ p ∈ _, (f + g) p • _) = (∑ p ∈ _, f p • _) + (∑ p ∈ _, g p • _)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intros p _
    rw [Pi.add_apply, add_smul]
  map_smul' c f := by
    apply Subtype.ext
    show (∑ p ∈ _, (c • f) p • _) = c • (∑ p ∈ _, f p • _)
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intros p _
    rw [Pi.smul_apply, smul_eq_mul, ← smul_smul]
  invFun B p := B.val p.val.1 p.val.2
  left_inv := by
    intro f
    funext p
    show (∑ q ∈ _, f q • Matrix.single q.val.1 q.val.2 1) p.val.1 p.val.2 = f p
    rw [Matrix.sum_apply]
    rw [Finset.sum_eq_single p]
    · rw [Matrix.smul_apply, Matrix.single_apply_same, smul_eq_mul, mul_one]
    · intros q _ hq
      rw [Matrix.smul_apply]
      have : ¬(q.val.1 = p.val.1 ∧ q.val.2 = p.val.2) := by
        intro ⟨h1, h2⟩
        apply hq
        apply Subtype.ext
        exact Prod.ext h1 h2
      rw [Matrix.single_apply, if_neg this, smul_zero]
    · intros h; exact absurd (Finset.mem_attach _ p) h
  right_inv := by
    intro B
    apply Subtype.ext
    ext i j
    show (∑ p ∈ (diagSet δ).attach,
            B.val p.val.1 p.val.2 • Matrix.single p.val.1 p.val.2 (1 : R)) i j = B.val i j
    rw [Matrix.sum_apply]
    by_cases hij : δ i = δ j
    · -- Sum over (diagSet δ).attach equals just the term at (i,j).
      let p₀ : diagSet δ := diagSetMk δ i j hij
      rw [Finset.sum_eq_single p₀]
      · show B.val p₀.val.1 p₀.val.2 * (Matrix.single p₀.val.1 p₀.val.2 1) i j = B.val i j
        show B.val i j * Matrix.single i j 1 i j = B.val i j
        rw [Matrix.single_apply_same, mul_one]
      · intros q _ hq
        rw [Matrix.smul_apply]
        have : ¬(q.val.1 = i ∧ q.val.2 = j) := by
          intro ⟨h1, h2⟩
          apply hq
          apply Subtype.ext
          show q.val = (i, j)
          exact Prod.ext h1 h2
        rw [Matrix.single_apply, if_neg this, smul_zero]
      · intros h; exact absurd (Finset.mem_attach _ p₀) h
    · have hB := (mem_commutant_iff δ B.val).mp B.property i j hij
      rw [hB]
      apply Finset.sum_eq_zero
      intros p _
      rw [Matrix.smul_apply]
      have hp_eq : δ p.val.1 = δ p.val.2 := (mem_diagSet δ p.val).mp p.property
      have : ¬(p.val.1 = i ∧ p.val.2 = j) := by
        intro ⟨h1, h2⟩
        rw [h1, h2] at hp_eq
        exact hij hp_eq
      rw [Matrix.single_apply, if_neg this, smul_zero]

snip end

variable {R : Type*} [CommRing R] [DecidableEq R] {n : ℕ}

/-- Helper computing the finrank of the commutant in terms of `diagSet`. -/
lemma finrank_commutant [Nontrivial R] [NoZeroDivisors R] (δ : Fin n → R) :
    Module.finrank R (commutant δ) = (diagSet δ).card := by
  have e := (commutantEquiv δ).symm
  rw [LinearEquiv.finrank_eq e]
  rw [Module.finrank_pi R (ι := diagSet δ)]
  exact Fintype.card_coe _

set_option linter.unusedSectionVars false in
/-- The auxiliary count: `#{(i,j) : δ i = δ j} = ∑_c (#δ⁻¹(c))²` summed over distinct values
of `δ`. -/
lemma diagSet_card_eq_sum_sq (δ : Fin n → R) :
    (diagSet δ).card =
      ∑ c ∈ Finset.univ.image δ,
        ((Finset.univ.filter (fun i : Fin n => δ i = c)).card)^2 := by
  unfold diagSet
  rw [show (Finset.univ.filter (fun p : Fin n × Fin n => δ p.1 = δ p.2)) =
      (Finset.univ.image δ).biUnion (fun c =>
        (Finset.univ.filter (fun i => δ i = c)) ×ˢ (Finset.univ.filter (fun j => δ j = c))) from ?_]
  · rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl ?_
      intros c _
      rw [Finset.card_product, sq]
    · intros c _ c' _ hcc
      simp only [Function.onFun, Finset.disjoint_left, Finset.mem_product,
                 Finset.mem_filter, Finset.mem_univ, true_and]
      rintro p ⟨h1, _⟩ ⟨h2, _⟩
      exact hcc (h1.symm.trans h2)
  · ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
               Finset.mem_image, Finset.mem_product]
    constructor
    · intro h
      exact ⟨δ p.1, ⟨p.1, rfl⟩, rfl, h.symm⟩
    · rintro ⟨c', _, h1, h2⟩
      exact h1.trans h2.symm

/-- Main problem: given a diagonal matrix `A = diagonal δ` over `ℝ`, the dimension of
its commutant equals the sum of squares of multiplicities of its eigenvalues. -/
problem imc1994_p10 (n k : ℕ) (c : Fin k → ℝ) (hc : Function.Injective c)
    (d : Fin k → ℕ) (δ : Fin n → ℝ)
    (hδ_range : ∀ i, ∃ m, δ i = c m)
    (hδ_count : ∀ m, (Finset.univ.filter (fun i : Fin n => δ i = c m)).card = d m) :
    Module.finrank ℝ (commutant δ) = ∑ m, (d m)^2 := by
  rw [finrank_commutant, diagSet_card_eq_sum_sq]
  have himage : Finset.univ.image δ = (Finset.univ.filter (fun m => d m ≠ 0)).image c := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, ne_eq]
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨m, hm⟩ := hδ_range i
      refine ⟨m, ?_, hm.symm⟩
      have hi : i ∈ Finset.univ.filter (fun i : Fin n => δ i = c m) := by
        rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hm⟩
      have hcard : (Finset.univ.filter (fun i : Fin n => δ i = c m)).card ≠ 0 := by
        rw [Finset.card_ne_zero]; exact ⟨i, hi⟩
      rw [hδ_count] at hcard; exact hcard
    · rintro ⟨m, hdm, rfl⟩
      have : (Finset.univ.filter (fun i : Fin n => δ i = c m)).card ≠ 0 := by
        rw [hδ_count]; exact hdm
      rw [Finset.card_ne_zero] at this
      obtain ⟨i, hi⟩ := this
      rw [Finset.mem_filter] at hi
      exact ⟨i, hi.2⟩
  rw [himage]
  rw [Finset.sum_image (fun a _ b _ hab => hc hab)]
  -- Now: ∑ m ∈ filter (d m ≠ 0), (#{i : δ i = c m})² = ∑ m, (d m)²
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intros m _
  rw [hδ_count]
  by_cases hm : d m = 0
  · simp [hm]
  · simp [hm]

end Imc1994P10
