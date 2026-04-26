/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2007, Problem 3
(IMC 2007, Day 1, Problem 3)

Call a polynomial `P(x_1, …, x_k)` *good* if there exist `2 × 2` real matrices
`A_1, …, A_k` such that `P = det(x_1 A_1 + ⋯ + x_k A_k)`.

Find all positive integers `k` for which every homogeneous polynomial of
degree `2` in `k` variables is good.

Answer: `k ∈ {1, 2}`.
-/

namespace Imc2007P3

open Matrix

/-- We represent a homogeneous polynomial of degree `2` in `k` variables by
its coefficient function `c : Fin k → Fin k → ℝ`, with the understanding
that the associated polynomial is
`Q(x) = ∑_{i, j} c i j · x_i · x_j`.
Every homogeneous quadratic arises this way. -/
def QuadForm (k : ℕ) (c : Fin k → Fin k → ℝ) (x : Fin k → ℝ) : ℝ :=
  ∑ i, ∑ j, c i j * x i * x j

/-- A function `P : (Fin k → ℝ) → ℝ` is *good* if there exist `2 × 2` real
matrices `A_1, …, A_k` such that `P(x) = det(∑ x_i A_i)` for every `x`. -/
def IsGood (k : ℕ) (P : (Fin k → ℝ) → ℝ) : Prop :=
  ∃ A : Fin k → Matrix (Fin 2) (Fin 2) ℝ,
    ∀ x : Fin k → ℝ, P x = (∑ i, x i • A i).det

/-- The property that every homogeneous quadratic in `k` variables is good. -/
def AllQuadraticsGood (k : ℕ) : Prop :=
  ∀ c : Fin k → Fin k → ℝ, IsGood k (QuadForm k c)

snip begin

/-! ### k = 1: every quadratic `α x²` is good. -/

/-- For `k = 1`, the single matrix `![![1,0],![0,α]]` witnesses goodness. -/
lemma allGood_one : AllQuadraticsGood 1 := by
  intro c
  set α : ℝ := c 0 0
  refine ⟨fun _ => !![1, 0; 0, α], ?_⟩
  intro x
  simp [QuadForm, Matrix.det_fin_two, α]
  ring

/-! ### k = 2: every quadratic `α x² + β y² + γ x y` is good. -/

/-- For `k = 2`, the matrices
`A_1 = ![[1, 0], [0, α]]` and `A_2 = ![[0, β], [-1, γ]]`
witness goodness, where `α = c₀₀`, `β = c₁₁`, `γ = c₀₁ + c₁₀`.

Computing: with `x = x 0`, `y = x 1`,
`x A_1 + y A_2 = [[x, β y], [-y, α x + γ y]]`,
`det = x (α x + γ y) - β y · (-y) = α x² + γ x y + β y²`,
matching `QuadForm 2 c = c₀₀ x² + (c₀₁ + c₁₀) x y + c₁₁ y²`. -/
lemma allGood_two : AllQuadraticsGood 2 := by
  intro c
  set α : ℝ := c 0 0
  set β : ℝ := c 1 1
  set γ : ℝ := c 0 1 + c 1 0
  refine ⟨![!![1, 0; 0, α], !![0, β; -1, γ]], ?_⟩
  intro x
  simp [QuadForm, Fin.sum_univ_two, Matrix.det_fin_two, α, β, γ]
  ring

/-! ### k ≥ 3: the polynomial `∑ x_i²` is not good.

Proof: if it were, with matrices `A_1, …, A_k`, consider the first columns
`v_i := (A_i) · e_0 ∈ ℝ²`. Since `k ≥ 3`, these `k` vectors in `ℝ²` are
linearly dependent, so there exist `y_i` not all zero with
`∑ y_i v_i = 0`. Then the first column of `M := ∑ y_i A_i` is zero, so
`det M = 0`. But by assumption `det M = ∑ y_i² > 0`, contradiction. -/

/-- For `k ≥ 3`, the sum-of-squares quadratic form is not good. -/
lemma sumSq_not_good {k : ℕ} (hk : 3 ≤ k) :
    ¬ IsGood k (fun x : Fin k → ℝ => ∑ i, (x i) ^ 2) := by
  rintro ⟨A, hA⟩
  -- Define v_i = A_i · e_0 ∈ Fin 2 → ℝ, i.e. the first column of A_i.
  let v : Fin k → (Fin 2 → ℝ) := fun i r => A i r 0
  -- Since k ≥ 3 > 2, the vectors {v i} are linearly dependent in Fin 2 → ℝ.
  have hdep : ¬ LinearIndependent ℝ v := by
    intro hli
    have hle := hli.fintype_card_le_finrank (R := ℝ) (M := Fin 2 → ℝ)
    simp at hle
    omega
  -- Extract y with ∑ y i • v i = 0 and y ≠ 0.
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨y, hy_sum, i₀, hyi₀⟩ := hdep
  -- Then M := ∑ y i • A i has zero first column.
  let M : Matrix (Fin 2) (Fin 2) ℝ := ∑ i, y i • A i
  have hM_col : ∀ r : Fin 2, M r 0 = 0 := by
    intro r
    have : M r 0 = ∑ i, y i * A i r 0 := by
      simp [M, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [this]
    have : (∑ i, y i • v i) r = 0 := by rw [hy_sum]; rfl
    simpa [v, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] using this
  -- Hence det M = 0.
  have hdet : M.det = 0 := by
    rw [show M = Mᵀᵀ from rfl]
    rw [Matrix.det_transpose]
    apply Matrix.det_eq_zero_of_row_eq_zero (i := 0)
    intro j
    simp [Matrix.transpose_apply, hM_col j]
  -- But det M = ∑ y_i² by hypothesis.
  have hsum_sq : M.det = ∑ i, (y i) ^ 2 := by
    have := hA y
    simpa [M] using this.symm
  -- Therefore ∑ y_i² = 0, giving y = 0, contradicting hyi₀.
  have hall : ∀ i, y i = 0 := by
    have hzero : ∑ i, (y i) ^ 2 = 0 := by rw [← hsum_sq]; exact hdet
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ (y i) ^ 2 := fun i _ => sq_nonneg _
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero i (Finset.mem_univ _)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  exact hyi₀ (hall i₀)

/-- Build a coefficient matrix `c` for the sum-of-squares polynomial. -/
def sumSqCoeff (k : ℕ) : Fin k → Fin k → ℝ := fun i j => if i = j then 1 else 0

lemma quadForm_sumSqCoeff (k : ℕ) (x : Fin k → ℝ) :
    QuadForm k (sumSqCoeff k) x = ∑ i, (x i) ^ 2 := by
  unfold QuadForm sumSqCoeff
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp; ring
  · intro j _ hji
    simp [Ne.symm hji]
  · intro h
    exact (h (Finset.mem_univ _)).elim

snip end

/-- The set of `k ≥ 1` for which every homogeneous degree-2 polynomial in
`k` variables is good. -/
determine goodDims : Set ℕ := {1, 2}

/-- IMC 2007 P3:

For a positive integer `k`, every homogeneous polynomial of degree `2` in
`k` variables can be written as `det(x_1 A_1 + ⋯ + x_k A_k)` for some
`2 × 2` real matrices `A_1, …, A_k` if and only if `k ∈ {1, 2}`. -/
problem imc2007_p3 (k : ℕ) (hk : 1 ≤ k) :
    AllQuadraticsGood k ↔ k ∈ goodDims := by
  constructor
  · intro hAll
    -- If all hom-quadratics in k vars are good and k ≥ 3, the sum-of-squares
    -- is good, contradicting sumSq_not_good.
    by_contra hne
    simp [goodDims] at hne
    have hk3 : 3 ≤ k := by
      obtain ⟨h1, h2⟩ := hne
      omega
    have hgood := hAll (sumSqCoeff k)
    have : IsGood k (fun x : Fin k → ℝ => ∑ i, (x i) ^ 2) := by
      convert hgood using 1
      ext x
      exact (quadForm_sumSqCoeff k x).symm
    exact sumSq_not_good hk3 this
  · intro hk'
    simp [goodDims] at hk'
    rcases hk' with rfl | rfl
    · exact allGood_one
    · exact allGood_two

end Imc2007P3
