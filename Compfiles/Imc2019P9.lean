/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2019, Problem 9
(IMC 2019, Day 2, Problem 9)

Determine all positive integers `n` for which there exist invertible real
`n × n` matrices `A` and `B` satisfying `A B - B A = B^2 A`.

Answer: all even positive integers.
-/

namespace Imc2019P9

open Matrix

/-- The `2 × 2` witness for `A`. -/
def A2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- The `2 × 2` witness for `B`. -/
def B2 : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 1; -1, -1]

snip begin

/-- `A2` is invertible: its determinant is `-1`, nonzero. -/
lemma A2_isUnit : IsUnit A2 := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simp [A2, Matrix.det_fin_two]

/-- `B2` is invertible: its determinant is `2`, nonzero. -/
lemma B2_isUnit : IsUnit B2 := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simp [B2, Matrix.det_fin_two]

/-- The 2×2 witness satisfies `A B - B A = B * B * A`. -/
lemma twoByTwo_eq' : A2 * B2 - B2 * A2 = B2 * B2 * A2 := by
  simp only [A2, B2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply] <;> ring

/-- The 2×2 witness satisfies `A B - B A = B^2 * A`. -/
lemma twoByTwo_eq : A2 * B2 - B2 * A2 = B2 ^ 2 * A2 := by
  rw [pow_two]; exact twoByTwo_eq'

/-- Block-diagonal `A` matrix: `k` copies of `A2` along the diagonal. -/
noncomputable def Ablock (k : ℕ) : Matrix (Fin 2 × Fin k) (Fin 2 × Fin k) ℝ :=
  Matrix.blockDiagonal fun _ : Fin k => A2

/-- Block-diagonal `B` matrix: `k` copies of `B2` along the diagonal. -/
noncomputable def Bblock (k : ℕ) : Matrix (Fin 2 × Fin k) (Fin 2 × Fin k) ℝ :=
  Matrix.blockDiagonal fun _ : Fin k => B2

/-- The block-diagonal construction satisfies the equation `A B - B A = B² A`. -/
lemma block_eq (k : ℕ) : Ablock k * Bblock k - Bblock k * Ablock k = Bblock k ^ 2 * Ablock k := by
  unfold Ablock Bblock
  rw [pow_two]
  rw [show (Matrix.blockDiagonal fun _ : Fin k => A2) * Matrix.blockDiagonal (fun _ : Fin k => B2) =
      Matrix.blockDiagonal (fun _ : Fin k => A2 * B2) from (Matrix.blockDiagonal_mul _ _).symm]
  rw [show (Matrix.blockDiagonal fun _ : Fin k => B2) * Matrix.blockDiagonal (fun _ : Fin k => A2) =
      Matrix.blockDiagonal (fun _ : Fin k => B2 * A2) from (Matrix.blockDiagonal_mul _ _).symm]
  rw [show (Matrix.blockDiagonal fun _ : Fin k => B2) * Matrix.blockDiagonal (fun _ : Fin k => B2) =
      Matrix.blockDiagonal (fun _ : Fin k => B2 * B2) from (Matrix.blockDiagonal_mul _ _).symm]
  rw [show (Matrix.blockDiagonal fun _ : Fin k => B2 * B2) *
          Matrix.blockDiagonal (fun _ : Fin k => A2) =
      Matrix.blockDiagonal (fun _ : Fin k => B2 * B2 * A2) from (Matrix.blockDiagonal_mul _ _).symm]
  rw [← Matrix.blockDiagonal_sub]
  congr 1
  funext i
  simp only [Pi.sub_apply]
  exact twoByTwo_eq'

/-- The block-diagonal `A` is a unit. -/
lemma Ablock_isUnit (k : ℕ) : IsUnit (Ablock k) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  unfold Ablock
  rw [Matrix.det_blockDiagonal]
  rw [IsUnit.prod_iff]
  intro _ _
  exact (Matrix.isUnit_iff_isUnit_det _).mp A2_isUnit

/-- The block-diagonal `B` is a unit. -/
lemma Bblock_isUnit (k : ℕ) : IsUnit (Bblock k) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  unfold Bblock
  rw [Matrix.det_blockDiagonal]
  rw [IsUnit.prod_iff]
  intro _ _
  exact (Matrix.isUnit_iff_isUnit_det _).mp B2_isUnit

/-- Even existence, working over `Fin 2 × Fin k`. -/
lemma exists_even_pair (k : ℕ) :
    ∃ A B : Matrix (Fin 2 × Fin k) (Fin 2 × Fin k) ℝ,
      IsUnit A ∧ IsUnit B ∧ A * B - B * A = B ^ 2 * A :=
  ⟨Ablock k, Bblock k, Ablock_isUnit k, Bblock_isUnit k, block_eq k⟩

/-- Transport existence via an equivalence of index types (using `reindexAlgEquiv`). -/
lemma exists_of_equiv {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β)
    (h : ∃ A B : Matrix α α ℝ, IsUnit A ∧ IsUnit B ∧ A * B - B * A = B ^ 2 * A) :
    ∃ A B : Matrix β β ℝ, IsUnit A ∧ IsUnit B ∧ A * B - B * A = B ^ 2 * A := by
  obtain ⟨A, B, hA, hB, hEq⟩ := h
  set φ := Matrix.reindexAlgEquiv ℝ ℝ e
  refine ⟨φ A, φ B, hA.map φ, hB.map φ, ?_⟩
  have := congrArg φ hEq
  simp only [map_sub, map_mul, map_pow] at this
  exact this

/-- Solution for even `n`. -/
lemma solution_even {n : ℕ} (_hn_pos : 0 < n) (hn_even : Even n) :
    ∃ A B : Matrix (Fin n) (Fin n) ℝ, IsUnit A ∧ IsUnit B ∧ A * B - B * A = B ^ 2 * A := by
  obtain ⟨k, hk⟩ := hn_even
  have hn_eq : n = 2 * k := by omega
  have hEx := exists_even_pair k
  have e1 : Fin 2 × Fin k ≃ Fin (2 * k) := finProdFinEquiv
  have e2 : Fin (2 * k) ≃ Fin n := (Fin.castOrderIso hn_eq.symm).toEquiv
  exact exists_of_equiv (e1.trans e2) hEx

/-! ### Odd case: impossibility. -/

/-- Telescoping sum: `∑_{k ∈ [i, j)} (f(k+1) - f(k)) = f(j) - f(i)` for `i ≤ j`. -/
lemma sum_Ico_telescope (f : ℕ → ℝ) {i j : ℕ} (hij : i ≤ j) :
    ∑ k ∈ Finset.Ico i j, (f (k + 1) - f k) = f j - f i := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    rw [Finset.sum_Ico_succ_top hij, ih]; ring

/-- If a real sequence `f : ℕ → ℝ` takes values in a finite set and satisfies
`f (k+1) = f k ^ 2 + f k`, then `f k = 0` for some `k`. -/
lemma exists_zero_of_iter (f : ℕ → ℝ)
    (hrec : ∀ k, f (k + 1) = f k ^ 2 + f k)
    (s : Finset ℝ) (hs_mem : ∀ k, f k ∈ s) :
    ∃ k, f k = 0 := by
  have hpig : ∃ i j : ℕ, i < j ∧ f i = f j := by
    by_contra hne
    push Not at hne
    have hinj : Function.Injective (fun k : Fin (s.card + 1) => f k.val) := by
      intro ⟨i, hi⟩ ⟨j, hj⟩ hij
      simp only at hij
      rcases lt_trichotomy i j with h | h | h
      · exact absurd hij (hne i j h)
      · exact Fin.ext h
      · exact absurd hij.symm (hne j i h)
    have hsub : (Finset.univ : Finset (Fin (s.card + 1))).image
        (fun k : Fin (s.card + 1) => f k.val) ⊆ s := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨k, hk⟩ := hx
      rw [← hk]; exact hs_mem _
    have hinj_card : ((Finset.univ : Finset (Fin (s.card + 1))).image
        (fun k : Fin (s.card + 1) => f k.val)).card = s.card + 1 := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have := Finset.card_le_card hsub
    rw [hinj_card] at this
    omega
  obtain ⟨i, j, hij, hfij⟩ := hpig
  have htel := sum_Ico_telescope f hij.le
  have hsq : ∑ k ∈ Finset.Ico i j, f k ^ 2 = 0 := by
    have heq : ∀ k ∈ Finset.Ico i j, f (k + 1) - f k = f k ^ 2 := by
      intro k _
      rw [hrec k]; ring
    rw [← Finset.sum_congr rfl heq, htel, hfij, sub_self]
  have hmem_i : i ∈ Finset.Ico i j := Finset.mem_Ico.mpr ⟨le_refl _, hij⟩
  have hall : ∀ k ∈ Finset.Ico i j, f k ^ 2 = 0 := by
    intro k hk
    have hnn : ∀ x ∈ Finset.Ico i j, 0 ≤ f x ^ 2 := fun x _ => sq_nonneg _
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsq k hk
  refine ⟨i, sq_eq_zero_iff.mp (hall i hmem_i)⟩

/-- If `B *ᵥ v = lam • v` and `v ≠ 0`, then `B.charpoly.eval lam = 0`. -/
lemma charpoly_eval_eq_zero_of_eigenvalue {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (lam : ℝ) (v : Fin n → ℝ) (hv : v ≠ 0) (hBv : B *ᵥ v = lam • v) :
    B.charpoly.eval lam = 0 := by
  rw [Matrix.eval_charpoly]
  have hker : ((Matrix.scalar (Fin n)) lam - B) *ᵥ v = 0 := by
    rw [sub_mulVec]
    have h1 : (Matrix.scalar (Fin n)) lam *ᵥ v = lam • v := by
      ext i
      simp [Matrix.scalar_apply, Matrix.mulVec, Matrix.diagonal, dotProduct]
    rw [h1, hBv]; exact sub_self _
  -- det = 0 follows from nontrivial kernel.
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  exact ⟨v, hv, hker⟩

/-- `B.charpoly` has degree `n` (Fintype cardinality of its index type). -/
lemma charpoly_natDegree {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    B.charpoly.natDegree = n := by
  rw [Matrix.charpoly_natDegree_eq_dim]
  exact Fintype.card_fin n

/-- `B.charpoly` is monic. -/
lemma charpoly_monic' {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : B.charpoly.Monic :=
  Matrix.charpoly_monic B

/-- A monic polynomial over ℝ of odd natDegree has a real root. -/
lemma exists_root_of_odd_natDegree_monic {p : Polynomial ℝ}
    (hmonic : p.Monic) (hodd : Odd p.natDegree) : ∃ r : ℝ, p.eval r = 0 := by
  have hpos_deg : 0 < p.natDegree := by rcases hodd with ⟨k, hk⟩; omega
  have hne : p ≠ 0 := hmonic.ne_zero
  have hcont : Continuous (fun x => p.eval x) := p.continuous
  have hlc : p.leadingCoeff = 1 := hmonic
  have hdeg_pos : 0 < p.degree := Polynomial.natDegree_pos_iff_degree_pos.mp hpos_deg
  have hlc_nn : 0 ≤ p.leadingCoeff := by rw [hlc]; norm_num
  have hTop : Filter.Tendsto (fun x => p.eval x) Filter.atTop Filter.atTop :=
    Polynomial.tendsto_atTop_of_leadingCoeff_nonneg p hdeg_pos hlc_nn
  set Q : Polynomial ℝ := p.comp (-Polynomial.X) with hQ_def
  have hQ_natDeg : Q.natDegree = p.natDegree := by
    simp [Q, Polynomial.natDegree_comp]
  have hQ_lc : Q.leadingCoeff = -1 := by
    rw [hQ_def, Polynomial.comp_neg_X_leadingCoeff_eq, Odd.neg_one_pow hodd, hlc]; ring
  have hQ_deg_pos : 0 < Q.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp (by rw [hQ_natDeg]; exact hpos_deg)
  have hQ_lc_np : Q.leadingCoeff ≤ 0 := by rw [hQ_lc]; norm_num
  have hQ_top : Filter.Tendsto (fun x => Q.eval x) Filter.atTop Filter.atBot :=
    Polynomial.tendsto_atBot_of_leadingCoeff_nonpos Q hQ_deg_pos hQ_lc_np
  have hBot : Filter.Tendsto (fun x => p.eval x) Filter.atBot Filter.atBot := by
    have hh : Filter.Tendsto (fun x => p.eval (-x)) Filter.atTop Filter.atBot := by
      have : ∀ x, Q.eval x = p.eval (-x) := by intro x; simp [Q, Polynomial.eval_comp]
      convert hQ_top using 1; ext x; exact (this x).symm
    have := hh.comp Filter.tendsto_neg_atBot_atTop
    refine this.congr ?_; intro x; simp
  rcases (hBot.eventually (Filter.eventually_lt_atBot (0 : ℝ))).exists with ⟨a, ha⟩
  rcases (hTop.eventually (Filter.eventually_gt_atTop (0 : ℝ))).exists with ⟨b, hb⟩
  rcases lt_or_ge a b with hlt | hle
  · obtain ⟨r, _, hr⟩ := intermediate_value_Ioo hlt.le hcont.continuousOn
      (show (0 : ℝ) ∈ Set.Ioo (p.eval a) (p.eval b) from ⟨ha, hb⟩)
    exact ⟨r, hr⟩
  · have hlt' : b < a := by
      rcases lt_or_eq_of_le hle with h' | h'
      · exact h'
      · exfalso; subst h'; linarith
    obtain ⟨r, _, hr⟩ := intermediate_value_Ioo' hlt'.le hcont.continuousOn
      (show (0 : ℝ) ∈ Set.Ioo (p.eval a) (p.eval b) from ⟨ha, hb⟩)
    exact ⟨r, hr⟩

/-- Existence of a real eigenvector for a real matrix whose charpoly has a real root. -/
lemma exists_eigenvector_of_charpoly_root {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (lam : ℝ) (hlam : B.charpoly.eval lam = 0) :
    ∃ v : Fin n → ℝ, v ≠ 0 ∧ B *ᵥ v = lam • v := by
  rw [Matrix.eval_charpoly] at hlam
  rw [← Matrix.exists_mulVec_eq_zero_iff] at hlam
  obtain ⟨v, hv, hvker⟩ := hlam
  refine ⟨v, hv, ?_⟩
  rw [sub_mulVec] at hvker
  have h1 : (Matrix.scalar (Fin n)) lam *ᵥ v = lam • v := by
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec, Matrix.diagonal, dotProduct]
  rw [h1] at hvker
  have : lam • v = B *ᵥ v := sub_eq_zero.mp hvker
  exact this.symm

/-- The sequence of (eigenvalue, eigenvector) pairs starting from `(lam0, v0)`,
defined by `(μ, w) ↦ (μ + μ², A⁻¹ w)`. -/
noncomputable def eigSeq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (lam0 : ℝ) (v0 : Fin n → ℝ) :
    ℕ → ℝ × (Fin n → ℝ)
  | 0 => (lam0, v0)
  | k + 1 =>
    let p := eigSeq A lam0 v0 k
    (p.1 + p.1^2, A⁻¹ *ᵥ p.2)

lemma eigSeq_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (lam0 : ℝ) (v0 : Fin n → ℝ) :
    eigSeq A lam0 v0 0 = (lam0, v0) := rfl

lemma eigSeq_succ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (lam0 : ℝ) (v0 : Fin n → ℝ) (k : ℕ) :
    eigSeq A lam0 v0 (k + 1) =
      ((eigSeq A lam0 v0 k).1 + (eigSeq A lam0 v0 k).1 ^ 2,
       A⁻¹ *ᵥ (eigSeq A lam0 v0 k).2) := rfl

/-- Main impossibility result for odd n. -/
lemma no_solution_odd {n : ℕ} (hn_odd : Odd n)
    (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsUnit A) (hB : IsUnit B) (hEq : A * B - B * A = B ^ 2 * A) : False := by
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).mp hA
  have hBdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det _).mp hB
  -- Key identity: A B A⁻¹ = B + B².
  have hConj : A * B * A⁻¹ = B + B ^ 2 := by
    have h1 : A * B = (B + B ^ 2) * A := by
      have := hEq
      rw [sub_eq_iff_eq_add] at this
      -- this : A * B = B^2 * A + B * A
      rw [this]; noncomm_ring
    calc A * B * A⁻¹ = (B + B ^ 2) * A * A⁻¹ := by rw [h1]
      _ = B + B ^ 2 := by rw [Matrix.mul_nonsing_inv_cancel_right _ _ hAdet]
  -- Step 1: odd-degree charpoly has real root, thus real eigenvalue.
  have hchp_monic : B.charpoly.Monic := charpoly_monic' B
  have hchp_natDeg : B.charpoly.natDegree = n := charpoly_natDegree B
  have hchp_odd : Odd B.charpoly.natDegree := by rw [hchp_natDeg]; exact hn_odd
  obtain ⟨lam0, hlam0⟩ := exists_root_of_odd_natDegree_monic hchp_monic hchp_odd
  obtain ⟨v0, hv0, hBv0⟩ := exists_eigenvector_of_charpoly_root B lam0 hlam0
  -- Key iteration: for any eigenvector (μ, w), (μ + μ², A⁻¹ w) is also an eigenvector.
  have key : ∀ (μ : ℝ) (w : Fin n → ℝ), w ≠ 0 → B *ᵥ w = μ • w →
      (A⁻¹ *ᵥ w ≠ 0) ∧ (B *ᵥ (A⁻¹ *ᵥ w) = (μ + μ^2) • (A⁻¹ *ᵥ w)) := by
    intro μ w hw hBw
    refine ⟨?_, ?_⟩
    · -- A⁻¹ w ≠ 0.
      intro hzero
      have : A *ᵥ (A⁻¹ *ᵥ w) = A *ᵥ 0 := by rw [hzero]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hAdet, Matrix.one_mulVec,
          Matrix.mulVec_zero] at this
      exact hw this
    · -- Use: B = A⁻¹ (B+B²) A.
      have hB_alt : B = A⁻¹ * (B + B^2) * A := by
        calc B
            = (A⁻¹ * A) * B * (A⁻¹ * A) := by
              rw [Matrix.nonsing_inv_mul _ hAdet, one_mul, mul_one]
          _ = A⁻¹ * (A * B * A⁻¹) * A := by noncomm_ring
          _ = A⁻¹ * (B + B^2) * A := by rw [hConj]
      have hBBw : (B + B^2) *ᵥ w = (μ + μ^2) • w := by
        rw [Matrix.add_mulVec, hBw]
        have hB2w : B^2 *ᵥ w = μ^2 • w := by
          rw [pow_two, ← Matrix.mulVec_mulVec, hBw, Matrix.mulVec_smul, hBw, smul_smul, ← pow_two]
        rw [hB2w, add_smul]
      have hAAinv_w : A *ᵥ (A⁻¹ *ᵥ w) = w := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hAdet, Matrix.one_mulVec]
      have hexpand : (A⁻¹ * (B + B^2) * A) *ᵥ (A⁻¹ *ᵥ w) =
          A⁻¹ *ᵥ ((B + B^2) *ᵥ (A *ᵥ (A⁻¹ *ᵥ w))) := by
        rw [show A⁻¹ * (B + B^2) * A = A⁻¹ * ((B + B^2) * A) from by noncomm_ring]
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      calc B *ᵥ (A⁻¹ *ᵥ w)
          = (A⁻¹ * (B + B^2) * A) *ᵥ (A⁻¹ *ᵥ w) := by rw [← hB_alt]
        _ = A⁻¹ *ᵥ ((B + B^2) *ᵥ (A *ᵥ (A⁻¹ *ᵥ w))) := hexpand
        _ = A⁻¹ *ᵥ ((B + B^2) *ᵥ w) := by rw [hAAinv_w]
        _ = A⁻¹ *ᵥ ((μ + μ^2) • w) := by rw [hBBw]
        _ = (μ + μ^2) • (A⁻¹ *ᵥ w) := by rw [Matrix.mulVec_smul]
  -- Properties of the sequence.
  set σ := eigSeq A lam0 v0 with hσ_def
  have σ_prop : ∀ k, (σ k).2 ≠ 0 ∧ B *ᵥ (σ k).2 = (σ k).1 • (σ k).2 := by
    intro k
    induction k with
    | zero => exact ⟨hv0, hBv0⟩
    | succ k ih =>
      obtain ⟨hne, heig⟩ := ih
      rw [hσ_def, eigSeq_succ]
      rw [hσ_def] at hne heig
      exact key _ _ hne heig
  have σ_rec : ∀ k, (σ (k + 1)).1 = (σ k).1 ^ 2 + (σ k).1 := by
    intro k
    rw [hσ_def, eigSeq_succ]
    simp only
    ring
  -- All (σ k).1 are roots of charpoly.
  have mem_root : ∀ k, (σ k).1 ∈ B.charpoly.roots.toFinset := by
    intro k
    obtain ⟨hne, heig⟩ := σ_prop k
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hchp_monic.ne_zero]
    exact charpoly_eval_eq_zero_of_eigenvalue B _ _ hne heig
  -- By the iteration lemma, some (σ k).1 = 0.
  let f : ℕ → ℝ := fun k => (σ k).1
  obtain ⟨k, hk⟩ := exists_zero_of_iter f σ_rec _ mem_root
  -- But B invertible ⇒ 0 is not an eigenvalue of B.
  obtain ⟨hne, heig⟩ := σ_prop k
  have hB0 : B *ᵥ (σ k).2 = 0 := by
    rw [heig]
    show (σ k).1 • (σ k).2 = 0
    rw [show (σ k).1 = f k from rfl, hk, zero_smul]
  -- Contradicts B unit: if B *ᵥ w = 0 then w = 0.
  have : (σ k).2 = 0 := by
    have hdet : B.det ≠ 0 := hBdet.ne_zero
    by_contra hne'
    have := Matrix.exists_mulVec_eq_zero_iff (M := B).mp ⟨(σ k).2, hne', hB0⟩
    exact hdet this
  exact hne this

snip end

/-- The set of positive integers for which such matrices exist. -/
determine answer : Set ℕ := {n | Even n}

problem imc2019_p9 (n : ℕ) (hn : 1 ≤ n) :
    (∃ A B : Matrix (Fin n) (Fin n) ℝ, IsUnit A ∧ IsUnit B ∧
        A * B - B * A = B ^ 2 * A) ↔ n ∈ answer := by
  constructor
  · rintro ⟨A, B, hA, hB, hEq⟩
    show Even n
    by_contra hOdd
    rw [Nat.not_even_iff_odd] at hOdd
    exact (no_solution_odd hOdd A B hA hB hEq).elim
  · intro hEven
    exact solution_even hn hEven

end Imc2019P9
