/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2014, Problem 7

Let `A = (aᵢⱼ)` be a symmetric `n × n` real matrix with eigenvalues
`λ₁, …, λₙ`. Show that

  `∑_{i < j} aᵢᵢ aⱼⱼ ≥ ∑_{i < j} λᵢ λⱼ`.
-/

namespace Imc2014P7

open Matrix BigOperators Finset

/--
For a function `x : Fin n → ℝ`,
`(∑ x_i)^2 = ∑ x_i^2 + ∑_{(i,j) off-diagonal} x_i x_j`.
-/
lemma sq_sum_eq_sum_sq_plus_offDiag (n : ℕ) (x : Fin n → ℝ) :
    (∑ i, x i) ^ 2 =
      (∑ i, (x i) ^ 2) +
        ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, x p.1 * x p.2 := by
  have h1 : (∑ i, x i) ^ 2 =
      ∑ p ∈ (Finset.univ ×ˢ Finset.univ : Finset (Fin n × Fin n)),
        x p.1 * x p.2 := by
    rw [sq, Finset.sum_mul_sum]
    rw [← Finset.sum_product']
  rw [h1]
  -- Split univ ×ˢ univ = diag ∪ offDiag
  rw [show (Finset.univ ×ˢ Finset.univ : Finset (Fin n × Fin n)) =
      (Finset.univ : Finset (Fin n)).diag ∪ (Finset.univ : Finset (Fin n)).offDiag
      from (Finset.diag_union_offDiag (s := Finset.univ)).symm]
  rw [Finset.sum_union (Finset.disjoint_diag_offDiag _)]
  -- Diagonal sum
  have hdiag : ∑ p ∈ (Finset.univ : Finset (Fin n)).diag, x p.1 * x p.2
      = ∑ i, (x i) ^ 2 := by
    rw [show (Finset.univ : Finset (Fin n)).diag =
          (Finset.univ : Finset (Fin n)).map ⟨fun i => (i, i), fun _ _ h => (Prod.mk.inj h).1⟩
        from rfl]
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intros i _
    simp [sq]
  rw [hdiag]

/--
The off-diagonal sum equals twice the sum over `i < j` for symmetric `f`.
-/
lemma sum_offDiag_eq_two_sum_lt (n : ℕ) (f : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, f i j = f j i) :
    ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, f p.1 p.2
      = 2 * ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
              (fun p => p.1 < p.2), f p.1 p.2 := by
  let Slt : Finset (Fin n × Fin n) :=
    (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2)
  let Sgt : Finset (Fin n × Fin n) :=
    (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1)
  have hOff : (Finset.univ : Finset (Fin n)).offDiag = Slt ∪ Sgt := by
    ext ⟨i, j⟩
    simp only [Slt, Sgt, Finset.mem_offDiag, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact h.ne
      · exact h.ne'
  have hdisj : Disjoint Slt Sgt := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ h1 h2
    simp [Slt, Sgt] at h1 h2
    exact absurd h1 (asymm h2)
  rw [hOff, Finset.sum_union hdisj]
  have hswap : ∑ p ∈ Sgt, f p.1 p.2 = ∑ p ∈ Slt, f p.1 p.2 := by
    refine Finset.sum_nbij' (fun p => (p.2, p.1)) (fun p => (p.2, p.1))
      ?_ ?_ ?_ ?_ ?_
    · rintro ⟨i, j⟩ h
      simp only [Sgt, Finset.mem_filter, Finset.mem_univ, true_and] at h
      simp only [Slt, Finset.mem_filter, Finset.mem_univ, true_and]
      exact h
    · rintro ⟨i, j⟩ h
      simp only [Slt, Finset.mem_filter, Finset.mem_univ, true_and] at h
      simp only [Sgt, Finset.mem_filter, Finset.mem_univ, true_and]
      exact h
    · rintro ⟨i, j⟩ _; rfl
    · rintro ⟨i, j⟩ _; rfl
    · rintro ⟨i, j⟩ _; exact (hsym _ _)
  rw [hswap]
  ring

/--
For a symmetric (Hermitian) matrix `A` over ℝ, `tr(A * A) = ∑ λ_i^2`.
-/
lemma trace_sq_eq_sum_sq_eigenvalues
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (A * A).trace = ∑ i, (hA.eigenvalues i) ^ 2 := by
  -- Use the spectral theorem: A = U * D * Us where U is unitary, D is diagonal of eigenvalues.
  let U : Matrix n n ℝ := (hA.eigenvectorUnitary : Matrix n n ℝ)
  let Us : Matrix n n ℝ := (star hA.eigenvectorUnitary : Matrix n n ℝ)
  let D : Matrix n n ℝ := diagonal hA.eigenvalues
  have hUsU : Us * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hAeq : A = U * D * Us := by
    have h := hA.spectral_theorem
    have hcs : (Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hA.eigenvectorUnitary)
            (diagonal (RCLike.ofReal ∘ hA.eigenvalues)) =
        U * (diagonal (RCLike.ofReal ∘ hA.eigenvalues)) * Us := by
      show (hA.eigenvectorUnitary : Matrix n n ℝ) *
          (diagonal (RCLike.ofReal ∘ hA.eigenvalues)) *
          (star hA.eigenvectorUnitary : Matrix n n ℝ) =
        U * (diagonal (RCLike.ofReal ∘ hA.eigenvalues)) * Us
      rfl
    rw [hcs] at h
    have hD : (diagonal (RCLike.ofReal ∘ hA.eigenvalues) : Matrix n n ℝ) = D := by
      ext i j
      simp [D, diagonal]
    rw [hD] at h
    exact h
  -- Compute A * A.
  have hsq : A * A = U * (D * D) * Us := by
    rw [hAeq]
    -- (U*D*Us) * (U*D*Us) = U * D * (Us*U) * D * Us = U * D * 1 * D * Us = U * (D*D) * Us
    have : (U * D * Us) * (U * D * Us) = U * D * (Us * U) * D * Us := by
      simp only [Matrix.mul_assoc]
    rw [this, hUsU, Matrix.mul_one]
    rw [Matrix.mul_assoc U D D]
  rw [hsq]
  -- trace cyclicity: tr(U * (D*D) * Us) = tr((D*D) * (Us * U)) = tr(D*D)
  have htr : (U * (D * D) * Us).trace = (D * D).trace := by
    rw [show U * (D * D) * Us = (U * (D * D)) * Us from rfl,
        Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUsU, Matrix.one_mul]
  rw [htr]
  -- tr(D*D) = ∑ λ_i^2
  have hDD : (D * D : Matrix n n ℝ) = diagonal (fun i => hA.eigenvalues i ^ 2) := by
    show diagonal hA.eigenvalues * diagonal hA.eigenvalues = _
    rw [Matrix.diagonal_mul_diagonal]
    apply congrArg
    funext i; ring
  rw [hDD, Matrix.trace_diagonal]

/--
For a symmetric matrix `A`, `∑_{i,j} (A_{ij})^2 = tr(A * A)`.
-/
lemma sum_sq_entries_eq_trace_sq
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    ∑ i, ∑ j, (A i j) ^ 2 = (A * A).trace := by
  show ∑ i, ∑ j, (A i j) ^ 2 = ∑ i, (A * A) i i
  refine Finset.sum_congr rfl (fun i _ => ?_)
  show ∑ j, (A i j) ^ 2 = ∑ k, A i k * A k i
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hsym : A k i = A i k := by
    have h := hA.apply i k
    simp only [star_trivial] at h
    exact h
  rw [hsym, sq]

snip begin

-- (no auxiliary results outside the lemmas above)

snip end

problem imc2014_p7 (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2),
        A p.1 p.1 * A p.2 p.2 ≥
      ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2),
        hA.eigenvalues p.1 * hA.eigenvalues p.2 := by
  let d : Fin n → ℝ := fun i => A i i
  let lam : Fin n → ℝ := hA.eigenvalues
  have hd_sum_eq : ∑ i, d i = ∑ i, lam i := by
    have h2 : A.trace = ∑ i, (lam i : ℝ) := hA.trace_eq_sum_eigenvalues
    show ∑ i, A i i = _
    rw [show ∑ i, A i i = A.trace from rfl, h2]
  have hkey : ∑ i, (d i) ^ 2 ≤ ∑ i, (lam i) ^ 2 := by
    have h1 : ∑ i, (d i) ^ 2 ≤ ∑ i, ∑ j, (A i j) ^ 2 := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      have hsub : (A i i) ^ 2 = ∑ j ∈ ({i} : Finset (Fin n)), (A i j) ^ 2 := by simp
      show (A i i) ^ 2 ≤ _
      rw [hsub]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => sq_nonneg _)
    have h2 : ∑ i, ∑ j, (A i j) ^ 2 = (A * A).trace := sum_sq_entries_eq_trace_sq hA
    have h3 : (A * A).trace = ∑ i, (lam i) ^ 2 := trace_sq_eq_sum_sq_eigenvalues hA
    linarith
  have hd_id : (∑ i, d i) ^ 2 = (∑ i, (d i) ^ 2) +
        ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, d p.1 * d p.2 :=
    sq_sum_eq_sum_sq_plus_offDiag n d
  have hlam_id : (∑ i, lam i) ^ 2 = (∑ i, (lam i) ^ 2) +
        ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, lam p.1 * lam p.2 :=
    sq_sum_eq_sum_sq_plus_offDiag n lam
  have hd_off : ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, d p.1 * d p.2 =
      2 * ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
            (fun p => p.1 < p.2), d p.1 * d p.2 :=
    sum_offDiag_eq_two_sum_lt n (fun i j => d i * d j) (fun i j => mul_comm _ _)
  have hlam_off : ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, lam p.1 * lam p.2 =
      2 * ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
            (fun p => p.1 < p.2), lam p.1 * lam p.2 :=
    sum_offDiag_eq_two_sum_lt n (fun i j => lam i * lam j) (fun i j => mul_comm _ _)
  have hsumeq2 : (∑ i, d i) ^ 2 = (∑ i, lam i) ^ 2 := by rw [hd_sum_eq]
  -- Goal: ∑_{p p.1<p.2} lam p.1 * lam p.2 ≤ ∑_{p p.1<p.2} d p.1 * d p.2
  show ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2),
        lam p.1 * lam p.2 ≤
      ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2),
        d p.1 * d p.2
  linarith [hd_id, hlam_id, hd_off, hlam_off, hsumeq2, hkey]

end Imc2014P7
