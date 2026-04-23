/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2022, Problem 7

Let `A_1, …, A_k` be `n × n` idempotent complex matrices such that
`A_i A_j = -A_j A_i` for all `i ≠ j`. Prove that at least one of them
has rank at most `n / k`.
-/

namespace Imc2022P7

open Matrix

snip begin

/-- For an idempotent complex matrix, the trace (as a complex number) equals
the rank (cast to a complex number). -/
lemma trace_eq_rank_of_idempotent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (h : A * A = A) :
    (A.trace : ℂ) = (A.rank : ℂ) := by
  -- Translate to `LinearMap` language via `Matrix.toLin'`.
  have hidem : IsIdempotentElem (A.toLin' : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) := by
    unfold IsIdempotentElem
    rw [show A.toLin' * A.toLin' = (A * A).toLin' from (Matrix.toLin'_mul A A).symm, h]
  -- Hence `A.toLin'` is a projection onto its range.
  have hproj : LinearMap.IsProj (LinearMap.range A.toLin') A.toLin' :=
    LinearMap.IsIdempotentElem.isProj_range _ hidem
  -- Apply `IsProj.trace` to get `trace = finrank(range)` in ℂ.
  have htr :
      LinearMap.trace ℂ (Fin n → ℂ) A.toLin' =
        (Module.finrank ℂ (LinearMap.range A.toLin') : ℂ) :=
    hproj.trace
  -- Relate the LinearMap trace to the matrix trace.
  rw [Matrix.trace_toLin'_eq] at htr
  rw [htr]
  -- Relate `finrank (range A.toLin')` to `A.rank`.
  rfl

/-- The sum of pairwise anti-commuting idempotent matrices is idempotent. -/
lemma sum_mul_sum_eq_sum {n k : ℕ} (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hidem : ∀ i, A i * A i = A i)
    (hanticomm : ∀ i j, i ≠ j → A i * A j = - (A j * A i)) :
    (∑ i, A i) * (∑ i, A i) = ∑ i, A i := by
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  -- Split ∑_i ∑_j (A i * A j) into diagonal + off-diagonal pieces via a product.
  have hprod : (∑ i : Fin k, ∑ j : Fin k, A i * A j) =
      ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)), A p.1 * A p.2 := by
    rw [← Finset.sum_product']
    rfl
  rw [hprod]
  -- Split (Finset.univ : Fin k × Fin k) = diag ∪ offDiag.
  have hsplit : (Finset.univ : Finset (Fin k × Fin k)) =
      (Finset.univ : Finset (Fin k)).diag ∪ (Finset.univ : Finset (Fin k)).offDiag := by
    rw [Finset.diag_union_offDiag, Finset.univ_product_univ]
  rw [hsplit, Finset.sum_union (Finset.disjoint_diag_offDiag _)]
  -- Diagonal part gives ∑ A i * A i = ∑ A i.
  have hdiag : (∑ p ∈ (Finset.univ : Finset (Fin k)).diag, A p.1 * A p.2) = ∑ i, A i := by
    rw [Finset.sum_diag]
    exact Finset.sum_congr rfl (fun i _ => hidem i)
  rw [hdiag]
  -- Off-diagonal part is zero, by pairing (i,j) with (j,i).
  suffices hoff : (∑ p ∈ (Finset.univ : Finset (Fin k)).offDiag, A p.1 * A p.2) = 0 by
    rw [hoff, add_zero]
  -- Use involution-style pairing via `Finset.sum_involution`.
  apply Finset.sum_involution (fun p _ => (p.2, p.1))
  · -- Pairing: A i * A j + A j * A i = 0.
    intro p hp
    rcases p with ⟨i, j⟩
    simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at hp
    have := hanticomm i j hp
    rw [this]
    simp [add_comm]
  · -- Fixed point condition: if f p ≠ 0 then (p.2, p.1) ≠ p.
    intro p hp _hne hfix
    rcases p with ⟨i, j⟩
    simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at hp
    simp only [Prod.mk.injEq] at hfix
    exact hp hfix.1.symm
  · intro p hp
    rcases p with ⟨i, j⟩
    simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at hp ⊢
    exact fun h => hp h.symm
  · intro p _
    rfl

snip end

/-- The problem: among pairwise anti-commuting idempotent complex
matrices, at least one has rank ≤ n/k. -/
problem imc2022_p7 {n k : ℕ} (hk : 0 < k) (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hidem : ∀ i, A i * A i = A i)
    (hanticomm : ∀ i j, i ≠ j → A i * A j = - (A j * A i)) :
    ∃ i, (A i).rank * k ≤ n := by
  classical
  set S : Matrix (Fin n) (Fin n) ℂ := ∑ i, A i with hS_def
  -- S is idempotent.
  have hS_idem : S * S = S := sum_mul_sum_eq_sum A hidem hanticomm
  -- rank(S) = trace(S) = ∑ trace(A i) = ∑ rank(A i), as ℂ, hence as ℕ.
  have hS_trace : (S.trace : ℂ) = (S.rank : ℂ) := trace_eq_rank_of_idempotent S hS_idem
  have hAi_trace : ∀ i, ((A i).trace : ℂ) = ((A i).rank : ℂ) :=
    fun i => trace_eq_rank_of_idempotent (A i) (hidem i)
  have hS_trace_eq : S.trace = ∑ i, (A i).trace := by
    simp [S, Matrix.trace_sum]
  have hrank_sum : (S.rank : ℂ) = ∑ i, ((A i).rank : ℂ) := by
    rw [← hS_trace, hS_trace_eq]
    exact Finset.sum_congr rfl (fun i _ => hAi_trace i)
  -- Cast to ℕ.
  have hrank_sum_nat : S.rank = ∑ i, (A i).rank := by
    have := hrank_sum
    have h1 : ((S.rank : ℂ) : ℂ) = ((∑ i, (A i).rank : ℕ) : ℂ) := by
      rw [this]; push_cast; rfl
    exact_mod_cast h1
  -- S.rank ≤ n.
  have hS_le_n : S.rank ≤ n := S.rank_le_height
  -- Hence ∑ rank(A i) ≤ n.
  have hsum_le : (∑ i, (A i).rank) ≤ n := hrank_sum_nat ▸ hS_le_n
  -- Pigeonhole: minimal rank ≤ n / k.
  by_contra hcon
  push Not at hcon
  -- Each (A i).rank * k > n, i.e. each rank > n/k. Sum > n.
  have : (∑ _i : Fin k, (n + 1)) ≤ ∑ i, (A i).rank * k := by
    apply Finset.sum_le_sum
    intro i _
    have := hcon i
    omega
  simp at this
  have hbad : (n + 1) * k ≤ (∑ i, (A i).rank) * k := by
    rw [Finset.sum_mul]
    linarith
  have : (n + 1) * k ≤ n * k := by
    calc (n + 1) * k ≤ (∑ i, (A i).rank) * k := hbad
      _ ≤ n * k := Nat.mul_le_mul_right k hsum_le
  have : n + 1 ≤ n := Nat.le_of_mul_le_mul_right this hk
  omega

end Imc2022P7
