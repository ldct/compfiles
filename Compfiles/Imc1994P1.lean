/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1994, Problem 1 (a)

Let `A` be an `n × n` (`n ≥ 2`) symmetric, invertible matrix with strictly positive
real entries. Show that the number of zero entries of `A⁻¹` is at most `n² - 2n`.

## Proof outline

For each column `m` of `B := A⁻¹`, the row `k ≠ m` of the equation `A * B = 1`
gives `∑ᵢ A k i * B i m = 0`. Since each `A k i > 0`, the column `i ↦ B i m`
cannot have only one nonzero entry (a single positive coefficient times a single
nonzero would be nonzero). So each column of `B` has at least two nonzero
entries, hence at most `n - 2` zero entries. Summing over `n` columns gives at
most `n(n-2) = n² - 2n` zero entries in total.
-/

namespace Imc1994P1

open Matrix

/-- For each column `m` of `A⁻¹`, the column has at least two nonzero entries.
This is the key lemma. -/
lemma two_nonzero_per_column {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsUnit A.det)
    (hpos : ∀ i j, 0 < A i j) (m : Fin n) :
    2 ≤ ((Finset.univ : Finset (Fin n)).filter (fun i => A⁻¹ i m ≠ 0)).card := by
  by_contra hlt
  push Not at hlt
  -- The set S of indices i with A⁻¹ i m ≠ 0 has cardinality ≤ 1.
  set S : Finset (Fin n) := (Finset.univ : Finset (Fin n)).filter
    (fun i => A⁻¹ i m ≠ 0) with hSdef
  interval_cases h : S.card
  · -- S.card = 0: column m of A⁻¹ is all zero.
    have hall : ∀ i, A⁻¹ i m = 0 := by
      intro i
      by_contra hne
      have : i ∈ S := by simp [hSdef, hne]
      have : 0 < S.card := Finset.card_pos.mpr ⟨i, this⟩
      omega
    -- But (A * A⁻¹) m m = 1, while it equals ∑ᵢ A m i * A⁻¹ i m = 0.
    have hmul : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
    have h1 : (A * A⁻¹) m m = 1 := by rw [hmul]; simp
    have h0 : (A * A⁻¹) m m = 0 := by
      simp [Matrix.mul_apply]
      exact Finset.sum_eq_zero (fun i _ => by rw [hall i]; ring)
    rw [h1] at h0
    exact one_ne_zero h0
  · -- S.card = 1: column m of A⁻¹ has exactly one nonzero entry, at some index i₀.
    rw [Finset.card_eq_one] at h
    obtain ⟨i₀, hS_eq⟩ := h
    have hi₀_ne : A⁻¹ i₀ m ≠ 0 := by
      have : i₀ ∈ S := by rw [hS_eq]; exact Finset.mem_singleton_self i₀
      simpa [hSdef] using this
    have hother : ∀ i, i ≠ i₀ → A⁻¹ i m = 0 := by
      intro i hne
      by_contra hne0
      have : i ∈ S := by simp [hSdef, hne0]
      rw [hS_eq] at this
      exact hne (Finset.mem_singleton.mp this)
    -- Choose k ≠ m. Such k exists since n ≥ 2.
    have hexists_k : ∃ k : Fin n, k ≠ m := by
      by_contra hall_eq
      push Not at hall_eq
      -- Then every k equals m, so n ≤ 1.
      have : Fintype.card (Fin n) ≤ 1 := by
        rw [Fintype.card_fin]
        by_contra hgt
        push Not at hgt
        -- There exist two distinct elements in Fin n.
        have h2 : 2 ≤ n := by omega
        let a : Fin n := ⟨0, by omega⟩
        let b : Fin n := ⟨1, by omega⟩
        have hab : a ≠ b := by
          intro heq
          have : (0 : ℕ) = 1 := by
            have := Fin.mk.inj_iff.mp heq
            exact this
          exact zero_ne_one this
        have ha := hall_eq a
        have hb := hall_eq b
        rw [ha] at hab
        exact hab hb.symm
      rw [Fintype.card_fin] at this
      omega
    obtain ⟨k, hkm⟩ := hexists_k
    -- Then (A * A⁻¹) k m = 0 (off-diagonal of identity).
    have hmul : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
    have h0 : (A * A⁻¹) k m = 0 := by
      rw [hmul]; simp [hkm]
    -- But (A * A⁻¹) k m = ∑ᵢ A k i * A⁻¹ i m = A k i₀ * A⁻¹ i₀ m.
    have hsum_eq : (A * A⁻¹) k m = A k i₀ * A⁻¹ i₀ m := by
      simp [Matrix.mul_apply]
      rw [Finset.sum_eq_single i₀]
      · intro b _ hb
        rw [hother b hb]; ring
      · intro hi₀; exact absurd (Finset.mem_univ i₀) hi₀
    have hak : 0 < A k i₀ := hpos k i₀
    have hprod : A k i₀ * A⁻¹ i₀ m ≠ 0 := mul_ne_zero (ne_of_gt hak) hi₀_ne
    rw [hsum_eq] at h0
    exact hprod h0

set_option linter.unusedVariables false in
problem imc1994_p1 {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hsymm : A.IsSymm)
    (hinv : IsUnit A.det)
    (hpos : ∀ i j, 0 < A i j) :
    ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => A⁻¹ p.1 p.2 = 0)).card
      ≤ n^2 - 2 * n := by
  -- Count zeros of A⁻¹ column by column.
  -- Per column m, the number of zero entries is ≤ n - 2.
  -- Total: ≤ n * (n - 2) = n² - 2n.
  set Z : Finset (Fin n × Fin n) :=
    (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => A⁻¹ p.1 p.2 = 0) with hZdef
  -- Express Z as the disjoint union over m of the "zero-rows-in-column-m" sets.
  have hZ_eq : Z.card = ∑ m : Fin n,
      ((Finset.univ : Finset (Fin n)).filter (fun i => A⁻¹ i m = 0)).card := by
    rw [hZdef]
    rw [Finset.card_filter]
    rw [show (Finset.univ : Finset (Fin n × Fin n)) = (Finset.univ : Finset (Fin n)) ×ˢ
              (Finset.univ : Finset (Fin n)) from rfl]
    rw [Finset.sum_product_right]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.card_filter]
  -- Each column has at most n - 2 zeros.
  have hcol_bound : ∀ m : Fin n,
      ((Finset.univ : Finset (Fin n)).filter (fun i => A⁻¹ i m = 0)).card ≤ n - 2 := by
    intro m
    have h2 := two_nonzero_per_column hn A hinv hpos m
    -- Number of zeros + number of nonzeros = n.
    have hsplit : ((Finset.univ : Finset (Fin n)).filter (fun i => A⁻¹ i m = 0)).card
                + ((Finset.univ : Finset (Fin n)).filter (fun i => A⁻¹ i m ≠ 0)).card = n := by
      rw [← Finset.card_union_of_disjoint, Finset.filter_union_filter_not_eq]
      · simp
      · rw [Finset.disjoint_filter]
        intros _ _ h1 h2
        exact h2 h1
    omega
  rw [hZ_eq]
  calc ∑ m : Fin n,
        ((Finset.univ : Finset (Fin n)).filter (fun i => A⁻¹ i m = 0)).card
      ≤ ∑ _m : Fin n, (n - 2) := Finset.sum_le_sum (fun m _ => hcol_bound m)
    _ = n * (n - 2) := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    _ = n^2 - 2 * n := by
        have h2 : 2 * n ≤ n * n := Nat.mul_le_mul_right n hn
        have hsq : n^2 = n * n := sq n
        rw [hsq, Nat.mul_sub n n 2, mul_comm n 2]

end Imc1994P1
