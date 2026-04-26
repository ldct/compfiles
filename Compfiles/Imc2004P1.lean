/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2004, Problem 1

Let `S` be an infinite set of real numbers such that for every finite subset
`{s₁, …, sₖ} ⊆ S` one has `|s₁ + ⋯ + sₖ| < 1`. Show that `S` is countable.
-/

namespace Imc2004P1

open scoped BigOperators

snip begin

/-- If every finite subset of `T ⊆ ℝ` has `x > 1/n` for all its elements and
`T` has cardinality `≥ n` (with `n ≥ 1`), then its sum exceeds `1`. -/
lemma sum_gt_one_of_card_ge {n : ℕ} (hn : 1 ≤ n) (T : Finset ℝ)
    (hT : ∀ x ∈ T, (1 : ℝ) / n < x) (hcard : n ≤ T.card) :
    (1 : ℝ) < ∑ t ∈ T, t := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  calc (1 : ℝ) = n * (1 / n) := by field_simp
    _ ≤ T.card * (1 / n) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hcard
        · positivity
    _ = ∑ _ ∈ T, (1 / n : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ < ∑ t ∈ T, t :=
        Finset.sum_lt_sum_of_nonempty
          (by rw [Finset.nonempty_iff_ne_empty]; intro h; simp [h] at hcard; omega)
          (fun x hx => hT x hx)

lemma sum_lt_neg_one_of_card_ge {n : ℕ} (hn : 1 ≤ n) (T : Finset ℝ)
    (hT : ∀ x ∈ T, x < -(1 / n : ℝ)) (hcard : n ≤ T.card) :
    (∑ t ∈ T, t) < -1 := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; simp [h] at hcard; omega
  calc (∑ t ∈ T, t) < ∑ _ ∈ T, -(1 / n : ℝ) := by
          apply Finset.sum_lt_sum_of_nonempty hne
          intro x hx; exact hT x hx
    _ = T.card * -(1 / n : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ n * -(1 / n : ℝ) := by
        apply mul_le_mul_of_nonpos_right
        · exact_mod_cast hcard
        · rw [neg_nonpos]; positivity
    _ = -1 := by field_simp

snip end

problem imc2004_p1
    (S : Set ℝ)
    (hS : ∀ (T : Finset ℝ), ↑T ⊆ S → |∑ t ∈ T, t| < 1) :
    S.Countable := by
  -- For each positive n, Sₙ := S ∩ (1/n, ∞) has fewer than n elements, hence is finite.
  -- Similarly S_{-n} := S ∩ (-∞, -1/n) is finite.
  -- S ⊆ {0} ∪ ⋃ₙ (Sₙ ∪ S_{-n}); countable union of finite sets.
  have hSn_fin : ∀ n : ℕ, 1 ≤ n → (S ∩ Set.Ioi (1 / n : ℝ)).Finite := by
    intro n hn
    by_contra hinf
    rw [Set.not_finite] at hinf
    -- Extract n elements from the infinite set
    obtain ⟨T, hTsub, hTcard⟩ := hinf.exists_subset_card_eq n
    have hTS : ↑T ⊆ S := by
      intro x hx
      exact (hTsub hx).1
    have hTgt : ∀ x ∈ T, (1 : ℝ) / n < x := by
      intro x hx; exact (hTsub hx).2
    have hsum_gt : (1 : ℝ) < ∑ t ∈ T, t :=
      sum_gt_one_of_card_ge hn T hTgt (le_of_eq hTcard.symm)
    have hsum_pos : 0 < ∑ t ∈ T, t := by linarith
    have habs : |∑ t ∈ T, t| = ∑ t ∈ T, t := abs_of_pos hsum_pos
    have := hS T hTS
    rw [habs] at this
    linarith
  have hSnneg_fin : ∀ n : ℕ, 1 ≤ n → (S ∩ Set.Iio (-(1 / n) : ℝ)).Finite := by
    intro n hn
    by_contra hinf
    rw [Set.not_finite] at hinf
    obtain ⟨T, hTsub, hTcard⟩ := hinf.exists_subset_card_eq n
    have hTS : ↑T ⊆ S := by
      intro x hx; exact (hTsub hx).1
    have hTlt : ∀ x ∈ T, x < -(1 / n : ℝ) := by
      intro x hx; exact (hTsub hx).2
    have hsum_lt : (∑ t ∈ T, t) < -1 :=
      sum_lt_neg_one_of_card_ge hn T hTlt (le_of_eq hTcard.symm)
    have hsum_neg : (∑ t ∈ T, t) < 0 := by linarith
    have habs : |∑ t ∈ T, t| = -(∑ t ∈ T, t) := abs_of_neg hsum_neg
    have := hS T hTS
    rw [habs] at this
    linarith
  -- S ⊆ {0} ∪ ⋃ n, (Sₙ ∪ S_{-n})
  have hcover : S ⊆ {0} ∪ ⋃ n : {n : ℕ // 1 ≤ n},
      (S ∩ Set.Ioi (1 / (n : ℕ) : ℝ)) ∪ (S ∩ Set.Iio (-(1 / (n : ℕ) : ℝ))) := by
    intro x hx
    by_cases hx0 : x = 0
    · left; exact hx0
    · right
      rcases lt_or_gt_of_ne hx0 with hneg | hpos
      · -- x < 0, find n with 1/n < -x, i.e., -x > 1/n
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < -x by linarith)
        refine Set.mem_iUnion.mpr ⟨⟨n + 1, by omega⟩, ?_⟩
        right
        refine ⟨hx, ?_⟩
        simp only [Set.mem_Iio]
        have h1 : (1 : ℝ) / (↑(n + 1) : ℕ) < -x := by
          have : (1 : ℝ) / (n + 1) < -x := hn
          convert this using 2
          push_cast; ring
        linarith
      · -- x > 0
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
        refine Set.mem_iUnion.mpr ⟨⟨n + 1, by omega⟩, ?_⟩
        left
        refine ⟨hx, ?_⟩
        simp only [Set.mem_Ioi]
        have h1 : (1 : ℝ) / (↑(n + 1) : ℕ) < x := by
          have : (1 : ℝ) / (n + 1) < x := hn
          convert this using 2
          push_cast; ring
        exact h1
  apply Set.Countable.mono hcover
  apply Set.Countable.union
  · exact Set.countable_singleton 0
  · apply Set.countable_iUnion
    intro n
    apply Set.Countable.union
    · exact (hSn_fin n.1 n.2).countable
    · exact (hSnneg_fin n.1 n.2).countable


end Imc2004P1
