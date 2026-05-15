/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2004, Problem 9
(IMC 2004, Day 2, Problem 3)

Let `D` be the closed unit disk in the complex plane, and let `p₁, …, pₙ ∈ D`.
Show that there exists a point `p ∈ D` such that
`∑ |p - pᵢ| ≥ n`.
-/

namespace Imc2004P9

open Complex

snip begin

/-
Take `s = ∑ pᵢ`.  If `s = 0`, any unit vector works.  Otherwise take
`p = -s / |s|`; then `|p| = 1` and, by the triangle inequality,
`∑ |p - pᵢ| ≥ |n p - s| = |(-n - |s|) · (s / |s|)| = n + |s| ≥ n`.
-/

snip end

problem imc2004_p9 (n : ℕ) (p : Fin n → ℂ) (_hp : ∀ i, ‖p i‖ ≤ 1) :
    ∃ q : ℂ, ‖q‖ ≤ 1 ∧ (n : ℝ) ≤ ∑ i, ‖q - p i‖ := by
  set s : ℂ := ∑ i, p i with hs_def
  -- Choose q depending on whether s is zero.
  by_cases hs : s = 0
  · -- Any unit vector works; pick q = 1.
    refine ⟨1, by simp, ?_⟩
    -- By the triangle inequality, ∑ ‖1 - p i‖ ≥ ‖∑ (1 - p i)‖ = ‖n - s‖ = n.
    have htri : ‖∑ i, ((1 : ℂ) - p i)‖ ≤ ∑ i, ‖(1 : ℂ) - p i‖ := norm_sum_le _ _
    have hsum : ∑ i, ((1 : ℂ) - p i) = (n : ℂ) - s := by
      rw [Finset.sum_sub_distrib]
      simp [hs_def]
    rw [hsum, hs, sub_zero] at htri
    have hn : ‖(n : ℂ)‖ = n := by
      rw [Complex.norm_natCast]
    rw [hn] at htri
    exact htri
  · -- Take q = -s / ‖s‖.
    have hs_norm_pos : 0 < ‖s‖ := norm_pos_iff.mpr hs
    have hs_norm_ne : ‖s‖ ≠ 0 := ne_of_gt hs_norm_pos
    refine ⟨-s / (‖s‖ : ℂ), ?_, ?_⟩
    · -- ‖-s / ‖s‖‖ = 1 ≤ 1
      rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hs_norm_pos, div_self hs_norm_ne]
    · -- Triangle inequality ∑ ‖q - p i‖ ≥ ‖∑ (q - p i)‖ = ‖n q - s‖.
      set q : ℂ := -s / (‖s‖ : ℂ) with hq_def
      have htri : ‖∑ i, (q - p i)‖ ≤ ∑ i, ‖q - p i‖ := norm_sum_le _ _
      have hsum : ∑ i, (q - p i) = (n : ℂ) * q - s := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp [hs_def]
      -- Compute ‖n q - s‖ = n + ‖s‖.
      have hnq : (n : ℂ) * q - s = -(s / (‖s‖ : ℂ)) * (((n : ℝ) + ‖s‖ : ℝ) : ℂ) := by
        rw [hq_def]
        have hc : ((‖s‖ : ℝ) : ℂ) ≠ 0 := by
          rw [Ne, Complex.ofReal_eq_zero]; exact hs_norm_ne
        push_cast
        field_simp
        ring
      have hnorm_nq : ‖(n : ℂ) * q - s‖ = (n : ℝ) + ‖s‖ := by
        rw [hnq, norm_mul, norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hs_norm_pos, div_self hs_norm_ne, one_mul,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [hsum, hnorm_nq] at htri
      have h1 : (n : ℝ) ≤ (n : ℝ) + ‖s‖ := by
        have : (0 : ℝ) ≤ ‖s‖ := norm_nonneg _
        linarith
      exact le_trans h1 htri

end Imc2004P9
