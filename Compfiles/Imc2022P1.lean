/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2022, Problem 1

Let `f : [0,1] → (0, ∞)` be an integrable function such that
`f(x) · f(1 - x) = 1` for all `x ∈ [0, 1]`. Prove that

  `∫_0^1 f(x) dx ≥ 1`.
-/

namespace Imc2022P1

open MeasureTheory intervalIntegral Set

snip begin

/-- AM-GM in the special case `a * b = 1`, `0 < a`, `0 < b`: `2 ≤ a + b`. -/
lemma two_le_add_of_mul_eq_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a * b = 1) :
    2 ≤ a + b := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1)]

snip end

problem imc2022_p1 (f : ℝ → ℝ)
    (hf_int : IntervalIntegrable f volume 0 1)
    (hf_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < f x)
    (hf_sym : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x * f (1 - x) = 1) :
    1 ≤ ∫ x in (0 : ℝ)..1, f x := by
  -- Step 1: Split the integral at 1/2.
  have h0half : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hhalf1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hf_int_left : IntervalIntegrable f volume 0 (1 / 2) :=
    hf_int.mono_set (by rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1),
                             uIcc_of_le h0half]; exact Icc_subset_Icc_right hhalf1)
  have hf_int_right : IntervalIntegrable f volume (1 / 2) 1 :=
    hf_int.mono_set (by rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1),
                             uIcc_of_le hhalf1]; exact Icc_subset_Icc_left h0half)
  have hsplit : (∫ x in (0 : ℝ)..1, f x) =
      (∫ x in (0 : ℝ)..(1/2), f x) + (∫ x in (1/2 : ℝ)..1, f x) :=
    (integral_add_adjacent_intervals hf_int_left hf_int_right).symm
  -- Step 2: Rewrite the second integral using the substitution x ↦ 1 - x.
  -- `∫ x in 0..(1/2), f (1-x) = ∫ x in 1/2..1, f x`.
  have hsub : (∫ x in (0 : ℝ)..(1/2), f (1 - x)) = ∫ x in (1/2 : ℝ)..1, f x := by
    have h := integral_comp_sub_left f (a := 0) (b := 1/2) 1
    -- h : ∫ x in 0..1/2, f(1 - x) = ∫ x in 1 - 1/2..1 - 0, f x
    rw [h]; norm_num
  -- Step 3: Combine: ∫₀¹ f = ∫₀^{1/2} (f(x) + f(1-x)).
  have hf_int_right' : IntervalIntegrable f volume (1 - 1/2) (1 - 0) := by
    have : (1 - 1/2 : ℝ) = 1/2 := by norm_num
    rw [this]; simpa using hf_int_right
  have hg_int : IntervalIntegrable (fun x => f (1 - x)) volume 0 (1/2) := by
    have := hf_int_right'.comp_sub_left 1
    -- this : IntervalIntegrable (fun x => f (1 - x)) volume (1 - (1 - 0)) (1 - (1 - 1/2))
    have heq1 : (1 - (1 - 0) : ℝ) = 0 := by norm_num
    have heq2 : (1 - (1 - 1/2) : ℝ) = 1/2 := by norm_num
    rw [heq1, heq2] at this
    exact this.symm
  have hsum : (∫ x in (0 : ℝ)..1, f x) = ∫ x in (0 : ℝ)..(1/2), (f x + f (1 - x)) := by
    rw [hsplit, ← hsub, integral_add hf_int_left hg_int]
  -- Step 4: Pointwise bound: for x ∈ [0, 1/2], f(x) + f(1-x) ≥ 2.
  have hbound : ∀ x ∈ Set.Icc (0:ℝ) (1/2), 2 ≤ f x + f (1 - x) := by
    intro x hx
    simp only [Set.mem_Icc] at hx
    have hx' : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx.1, le_trans hx.2 hhalf1⟩
    have h1x' : 1 - x ∈ Set.Icc (0:ℝ) 1 :=
      ⟨by linarith, by linarith⟩
    exact two_le_add_of_mul_eq_one (hf_pos x hx') (hf_pos (1 - x) h1x') (hf_sym x hx')
  -- Step 5: Integrate the bound.
  have hconst_le :
      (∫ x in (0:ℝ)..(1/2), (2 : ℝ)) ≤ ∫ x in (0:ℝ)..(1/2), (f x + f (1 - x)) := by
    apply intervalIntegral.integral_mono_on h0half
    · exact intervalIntegrable_const
    · exact hf_int_left.add hg_int
    · exact hbound
  have hconst_eval : (∫ _ in (0:ℝ)..(1/2), (2 : ℝ)) = 1 := by
    rw [intervalIntegral.integral_const]; norm_num
  linarith [hsum ▸ hconst_le, hconst_eval]

end Imc2022P1
