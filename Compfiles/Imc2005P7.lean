/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2005, Problem 7
(Second day, Problem 1)

Let `f(x) = x^2 + b*x + c` and let `M = {x : ℝ | |f x| < 1}`. Prove that the
Lebesgue measure of `M` is at most `2 * √2`.
-/

namespace Imc2005P7

open MeasureTheory Set

snip begin

/-- For nonneg reals `u, v` with `u^2 = v^2 + 2`, we have `u ≤ v + √2`. -/
lemma sub_sqrt_bound {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u ^ 2 = v ^ 2 + 2) :
    u ≤ v + Real.sqrt 2 := by
  have hs : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hs2 : Real.sqrt 2 ^ 2 = 2 := by
    rw [sq]; exact Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hvs : 0 ≤ v + Real.sqrt 2 := add_nonneg hv hs
  have h : u ^ 2 ≤ (v + Real.sqrt 2) ^ 2 := by
    have hexp : (v + Real.sqrt 2) ^ 2 = v ^ 2 + 2 * v * Real.sqrt 2 + 2 := by
      rw [add_pow_two, hs2]
    rw [huv, hexp]
    have : 0 ≤ 2 * v * Real.sqrt 2 := by positivity
    linarith
  -- from u^2 ≤ (v + √2)^2 and both sides nonneg, conclude u ≤ v + √2.
  have habs : |u| ≤ v + Real.sqrt 2 := abs_le_of_sq_le_sq h hvs
  rw [abs_of_nonneg hu] at habs
  exact habs

snip end

problem imc2005_p7 (b c : ℝ) :
    volume {x : ℝ | |x ^ 2 + b * x + c| < 1} ≤ ENNReal.ofReal (2 * Real.sqrt 2) := by
  -- Let `m = -b/2` and `d = c - b^2/4` so that `x^2 + b*x + c = (x - m)^2 + d`.
  set m : ℝ := -b / 2 with hm_def
  set d : ℝ := c - b ^ 2 / 4 with hd_def
  -- Rewrite the condition.
  have hf_eq : ∀ x : ℝ, x ^ 2 + b * x + c = (x - m) ^ 2 + d := by
    intro x
    simp only [hm_def, hd_def]
    ring
  -- √2 nonneg.
  have hsqrt2_nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt2_sq : Real.sqrt 2 ^ 2 = 2 := by
    rw [sq]; exact Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  -- Split into three cases on d.
  by_cases hd1 : 1 ≤ d
  · -- Case d ≥ 1: the set is empty.
    have hempty : {x : ℝ | |x ^ 2 + b * x + c| < 1} = ∅ := by
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
      rw [hf_eq x, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (x - m) ^ 2 + d)]
      have : (0 : ℝ) ≤ (x - m) ^ 2 := sq_nonneg _
      linarith
    rw [hempty]
    simp
  · by_cases hd2 : -1 < d
    · -- Case -1 < d < 1: the set is an interval Ioo (m - √(1-d)) (m + √(1-d)).
      have hd1' : d < 1 := lt_of_not_ge hd1
      have h1d_pos : 0 < 1 - d := by linarith
      set r : ℝ := Real.sqrt (1 - d) with hr_def
      have hr_nn : 0 ≤ r := Real.sqrt_nonneg _
      have hr_sq : r ^ 2 = 1 - d := by
        rw [hr_def, sq]; exact Real.mul_self_sqrt h1d_pos.le
      have hr_lt : r < Real.sqrt 2 := by
        rw [hr_def]
        exact Real.sqrt_lt_sqrt h1d_pos.le (by linarith)
      have hset_eq : {x : ℝ | |x ^ 2 + b * x + c| < 1} = Ioo (m - r) (m + r) := by
        ext x
        simp only [mem_setOf_eq, mem_Ioo]
        rw [hf_eq x, abs_lt]
        constructor
        · rintro ⟨hlo, hhi⟩
          have hsq : (x - m) ^ 2 < r ^ 2 := by rw [hr_sq]; linarith
          have habs : |x - m| < r := abs_lt_of_sq_lt_sq hsq hr_nn
          rw [abs_lt] at habs
          constructor <;> linarith
        · rintro ⟨hlo, hhi⟩
          have h_neg : -r < x - m := by linarith
          have h_pos : x - m < r := by linarith
          have hsq : (x - m) ^ 2 < r ^ 2 := sq_lt_sq' h_neg h_pos
          rw [hr_sq] at hsq
          refine ⟨?_, ?_⟩
          · have : (0 : ℝ) ≤ (x - m) ^ 2 := sq_nonneg _
            linarith
          · linarith
      rw [hset_eq, Real.volume_Ioo]
      have hlen : (m + r) - (m - r) = 2 * r := by ring
      rw [hlen]
      apply ENNReal.ofReal_le_ofReal
      linarith
    · -- Case d ≤ -1: the set is contained in a union of two intervals.
      have hd2' : d ≤ -1 := le_of_not_gt hd2
      have h1d_ge2 : 2 ≤ 1 - d := by linarith
      have h_1d_nn : 0 ≤ -1 - d := by linarith
      set u : ℝ := Real.sqrt (1 - d) with hu_def
      set v : ℝ := Real.sqrt (-1 - d) with hv_def
      have hu_nn : 0 ≤ u := Real.sqrt_nonneg _
      have hv_nn : 0 ≤ v := Real.sqrt_nonneg _
      have hu_sq : u ^ 2 = 1 - d := by
        rw [hu_def, sq]; exact Real.mul_self_sqrt (by linarith)
      have hv_sq : v ^ 2 = -1 - d := by
        rw [hv_def, sq]; exact Real.mul_self_sqrt h_1d_nn
      have huv_rel : u ^ 2 = v ^ 2 + 2 := by rw [hu_sq, hv_sq]; ring
      have hvu : v ≤ u := by
        have hsq_le : v ^ 2 ≤ u ^ 2 := by rw [huv_rel]; linarith
        have habs_le : |v| ≤ u := abs_le_of_sq_le_sq hsq_le hu_nn
        rw [abs_of_nonneg hv_nn] at habs_le
        exact habs_le
      have hbound : u ≤ v + Real.sqrt 2 := sub_sqrt_bound hu_nn hv_nn huv_rel
      -- The set: x s.t. -1 < (x-m)^2 + d < 1, i.e. v^2 < (x-m)^2 < u^2.
      -- This means v < |x - m| < u.
      have hsub : {x : ℝ | |x ^ 2 + b * x + c| < 1} ⊆
          Ioo (m - u) (m - v) ∪ Ioo (m + v) (m + u) := by
        intro x hx
        simp only [mem_setOf_eq] at hx
        rw [hf_eq x, abs_lt] at hx
        obtain ⟨hlo, hhi⟩ := hx
        have hsq_lo : v ^ 2 < (x - m) ^ 2 := by rw [hv_sq]; linarith
        have hsq_hi : (x - m) ^ 2 < u ^ 2 := by rw [hu_sq]; linarith
        have hbslt : v < |x - m| := by
          have hx_nn : 0 ≤ |x - m| := abs_nonneg _
          have hsq' : v ^ 2 < |x - m| ^ 2 := by rw [sq_abs]; exact hsq_lo
          have h_abs_v : |v| < |x - m| := abs_lt_of_sq_lt_sq hsq' hx_nn
          rwa [abs_of_nonneg hv_nn] at h_abs_v
        have habslt : |x - m| < u := abs_lt_of_sq_lt_sq hsq_hi hu_nn
        rcases abs_lt.mp habslt with ⟨hxm_lo, hxm_hi⟩
        rcases lt_or_ge 0 (x - m) with hxm_pos | hxm_np
        · have hxm_gt : v < x - m := by
            rw [abs_of_pos hxm_pos] at hbslt
            exact hbslt
          right
          refine ⟨?_, ?_⟩ <;> linarith
        · have hxm_lt_negv : x - m < -v := by
            have habs_eq : |x - m| = -(x - m) := abs_of_nonpos hxm_np
            rw [habs_eq] at hbslt
            linarith
          left
          refine ⟨?_, ?_⟩ <;> linarith
      calc volume {x : ℝ | |x ^ 2 + b * x + c| < 1}
          ≤ volume (Ioo (m - u) (m - v) ∪ Ioo (m + v) (m + u)) :=
              measure_mono hsub
        _ ≤ volume (Ioo (m - u) (m - v)) + volume (Ioo (m + v) (m + u)) :=
              measure_union_le _ _
        _ = ENNReal.ofReal (u - v) + ENNReal.ofReal (u - v) := by
              rw [Real.volume_Ioo, Real.volume_Ioo]
              congr 1 <;> · congr 1; ring
        _ = ENNReal.ofReal (2 * (u - v)) := by
              rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
              congr 1; ring
        _ ≤ ENNReal.ofReal (2 * Real.sqrt 2) := by
              apply ENNReal.ofReal_le_ofReal
              have : u - v ≤ Real.sqrt 2 := by linarith
              linarith

end Imc2005P7
