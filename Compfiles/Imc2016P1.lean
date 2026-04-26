/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2016, Problem 1

Let `f : [a, b] → ℝ` be continuous on `[a,b]` and differentiable on `(a,b)`.
Suppose that `f` has infinitely many zeros, but there is no `x ∈ (a,b)` with
`f(x) = f'(x) = 0`. Prove that `f(a) * f(b) = 0`.
-/

namespace Imc2016P1

open Set Filter Topology

problem imc2016_p1 (a b : ℝ) (f : ℝ → ℝ)
    (hcont : ContinuousOn f (Icc a b))
    (hdiff : DifferentiableOn ℝ f (Ioo a b))
    (hzeros : {x ∈ Icc a b | f x = 0}.Infinite)
    (hno_double : ∀ x ∈ Ioo a b, ¬ (f x = 0 ∧ deriv f x = 0)) :
    f a * f b = 0 := by
  -- Let S be the zero set of f in [a,b]; it is infinite and contained in the
  -- compact set [a,b], so it has an accumulation point c ∈ [a,b].
  set S : Set ℝ := {x ∈ Icc a b | f x = 0} with hS_def
  have hS_sub : S ⊆ Icc a b := fun x hx => hx.1
  obtain ⟨c, hc_mem, hc_acc⟩ :=
    hzeros.exists_accPt_of_subset_isCompact isCompact_Icc hS_sub
  -- `f` is frequently zero near `c` along `𝓝[≠] c`.
  have hfreq : ∃ᶠ y in 𝓝[≠] c, f y = 0 := by
    have h := accPt_iff_frequently.mp hc_acc
    rw [Filter.frequently_iff] at h ⊢
    intro U hU
    -- 𝓝[≠] c basis: take U ∈ 𝓝[≠] c, extend to W ∈ 𝓝 c with W ∩ {y ≠ c} ⊆ U.
    rw [mem_nhdsWithin] at hU
    obtain ⟨W, hWopen, hcW, hWU⟩ := hU
    obtain ⟨y, hyW, hyne, hyS⟩ := h (hWopen.mem_nhds hcW)
    refine ⟨y, hWU ⟨hyW, ?_⟩, hyS.2⟩
    exact hyne
  -- Case: c is in the interior (a, b).
  by_cases hc_int : c ∈ Ioo a b
  · exfalso
    -- From `hfreq`, `deriv f c = 0`.
    have hderiv : deriv f c = 0 :=
      deriv_zero_of_frequently_const (c := (0 : ℝ)) (by
        -- The filter 𝓝[≠] c equals 𝓝[univ \ {c}] c = 𝓝[univ \ {c}] c.
        simpa using hfreq)
    -- Also, from continuity, f c = 0.
    have hfc : f c = 0 := by
      have hcts : ContinuousWithinAt f (Icc a b) c := hcont c hc_mem
      -- Since f is zero frequently in 𝓝[≠] c, and c ∈ Icc a b, the limit f c = 0.
      have : f c ∈ closure ({(0 : ℝ)} : Set ℝ) := by
        have hdcc : DifferentiableAt ℝ f c :=
          hdiff.differentiableAt (IsOpen.mem_nhds isOpen_Ioo hc_int)
        have hcts_at : ContinuousAt f c := hdcc.continuousAt
        have htend : Tendsto f (𝓝[≠] c) (𝓝 (f c)) :=
          hcts_at.tendsto.mono_left inf_le_left
        refine mem_closure_of_frequently_of_tendsto
          (s := ({(0 : ℝ)} : Set ℝ)) ?_ htend
        exact hfreq.mono (fun _ h => by simpa using h)
      rw [closure_singleton] at this
      exact this
    exact hno_double c hc_int ⟨hfc, hderiv⟩
  -- Case: c is not in the interior. So c = a or c = b.
  · rw [mem_Ioo, not_and_or] at hc_int
    have hca : c = a ∨ c = b := by
      rcases hc_int with h1 | h1
      · left
        have h2 : c ≥ a := hc_mem.1
        linarith [not_lt.mp h1]
      · right
        have h2 : c ≤ b := hc_mem.2
        linarith [not_lt.mp h1]
    -- In either case, f c = 0 (we show directly from continuity).
    -- Actually we only need that the corresponding endpoint is a zero.
    have hfc : f c = 0 := by
      have hcts : ContinuousWithinAt f (Icc a b) c := hcont c hc_mem
      have : f c ∈ closure ({(0 : ℝ)} : Set ℝ) := by
        have hfreq_Icc : ∃ᶠ y in 𝓝[Icc a b \ {c}] c, f y = 0 := by
          have h := accPt_iff_frequently.mp hc_acc
          rw [Filter.frequently_iff] at h ⊢
          intro U hU
          rw [mem_nhdsWithin] at hU
          obtain ⟨W, hWopen, hcW, hWU⟩ := hU
          obtain ⟨y, hyW, hyne, hyS⟩ := h (hWopen.mem_nhds hcW)
          refine ⟨y, hWU ⟨hyW, ?_⟩, hyS.2⟩
          exact ⟨hyS.1, hyne⟩
        have hmono : 𝓝[Icc a b \ {c}] c ≤ 𝓝[Icc a b] c := nhdsWithin_mono _ diff_subset
        have htend : Tendsto f (𝓝[Icc a b \ {c}] c) (𝓝 (f c)) :=
          hcts.tendsto.mono_left hmono
        refine mem_closure_of_frequently_of_tendsto
          (s := ({(0 : ℝ)} : Set ℝ)) ?_ htend
        exact hfreq_Icc.mono (fun _ h => by simpa using h)
      rw [closure_singleton] at this
      exact this
    -- So f c = 0. Since c = a or c = b, conclude.
    rcases hca with hca | hca
    · rw [hca] at hfc
      rw [hfc, zero_mul]
    · rw [hca] at hfc
      rw [hfc, mul_zero]

end Imc2016P1
