/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2000, Problem 1

Is it true that if `f : [0,1] → [0,1]` is monotone increasing, then
there exists `x ∈ [0,1]` with `f x = x`?

Answer: Yes. (No continuity required.)
-/

namespace Imc2000P1

problem imc2000_p1
    (f : ℝ → ℝ)
    (hmono : Monotone f)
    (hmaps : ∀ x, x ∈ Set.Icc (0 : ℝ) 1 → f x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, f x = x := by
  -- Let A = { x ∈ [0,1] | x ≤ f x }. Then 0 ∈ A, and A is bounded above by 1.
  -- Set a = sup A. We show f a = a.
  set A : Set ℝ := {x | x ∈ Set.Icc (0 : ℝ) 1 ∧ x ≤ f x} with hAdef
  have h0A : (0 : ℝ) ∈ A := by
    refine ⟨?_, ?_⟩
    · exact ⟨le_refl _, by norm_num⟩
    · exact (hmaps 0 ⟨le_refl _, by norm_num⟩).1
  have hAne : A.Nonempty := ⟨0, h0A⟩
  have hAbdd : BddAbove A := ⟨1, fun x hx => hx.1.2⟩
  set a := sSup A with hadef
  have ha_ge : 0 ≤ a := le_csSup hAbdd h0A
  have ha_le : a ≤ 1 := csSup_le hAne (fun x hx => hx.1.2)
  have ha_Icc : a ∈ Set.Icc (0 : ℝ) 1 := ⟨ha_ge, ha_le⟩
  have hfa_Icc : f a ∈ Set.Icc (0 : ℝ) 1 := hmaps a ha_Icc
  -- Goal: f a = a.
  refine ⟨a, ha_Icc, ?_⟩
  -- Rule out both a < f a and f a < a.
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- Case f a < a. Since a = sup A, there exists c ∈ A with f a < c ≤ a.
    -- Then f c ≥ c > f a, but by monotonicity f c ≤ f a. Contradiction.
    have hcsup : ∃ c ∈ A, f a < c := by
      by_contra hnot
      push Not at hnot
      -- Then f a is an upper bound for A, so a ≤ f a.
      have : a ≤ f a := csSup_le hAne hnot
      linarith
    obtain ⟨c, hcA, hcgt⟩ := hcsup
    have hc_le_a : c ≤ a := le_csSup hAbdd hcA
    have hfc_ge_c : c ≤ f c := hcA.2
    have hfc_le_fa : f c ≤ f a := hmono hc_le_a
    linarith
  · -- Case a < f a. Then f a ∈ A, so f a ≤ a. Contradiction.
    -- We show f a ∈ A: f a ∈ [0,1], and by monotonicity f (f a) ≥ f a.
    have hfa_in_A : f a ∈ A := by
      refine ⟨hfa_Icc, ?_⟩
      -- Need f a ≤ f (f a). By monotonicity since a ≤ f a.
      exact hmono (le_of_lt hgt)
    have : f a ≤ a := le_csSup hAbdd hfa_in_A
    linarith

end Imc2000P1
