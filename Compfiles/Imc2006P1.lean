/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2006, Problem 1

Prove or disprove the following implications for `f : ℝ → ℝ`:

(a) `f` continuous with range `ℝ` ⇒ `f` monotonic.
(b) `f` monotonic with range `ℝ` ⇒ `f` continuous.
(c) `f` monotonic and continuous ⇒ `f` has range `ℝ`.

Answers: (a) False. (b) True. (c) False.
-/

namespace Imc2006P1

/-- Answer to part (a): continuity + surjectivity does NOT imply monotonicity. -/
determine answerA : Prop := False

/-- Answer to part (b): monotonicity + surjectivity DOES imply continuity. -/
determine answerB : Prop := True

/-- Answer to part (c): monotonicity + continuity does NOT imply surjectivity. -/
determine answerC : Prop := False

snip begin

/-- The polynomial `x ↦ x^3 - x` is surjective on ℝ. -/
lemma cube_sub_self_surjective :
    Function.Surjective (fun x : ℝ => x^3 - x) := by
  intro y
  -- `x ↦ x^3 - x` is continuous and tends to ±∞ at ±∞, so by IVT it is surjective.
  have hcont : Continuous (fun x : ℝ => x^3 - x) := by fun_prop
  set a : ℝ := -(|y| + 2) with ha_def
  set b : ℝ := |y| + 2 with hb_def
  have h_abs_y : |y| ≥ y := le_abs_self y
  have h_abs_neg : |y| ≥ -y := neg_le_abs y
  have h_abs_nn : (0 : ℝ) ≤ |y| := abs_nonneg y
  have h_b_ge_2 : b ≥ 2 := by show |y| + 2 ≥ 2; linarith
  have h_b_cube : b^3 ≥ 4 * b := by
    have : b^2 ≥ 4 := by nlinarith
    nlinarith
  have ha : a^3 - a ≤ y := by
    have heq : a^3 - a = -(b^3 - b) := by
      show (-(|y|+2))^3 - -(|y|+2) = -((|y|+2)^3 - (|y|+2))
      ring
    rw [heq]
    nlinarith
  have hb : y ≤ b^3 - b := by
    show y ≤ (|y|+2)^3 - (|y|+2)
    nlinarith
  have hab : a ≤ b := by
    show -(|y| + 2) ≤ |y| + 2
    linarith
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc hab hcont.continuousOn ⟨ha, hb⟩
  exact ⟨x, hx⟩

snip end

problem imc2006_p1 :
    -- Part (a)
    (answerA ↔
      ∀ (f : ℝ → ℝ), Continuous f → Function.Surjective f → Monotone f) ∧
    -- Part (b)
    (answerB ↔
      ∀ (f : ℝ → ℝ), Monotone f → Function.Surjective f → Continuous f) ∧
    -- Part (c)
    (answerC ↔
      ∀ (f : ℝ → ℝ), Monotone f → Continuous f → Function.Surjective f) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Part (a): False. Counterexample: f(x) = x^3 - x.
    show False ↔ _
    refine ⟨False.elim, ?_⟩
    intro H
    set f : ℝ → ℝ := fun x => x^3 - x with hf_def
    have hcont : Continuous f := by
      show Continuous (fun x : ℝ => x^3 - x); fun_prop
    have hsurj : Function.Surjective f := cube_sub_self_surjective
    have hmono : Monotone f := H f hcont hsurj
    -- f(0) = 0, f(1/2) = -3/8, so f is not monotone on [0, 1/2].
    have h1 : f 0 ≤ f (1/2) := hmono (by norm_num)
    have h2 : f 0 = 0 := by simp [f]
    have h3 : f (1/2) = -3/8 := by simp [f]; norm_num
    rw [h2, h3] at h1
    linarith
  · -- Part (b): True. Uses `Monotone.continuous_of_surjective`.
    show True ↔ _
    refine ⟨fun _ f hmono hsurj => ?_, fun _ => trivial⟩
    exact hmono.continuous_of_surjective hsurj
  · -- Part (c): False. Counterexample: f = arctan.
    show False ↔ _
    refine ⟨False.elim, ?_⟩
    intro H
    have hmono : Monotone Real.arctan := Real.arctan_strictMono.monotone
    have hcont : Continuous Real.arctan := Real.continuous_arctan
    have hsurj : Function.Surjective Real.arctan := H Real.arctan hmono hcont
    -- But arctan is bounded by π/2, so cannot be surjective.
    obtain ⟨x, hx⟩ := hsurj (Real.pi / 2)
    have hlt : Real.arctan x < Real.pi / 2 := Real.arctan_lt_pi_div_two x
    linarith

end Imc2006P1
