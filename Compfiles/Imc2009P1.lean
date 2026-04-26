/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2009, Problem 1

Suppose that `f, g : ℝ → ℝ` satisfy `f r ≤ g r` for every rational `r`.

(a) Does `f x ≤ g x` for every real `x` if `f` and `g` are both non-decreasing?
(b) Does `f x ≤ g x` for every real `x` if `f` and `g` are both continuous?

Answers: (a) No. (b) Yes.
-/

namespace Imc2009P1

/-- Answer to part (a): the implication does NOT hold in general for
non-decreasing functions. -/
determine answerA : Prop := False

/-- Answer to part (b): the implication DOES hold for continuous functions. -/
determine answerB : Prop := True

snip begin

/-- The indicator of `[c, ∞)` is non-decreasing. -/
lemma monotone_indicator_Ici (c : ℝ) :
    Monotone (fun x : ℝ => if c ≤ x then (1 : ℝ) else 0) := by
  intro a b hab
  by_cases ha : c ≤ a
  · have hb : c ≤ b := le_trans ha hab
    simp [ha, hb]
  · by_cases hb : c ≤ b
    · simp [ha, hb]
    · simp [ha, hb]

/-- The indicator of `(c, ∞)` is non-decreasing. -/
lemma monotone_indicator_Ioi (c : ℝ) :
    Monotone (fun x : ℝ => if c < x then (1 : ℝ) else 0) := by
  intro a b hab
  by_cases ha : c < a
  · have hb : c < b := lt_of_lt_of_le ha hab
    simp [ha, hb]
  · by_cases hb : c < b
    · simp [ha, hb]
    · simp [ha, hb]

snip end

problem imc2009_p1 :
    -- Part (a): For non-decreasing f, g with f ≤ g on ℚ, does f ≤ g on ℝ?
    (answerA ↔
      ∀ (f g : ℝ → ℝ), Monotone f → Monotone g →
        (∀ r : ℚ, f (r : ℝ) ≤ g (r : ℝ)) →
        ∀ x : ℝ, f x ≤ g x) ∧
    -- Part (b): For continuous f, g with f ≤ g on ℚ, does f ≤ g on ℝ?
    (answerB ↔
      ∀ (f g : ℝ → ℝ), Continuous f → Continuous g →
        (∀ r : ℚ, f (r : ℝ) ≤ g (r : ℝ)) →
        ∀ x : ℝ, f x ≤ g x) := by
  refine ⟨?_, ?_⟩
  · -- Part (a): answer is False. Counterexample:
    -- f = indicator of [√3, ∞), g = indicator of (√3, ∞).
    show False ↔ _
    refine ⟨False.elim, ?_⟩
    intro H
    set c : ℝ := Real.sqrt 3 with hc_def
    set f : ℝ → ℝ := fun x => if c ≤ x then 1 else 0 with hf_def
    set g : ℝ → ℝ := fun x => if c < x then 1 else 0 with hg_def
    have hc_irr : Irrational c := by
      have : Irrational (Real.sqrt ((3 : ℕ) : ℝ)) :=
        Nat.Prime.irrational_sqrt (p := 3) (by decide)
      simpa using this
    have hmono_f : Monotone f := monotone_indicator_Ici c
    have hmono_g : Monotone g := monotone_indicator_Ioi c
    -- For every rational r, f r = g r (both 0 or both 1), so f r ≤ g r.
    have hrat : ∀ r : ℚ, f (r : ℝ) ≤ g (r : ℝ) := by
      intro r
      -- Since c is irrational, c ≠ r, so c < r ↔ c ≤ r.
      have hne : c ≠ (r : ℝ) := by
        intro heq
        exact hc_irr ⟨r, heq.symm⟩
      show (if c ≤ (r : ℝ) then (1 : ℝ) else 0) ≤ (if c < (r : ℝ) then (1 : ℝ) else 0)
      by_cases hlt : c < (r : ℝ)
      · have hle : c ≤ (r : ℝ) := hlt.le
        simp [hlt, hle]
      · have hnle : ¬ c ≤ (r : ℝ) := by
          intro hle
          rcases lt_or_eq_of_le hle with hlt' | heq
          · exact hlt hlt'
          · exact hne heq
        simp [hlt, hnle]
    -- Apply H at x = c. f c = 1, g c = 0.
    have hkey := H f g hmono_f hmono_g hrat c
    have hfc : f c = 1 := by show (if c ≤ c then (1 : ℝ) else 0) = 1; simp
    have hgc : g c = 0 := by show (if c < c then (1 : ℝ) else 0) = 0; simp
    rw [hfc, hgc] at hkey
    linarith
  · -- Part (b): answer is True. Proof via density of ℚ in ℝ.
    show True ↔ _
    refine ⟨fun _ => ?_, fun _ => trivial⟩
    intro f g hf hg hrat x
    -- g - f is continuous and ≥ 0 on ℚ; ℚ dense in ℝ, so g - f ≥ 0 everywhere.
    -- Use DenseRange.induction_on with the closed property {y | f y ≤ g y}.
    have hclosed : IsClosed { y : ℝ | f y ≤ g y } :=
      isClosed_le hf hg
    exact Rat.denseRange_cast.induction_on x hclosed hrat

end Imc2009P1
