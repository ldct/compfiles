/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2002, Problem 2

Does there exist a continuously differentiable `f : ℝ → ℝ`
with `f(x) > 0` and `f'(x) = f(f(x))` for all `x`?

Answer: No.
-/

namespace Imc2002P2

snip begin

/-- If `f` is differentiable on `ℝ` with derivative `f'`, and `f'(x) > 0` for all `x`,
then `f` is strictly monotone. -/
lemma strict_mono_of_deriv_pos {f f' : ℝ → ℝ}
    (hdiff : ∀ x, HasDerivAt f (f' x) x)
    (hpos : ∀ x, 0 < f' x) : StrictMono f := by
  apply strictMono_of_hasDerivAt_pos (f := f) (f' := f')
  · intro x; exact hdiff x
  · intro x; exact hpos x

snip end

problem imc2002_p2 :
    ¬ ∃ (f : ℝ → ℝ) (f' : ℝ → ℝ),
        (∀ x, HasDerivAt f (f' x) x) ∧
        Continuous f' ∧
        (∀ x, 0 < f x) ∧
        (∀ x, f' x = f (f x)) := by
  rintro ⟨f, f', hdiff, _hcont, hpos, hfeq⟩
  -- f' x = f (f x) > 0 for all x, so f is strictly increasing.
  have hf'_pos : ∀ x, 0 < f' x := fun x => by rw [hfeq x]; exact hpos _
  have hmono : StrictMono f := strict_mono_of_deriv_pos hdiff hf'_pos
  -- For all x, f' x = f (f x) > f 0, since f x > 0 and f strictly mono.
  have hf'_gt : ∀ x, f 0 < f' x := by
    intro x
    rw [hfeq x]
    exact hmono (hpos x)
  -- By MVT on [-1, 0]: there exists c ∈ (-1, 0) with f 0 - f (-1) = f' c * (0 - (-1)) = f' c.
  have h_mvt : ∃ c ∈ Set.Ioo (-1 : ℝ) 0, f 0 - f (-1) = f' c * (0 - (-1)) := by
    have hlt : (-1 : ℝ) < 0 := by norm_num
    have hfc : ContinuousOn f (Set.Icc (-1 : ℝ) 0) :=
      fun x _ => (hdiff x).continuousAt.continuousWithinAt
    have hff' : ∀ x ∈ Set.Ioo (-1 : ℝ) 0, HasDerivAt f (f' x) x :=
      fun x _ => hdiff x
    obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope f f' hlt hfc hff'
    refine ⟨c, hc, ?_⟩
    -- hceq : f' c = (f 0 - f (-1)) / (0 - (-1))
    have h01 : (0 : ℝ) - (-1) = 1 := by norm_num
    rw [h01] at hceq
    have : f 0 - f (-1) = f' c := by rw [hceq]; ring
    linarith
  obtain ⟨c, _hc_mem, hceq⟩ := h_mvt
  -- f' c > f 0, so f 0 - f (-1) > f 0, hence f (-1) < 0. Contradicts hpos.
  have h1 : f' c * (0 - (-1)) = f' c := by ring
  rw [h1] at hceq
  have h2 : f 0 < f 0 - f (-1) := by
    rw [hceq]; exact hf'_gt c
  have h3 : f (-1) < 0 := by linarith
  exact absurd h3 (not_lt.mpr (le_of_lt (hpos (-1))))

end Imc2002P2
