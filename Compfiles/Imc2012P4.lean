/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2012, Problem 4 (Day 1, Problem 4)

Let `f : ℝ → ℝ` be a continuously differentiable function satisfying
`f'(t) > f(f(t))` for all `t ∈ ℝ`. Prove that `f(f(f(t))) ≤ 0` for all `t ≥ 0`.
-/

namespace Imc2012P4

problem imc2012_p4
    (f f' : ℝ → ℝ)
    (hdiff : ∀ x, HasDerivAt f (f' x) x)
    (_hcont : Continuous f')
    (hineq : ∀ t, f (f t) < f' t) :
    ∀ t ≥ (0 : ℝ), f (f (f t)) ≤ 0 := by
  -- TODO: full proof.  The official IMC 2012 solution proceeds in three steps:
  --
  --   Lemma 1:  `limsup_{t → ∞} f t ≠ +∞`.  (Otherwise `f' > f(f) > 2`
  --             eventually, so `f(t) > t`, giving `f' > f`, hence `f` grows
  --             at least exponentially; then integrating `f' e^{-f} > c > 0`
  --             yields a contradiction since the LHS integrates to a bounded
  --             quantity and the RHS to `+∞`.)
  --
  --   Lemma 2:  `f t < t` for all `t > 0`.  (If `f t₀ = t₀ > 0`, then either
  --             some `t ≥ t₀` has `f t < t₀`, giving a contradiction at the
  --             infimum, or `f ≥ t₀` on `[t₀, ∞)`, forcing `f' ≥ t₀` and
  --             `f → ∞`, contradicting Lemma 1.)
  --
  --   Lemma 3:  If `s₁ ≤ 0` and `f s₁ > 0`, then `f s > s₁` for `s > s₁`.
  --
  -- Assuming the contrary `f(f(f t₀)) > 0`, set `t₁ = f t₀`, `t₂ = f t₁`,
  -- `t₃ = f t₂ > 0`.  Using the lemmas one shows `0 < t₃ < t₂ < t₁ < t₀`,
  -- and then for `t > t₀`, `f' t > f(f t) > t₂ > 0`, so `f → ∞`,
  -- contradicting Lemma 1.
  sorry

end Imc2012P4
