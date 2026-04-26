/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.Analysis.ODE.Gronwall

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1994, Problem 7

Let `f ∈ C¹[a,b]` with `f(a) = 0`, and let `λ > 0` be such that
`|f'(x)| ≤ λ |f(x)|` on `[a,b]`. Then `f(x) = 0` on `[a,b]`.

## Proof outline

This is a special case of the Grönwall uniqueness theorem
`eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right` already in Mathlib:
the conditions `f a = 0` and `‖f' x‖ ≤ K * ‖f x‖` on `[a, b)` force
`f ≡ 0` on `[a, b]`. The classical hand-written proof considers the
supremum `M = sup_{[a, a+h]} |f|` for `λ h < 1`; integrating
`|f' | ≤ λ |f|` from `a` gives `M ≤ λ h M`, so `M = 0`, and one
iterates to cover `[a, b]`. Mathlib's `gronwallBound` argument
encapsulates exactly this.
-/

namespace Imc1994P7

open Set

problem imc1994_p7 (f f' : ℝ → ℝ) (a b lam : ℝ) (hlam : 0 < lam)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (ha : f a = 0)
    (bound : ∀ x ∈ Icc a b, |f' x| ≤ lam * |f x|) :
    ∀ x ∈ Icc a b, f x = 0 := by
  have _ := hlam
  -- Reduce to the form expected by Mathlib's Grönwall uniqueness lemma.
  have bound' : ∀ x ∈ Ico a b, ‖f' x‖ ≤ lam * ‖f x‖ := by
    intro x hx
    have hxIcc : x ∈ Icc a b := Ico_subset_Icc_self hx
    have h := bound x hxIcc
    simpa [Real.norm_eq_abs] using h
  exact eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hf hf' ha bound'

end Imc1994P7
