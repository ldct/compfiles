/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2025, Problem 6

Let `f : (0, ∞) → ℝ` be a continuously differentiable function, and let
`b > a > 0` be real numbers such that `f(a) = f(b) = k`. Prove that there
exists a point `ξ ∈ (a, b)` such that

  `f(ξ) − ξ f'(ξ) = k`.
-/

namespace Imc2025P6

problem imc2025_p6 (f : ℝ → ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0))
    (a b k : ℝ) (ha : 0 < a) (hab : a < b)
    (hfa : f a = k) (hfb : f b = k) :
    ∃ ξ ∈ Set.Ioo a b, f ξ - ξ * deriv f ξ = k := by
  -- TODO: Apply Cauchy's mean value theorem to g(x) = f(x)/x and h(x) = 1/x
  -- on [a, b]. We get ξ ∈ (a, b) such that
  --   (g(a) - g(b)) / (h(a) - h(b)) = g'(ξ) / h'(ξ).
  -- The LHS equals (f(a)/a - f(b)/b) / (1/a - 1/b) = k (using f(a)=f(b)=k).
  -- The RHS equals ((ξ f'(ξ) - f(ξ))/ξ²) / (-1/ξ²) = f(ξ) - ξ f'(ξ).
  sorry

end Imc2025P6
