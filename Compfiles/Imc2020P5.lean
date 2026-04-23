/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2020, Problem 5

Find all twice continuously differentiable functions `f : ℝ → (0, +∞)`
satisfying
  `f''(x) · f(x) ≥ 2 (f'(x))²` for all `x ∈ ℝ`.

Answer: the positive constant functions.
-/

namespace Imc2020P5

/-- The problem: a twice continuously differentiable positive function `f`
satisfying `f(x) · f''(x) ≥ 2 (f'(x))²` must be constant.

The official proof: let `g = 1/f`. Then `g'' = (2(f')² - f''f) / f³ ≤ 0`,
so `g > 0` is concave. Using that a positive concave function on `ℝ` is
constant, `f = 1/g` is constant.

TODO: formalize. Key Mathlib gap: "positive concave function on `ℝ` is
constant" — and chaining derivatives of `1/f`.
-/
problem imc2020_p5 (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hpos : ∀ x, 0 < f x)
    (hineq : ∀ x, f x * iteratedDeriv 2 f x ≥ 2 * (deriv f x) ^ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, f x = c := by
  sorry

end Imc2020P5
