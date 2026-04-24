/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2003, Problem 12
(IMC 2003, Day 2, Problem 6)

Let `(aₙ)` be the sequence defined by
  `a₀ = 1`,  `aₙ₊₁ = (1/(n+1)) Σₖ₌₀ⁿ aₖ / (n - k + 2)`.

Find
  `lim_{n → ∞} Σₖ₌₀ⁿ aₖ / 2ᵏ`.

The answer is `e / 2`.
-/

namespace Imc2003P12

open Filter Topology

/-- The sequence `a` defined by the recurrence. -/
noncomputable def a : ℕ → ℝ
  | 0 => 1
  | n + 1 => (1 / (n + 1 : ℝ)) *
      ∑ k : Fin (n + 1), a k.val / (n - k.val + 2 : ℝ)

/-- The partial sums `Sₙ = Σ_{k=0}^n aₖ / 2ᵏ`. -/
noncomputable def S (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), a k / 2 ^ k

/-- The limit of the partial sums is `e / 2`. -/
noncomputable determine answer : ℝ := Real.exp 1 / 2

problem imc2003_p12 :
    Tendsto S atTop (𝓝 answer) := by
  -- Standard solution (sketch):
  -- Let `f(x) = Σ aₙ xⁿ` be the generating function of `a`. The recurrence
  -- implies `f'(x) = f(x) · Σₘ xᵐ/(m+2)`. Integrating on `[0, x]`:
  --   `log f(x) = Σ_{m ≥ 0} x^{m+1} / ((m+1)(m+2))
  --            = Σ (x^{m+1}/(m+1) - x^{m+1}/(m+2))
  --            = -log(1 - x) - (1/x)(-log(1 - x) - x)
  --            = 1 + (1 - 1/x) log(1 / (1 - x))`.
  -- At `x = 1/2`: `log f(1/2) = 1 + (-1) log 2 = 1 - log 2`, so
  -- `f(1/2) = e / 2`.
  --
  -- A complete formalization requires:
  --   (1) absolute convergence of `Σ aₙ/2ⁿ` (radius of convergence ≥ 1/2),
  --   (2) term-by-term differentiation of the resulting power series,
  --   (3) a uniqueness-of-ODE argument to identify the generating function,
  --   (4) evaluation of the closed form at `x = 1/2`.
  -- None of these are immediate in Mathlib's current analytic infrastructure,
  -- so we leave a sorry here.
  -- TODO: formalize the generating-function ODE argument.
  sorry

end Imc2003P12
