/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2021, Problem 4

Let `f : ℝ → ℝ` be a function. Suppose that for every `ε > 0`, there
exists `g : ℝ → (0, ∞)` such that for every pair `(x, y)`,

  if `|x - y| < min (g x) (g y)`, then `|f x - f y| < ε`.

Prove that `f` is the pointwise limit of a sequence of continuous
`ℝ → ℝ` functions (i.e. `f` is of Baire class `1`).
-/

namespace Imc2021P4

problem imc2021_p4 (f : ℝ → ℝ)
    (hyp : ∀ ε > 0, ∃ g : ℝ → ℝ, (∀ x, 0 < g x) ∧
      ∀ x y, |x - y| < min (g x) (g y) → |f x - f y| < ε) :
    ∃ (φ : ℕ → ℝ → ℝ), (∀ n, Continuous (φ n)) ∧
      ∀ x, Filter.Tendsto (fun n => φ n x) Filter.atTop (nhds (f x)) := by
  -- TODO: Following the official solution.
  -- The hypothesis says f has "small oscillation on small balls" in a
  -- uniform-over-pairs sense. The proof constructs piecewise-linear
  -- approximations φₙ using a finite partition of unity associated to
  -- the gauge function g with ε = 1/n, then shows φₙ x → f x pointwise.
  -- This is an instance of Baire class 1; the full argument is delicate
  -- but elementary (no measure theory).
  sorry

end Imc2021P4
