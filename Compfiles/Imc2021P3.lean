/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2021, Problem 3

A positive real number `d` is *good* if there exists an infinite sequence
`a₁, a₂, … ∈ (0, d)` such that for each `n`, the points `a₁, …, aₙ` partition
`[0, d]` into segments of length at most `1/n` each. Find `sup {d | d good}`.

Answer: `ln 2`.
-/

namespace Imc2021P3

/-- The set of "good" positive reals `d`. -/
def Good (d : ℝ) : Prop :=
  0 < d ∧ ∃ a : ℕ → ℝ,
    (∀ n, 0 < a n ∧ a n < d) ∧
    ∀ n : ℕ, 0 < n →
      ∀ x ∈ Set.Icc (0 : ℝ) d,
        ∃ i ∈ Finset.range n, |x - a i| ≤ 1 / n
      -- TODO: this is a simplified form; the actual condition is that
      -- consecutive sorted points plus {0, d} partition with gaps ≤ 1/n.

/-- The supremum of good `d`. -/
noncomputable determine answer : ℝ := Real.log 2

problem imc2021_p3 : sSup { d | Good d } = answer := by
  -- TODO: upper bound via log-identity; lower bound via explicit construction.
  sorry

end Imc2021P3
