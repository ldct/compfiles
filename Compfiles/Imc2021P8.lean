/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra, .Combinatorics] }

/-!
# International Mathematical Competition 2021, Problem 8

Let `n` be a positive integer. At most how many distinct unit vectors can be
selected in `ℝⁿ` such that from any three of them, at least two are orthogonal?

Answer: `2n`.
-/

namespace Imc2021P8

/-- The maximum number of unit vectors in ℝⁿ such that every 3 contain
an orthogonal pair. Answer: `2n`. -/
determine answer (n : ℕ) : ℕ := 2 * n

problem imc2021_p8 (n : ℕ) (hn : 0 < n) :
    IsGreatest
      { N | ∃ v : Fin N → EuclideanSpace ℝ (Fin n),
        Function.Injective v ∧
        (∀ i, ‖v i‖ = 1) ∧
        (∀ i j k : Fin N, i ≠ j → j ≠ k → i ≠ k →
          inner ℝ (v i) (v j) = (0 : ℝ) ∨
          inner ℝ (v j) (v k) = (0 : ℝ) ∨
          inner ℝ (v i) (v k) = (0 : ℝ)) }
      (answer n) := by
  -- TODO: projector-trace argument; example via {±e_i}.
  sorry

end Imc2021P8
