/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2024, Problem 8

Define the sequence `x₁, x₂, …` by `x₁ = 2`, `x₂ = 4`, and

  `xₙ₊₂ = 3 xₙ₊₁ − 2 xₙ + 2ⁿ / xₙ`  for `n ≥ 1`.

Prove that `lim xₙ / 2ⁿ` exists and satisfies
`(1 + √3)/2 ≤ lim ≤ 3/2`.
-/

namespace Imc2024P8

/-- The recursive sequence. -/
noncomputable def x : ℕ → ℝ
  | 0 => 2  -- x_1 (1-indexed in the problem; we use 0-indexed)
  | 1 => 4  -- x_2
  | n + 2 => 3 * x (n + 1) - 2 * x n + (2 : ℝ) ^ n / x n

problem imc2024_p8 :
    ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => x n / (2 : ℝ) ^ n) Filter.atTop (nhds L) ∧
      (1 + Real.sqrt 3) / 2 ≤ L ∧ L ≤ 3 / 2 := by
  -- TODO: use the auxiliary sequence y_n = x_n/2^{n-1} (satisfying y_{n+1} =
  -- y_n + 2/y_n), show it is monotonic bounded, compute limits.
  sorry

end Imc2024P8
