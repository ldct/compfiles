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

/-- The recursive sequence. We use 0-indexed: `x 0` corresponds to the
problem's `x_1 = 2`, `x 1` corresponds to `x_2 = 4`. The paper recurrence
`x_{m+2} = 3 x_{m+1} - 2 x_m + 2^m / x_m` for `m ≥ 1` with our index shift
`m = n + 1` becomes `x (n+2) = 3 x (n+1) - 2 x n + 2^(n+1) / x n`. -/
noncomputable def x : ℕ → ℝ
  | 0 => 2  -- x_1 (1-indexed in the problem; we use 0-indexed)
  | 1 => 4  -- x_2
  | n + 2 => 3 * x (n + 1) - 2 * x n + (2 : ℝ) ^ (n + 1) / x n

snip begin

/-- Combined induction: `x n > 0` and `2 * x n ≤ x (n+1)`. The induction is
on `n`; at step `n+1` we need the bound at `n` (for `x (n+2)`). -/
lemma pos_and_mono : ∀ n : ℕ, 0 < x n ∧ 2 * x n ≤ x (n + 1)
  | 0 => by
      refine ⟨by norm_num [x], ?_⟩
      show 2 * x 0 ≤ x 1
      simp [x]; norm_num
  | n + 1 => by
      have ih := pos_and_mono n
      obtain ⟨hpos_n, h_n⟩ := ih
      -- x(n+1) ≥ 2 x n > 0
      have hpos_n1 : 0 < x (n + 1) := lt_of_lt_of_le (by linarith) h_n
      refine ⟨hpos_n1, ?_⟩
      -- Need: 2 * x (n+1) ≤ x (n+2).
      -- x (n+2) = 2 x(n+1) + (x(n+1) - 2 x n) + 2^(n+1)/x n
      have hx2 : x (n + 2) = 2 * x (n + 1) + (x (n + 1) - 2 * x n) +
          (2 : ℝ) ^ (n + 1) / x n := by
        show 3 * x (n + 1) - 2 * x n + (2 : ℝ) ^ (n + 1) / x n = _
        ring
      have hpow : (0 : ℝ) < (2 : ℝ) ^ (n + 1) := by positivity
      have hdiv : (0 : ℝ) ≤ (2 : ℝ) ^ (n + 1) / x n := le_of_lt (div_pos hpow hpos_n)
      have hsub : 0 ≤ x (n + 1) - 2 * x n := by linarith
      linarith [hx2]

lemma x_pos (n : ℕ) : 0 < x n := (pos_and_mono n).1

lemma two_mul_x_le (n : ℕ) : 2 * x n ≤ x (n + 1) := (pos_and_mono n).2

snip end

problem imc2024_p8 :
    ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => x n / (2 : ℝ) ^ (n + 1))
        Filter.atTop (nhds L) ∧
      (1 + Real.sqrt 3) / 2 ≤ L ∧ L ≤ 3 / 2 := by
  -- Paper solution: let y_n = x_n / 2^n. Show 2 x_n ≤ x_{n+1} ≤ 2 x_n + n
  -- so y_n is increasing and bounded (y_{n+1} ≤ y_n + n/2^n), hence converges
  -- to some c. Then 4 y_{n+2} - 2 y_{n+1} - (4 y_{n+1} - 2 y_n) = 1/(2^n y_n),
  -- telescoping to 4 y_{m+2} - 2 y_{m+1} = 2 + Σ 1/(2^n y_n). Taking m→∞ gives
  -- 2c = 2 + S with S ∈ [1/c, 1], yielding 2c^2 ≥ 2c+1 and 2c ≤ 3,
  -- i.e. (1+√3)/2 ≤ c ≤ 3/2.
  sorry

end Imc2024P8
