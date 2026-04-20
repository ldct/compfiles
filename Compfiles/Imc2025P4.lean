/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Competition 2025, Problem 4

Let `a` be an even positive integer. Find all real numbers `x` such that

  `⌊ a√(bᵃ + x) · bᵃ⁻¹ ⌋ = bᵃ + ⌊x/a⌋`      (1)

holds for every positive integer `b`.

Answer:
- If `a = 2`, the set of solutions is `[-1, 2) ∪ [3, 4)`.
- If `a > 2`, the set of solutions is `[-1, a)`.
-/

namespace Imc2025P4

/-- The set of real numbers `x` satisfying (1) for all positive integers `b`,
  depending on the (even) parameter `a`. -/
noncomputable determine answer (a : ℕ) : Set ℝ :=
  if a = 2 then (Set.Ico (-1 : ℝ) 2 ∪ Set.Ico (3 : ℝ) 4)
  else Set.Ico (-1 : ℝ) a

problem imc2025_p4 (a : ℕ) (ha_pos : 0 < a) (ha_even : Even a) (x : ℝ) :
    x ∈ answer a ↔
    ∀ b : ℕ, 0 < b →
      ⌊((b : ℝ) ^ a + x) ^ ((a : ℝ)⁻¹) * (b : ℝ) ^ (a - 1)⌋ =
        (b : ℤ) ^ a + ⌊x / a⌋ := by
  -- TODO: The proof proceeds as follows (following the official solution).
  -- Setting b = 1 constrains ⌊a√(1+x)⌋ = 1 + ⌊x/a⌋.
  -- Bernoulli's inequality combined with this yields that ⌊x/a⌋ = m is
  -- restricted to {-1, 0} when a > 2, and to {-1, 0, 1} when a = 2.
  -- For each such m, we get the range (m+1)^a - 1 ≤ x < a(m+1).
  -- When a > 2: m=-1 gives [-1, 0); m=0 gives [0, a). Union is [-1, a).
  -- When a = 2: m=-1 gives [-1, 0); m=0 gives [0, 2); m=1 gives [3, 4).
  -- The verification direction uses Bernoulli again.
  sorry

end Imc2025P4
