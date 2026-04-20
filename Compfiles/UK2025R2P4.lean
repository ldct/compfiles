/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2025, Round 2, Problem 4

How many different sequences of positive integers satisfy u₁ = 1 and
u_{n+1} = (uₙ² + uₙ + 1)^{2025} / u_{n−1} for all n ≥ 2?
-/

namespace UK2025R2P4

/-- The set of valid sequences of positive integers u : ℕ → ℕ (indexed
from 1) with u 1 = 1 and u (n+1) · u (n-1) = (u n² + u n + 1)^2025 for
all n ≥ 2. -/
def validSequences : Set (ℕ → ℕ) :=
  { u | (∀ n, 1 ≤ n → 0 < u n) ∧
        u 1 = 1 ∧
        ∀ n, 2 ≤ n → u (n + 1) * u (n - 1) = (u n ^ 2 + u n + 1) ^ 2025 }

determine num_sequences : ℕ := 1

problem uk2025_r2_p4 :
    ∃ S : Finset (ℕ → ℕ), (↑S : Set (ℕ → ℕ)) = validSequences ∧
      S.card = num_sequences := by
  sorry

end UK2025R2P4
