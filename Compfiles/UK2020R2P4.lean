/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2020, Round 2, Problem 4

A sequence b₁, b₂, b₃, . . . of nonzero real numbers has the property
that b_{n+2} = (b_{n+1}² − 1)/bₙ for all positive integers n. Suppose
that b₁ = 1 and b₂ = k where 1 < k < 2. Show that there is some
constant B, depending on k, such that −B ≤ bₙ ≤ B for all n. Also
show that, for some 1 < k < 2, there is a value of n such that
bₙ > 2020.
-/

namespace UK2020R2P4

problem uk2020_r2_p4 :
    (∀ k : ℝ, 1 < k → k < 2 →
      ∀ b : ℕ → ℝ,
        (∀ n, 1 ≤ n → b n ≠ 0) →
        b 1 = 1 → b 2 = k →
        (∀ n, 1 ≤ n → b (n + 2) = (b (n + 1)^2 - 1) / b n) →
        ∃ B : ℝ, ∀ n, 1 ≤ n → -B ≤ b n ∧ b n ≤ B) ∧
    (∃ k : ℝ, 1 < k ∧ k < 2 ∧
      ∃ b : ℕ → ℝ,
        (∀ n, 1 ≤ n → b n ≠ 0) ∧
        b 1 = 1 ∧ b 2 = k ∧
        (∀ n, 1 ≤ n → b (n + 2) = (b (n + 1)^2 - 1) / b n) ∧
        ∃ n, 2020 < b n) := by
  sorry

end UK2020R2P4
