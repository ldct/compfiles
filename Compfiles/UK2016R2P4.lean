/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2016, Round 2, Problem 4

Suppose that p is a prime number and that there are different positive integers
u and v such that p² is the mean of u² and v². Prove that 2p − u − v is a
square or twice a square.
-/

namespace UK2016R2P4

problem uk2016_r2_p4 :
    ∀ p u v : ℕ, p.Prime → 0 < u → 0 < v → u ≠ v →
      2 * p^2 = u^2 + v^2 →
      (∃ k : ℤ, (2 * p - u - v : ℤ) = k^2) ∨
      (∃ k : ℤ, (2 * p - u - v : ℤ) = 2 * k^2) := by
  sorry

end UK2016R2P4
