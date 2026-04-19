/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2015, Round 1, Problem 2

Positive integers p, a and b satisfy the equation p² + a² = b². Prove that if
p is a prime greater than 3, then a is a multiple of 12 and 2(p + a + 1) is a
perfect square.
-/

namespace UK2015R1P2

problem uk2015_r1_p2 :
    ∀ p a b : ℕ, 0 < p → 0 < a → 0 < b → p.Prime → 3 < p →
      p^2 + a^2 = b^2 →
      12 ∣ a ∧ ∃ k : ℕ, 2 * (p + a + 1) = k^2 := by
  sorry

end UK2015R1P2
