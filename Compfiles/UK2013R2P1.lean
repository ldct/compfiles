/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2013, Round 2, Problem 1

Are there infinitely many pairs of positive integers (m, n) such that
both m divides n² + 1 and n divides m² + 1?
-/

namespace UK2013R2P1

/-- The odd-indexed Fibonacci pairs (F_{2k−1}, F_{2k+1}) give infinitely
    many such examples. We provide a strictly monotone injection
    ℕ → ℕ × ℕ whose image consists of valid pairs. -/
problem uk2013_r2_p1 :
    ∃ f : ℕ → ℕ × ℕ, StrictMono f ∧
      ∀ k, 0 < (f k).1 ∧ 0 < (f k).2 ∧
           (f k).1 ∣ (f k).2 ^ 2 + 1 ∧
           (f k).2 ∣ (f k).1 ^ 2 + 1 := by
  sorry

end UK2013R2P1
