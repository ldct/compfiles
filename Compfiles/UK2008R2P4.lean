/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2008, Round 2, Problem 4

Prove that there are infinitely many pairs of distinct positive integers x, y
such that x³ + y² divides x² + y³.
-/

namespace UK2008R2P4

problem uk2008_r2_p4 :
    ∃ f : ℕ → ℕ × ℕ,
      StrictMono f ∧
      ∀ k, 0 < (f k).1 ∧ 0 < (f k).2 ∧ (f k).1 ≠ (f k).2 ∧
           ((f k).1 ^ 3 + (f k).2 ^ 2) ∣ ((f k).1 ^ 2 + (f k).2 ^ 3) := by
  sorry

end UK2008R2P4
