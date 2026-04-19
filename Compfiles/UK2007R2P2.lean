/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2007, Round 2, Problem 2

Show that there are infinitely many pairs of positive integers (m, n) such
that (m + 1)/n + (n + 1)/m is a positive integer.
-/

namespace UK2007R2P2

problem uk2007_r2_p2 :
    ∃ f : ℕ → ℕ × ℕ,
      StrictMono f ∧
      ∀ k, 0 < (f k).1 ∧ 0 < (f k).2 ∧
           (f k).1 ∣ ((f k).2 + 1) ∧ (f k).2 ∣ ((f k).1 + 1) ∧
           -- the sum is a positive integer
           ∃ N : ℕ, 0 < N ∧
             ((f k).1 + 1) * (f k).1 + ((f k).2 + 1) * (f k).2
               = N * ((f k).1 * (f k).2) := by
  sorry

end UK2007R2P2
