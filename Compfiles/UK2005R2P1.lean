/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2005, Round 2, Problem 1

The integer N is positive. There are exactly 2005 ordered pairs (x, y)
of positive integers satisfying 1/x + 1/y = 1/N. Prove that N is a
perfect square.
-/

namespace UK2005R2P1

problem uk2005_r2_p1 (N : ℕ) (hN : 0 < N)
    (h : { p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧
           (1 : ℚ) / p.1 + (1 : ℚ) / p.2 = (1 : ℚ) / N }.ncard = 2005) :
    ∃ k : ℕ, N = k^2 := by
  sorry

end UK2005R2P1
