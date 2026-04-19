/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2009, Round 2, Problem 1

Find all solutions in non-negative integers a, b to √a + √b = √2009.
-/

namespace UK2009R2P1

/-- 2009 = 7² · 41, so √2009 = 7√41, and the solutions are (a, b) with
    √a = i√41, √b = (7-i)√41 for i = 0, 1, …, 7, i.e.
    a = 41·i², b = 41·(7-i)². -/
determine solution_set : Set (ℕ × ℕ) :=
  { (0, 2009), (41, 41 * 36), (41 * 4, 41 * 25), (41 * 9, 41 * 16),
    (41 * 16, 41 * 9), (41 * 25, 41 * 4), (41 * 36, 41), (2009, 0) }

problem uk2009_r2_p1 :
    { ab : ℕ × ℕ | (Real.sqrt ab.1 + Real.sqrt ab.2 = Real.sqrt 2009) } =
      solution_set := by
  sorry

end UK2009R2P1
