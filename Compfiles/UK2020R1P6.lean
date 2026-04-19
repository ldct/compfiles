/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2020, Round 1, Problem 6

A function f is called good if it assigns an integer value f(m, n) to every
ordered pair of integers (m, n) in such a way that for every pair of integers
(m, n) we have:
2f(m, n) = f(m − n, n − m) + m + n = f(m + 1, n) + f(m, n + 1) − 1.
Find all good functions.
-/

namespace UK2020R1P6

determine solution_set : Set (ℤ → ℤ → ℤ) :=
  { f | ∃ k : ℤ, ∀ m n : ℤ, f m n = (k + 1) * m - k * n }

problem uk2020_r1_p6 :
    { f : ℤ → ℤ → ℤ |
        (∀ m n, 2 * f m n = f (m - n) (n - m) + m + n) ∧
        (∀ m n, 2 * f m n = f (m + 1) n + f m (n + 1) - 1) } =
    solution_set := by
  sorry

end UK2020R1P6
