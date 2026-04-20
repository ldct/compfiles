/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2008, Round 1, Problem 6

The function f is defined on the set of positive integers by f(1) = 1,
f(2n) = 2 f(n), and n f(2n + 1) = (2n + 1)(f(n) + n) for all n ≥ 1.
i)  Prove that f(n) is always an integer.
ii) For how many positive integers less than 2007 is f(n) = 2n?
-/

namespace UK2008R1P6

/-- The function f as specified. We define it on ℕ (with f 0 = 0 by
convention). Since the recurrence on odd arguments has an `n` in the
denominator, we define f via the recursive rule
  f(2n) = 2 f(n)
  f(2n + 1) = ((2n + 1) * (f n + n)) / n   (for n ≥ 1)
  f(1) = 1
and the problem asks us to show that the latter division is exact. -/
noncomputable def f : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    let m := (n + 2) / 2
    if (n + 2) % 2 = 0 then 2 * f m
    else (((n + 2) * (f m + m)) / m)
  decreasing_by
    all_goals (simp_wf; omega)

determine solution_value : ℕ := 10

problem uk2008_r1_p6 :
    (∀ n : ℕ, 0 < n → (f (2 * n + 1) * n = (2 * n + 1) * (f n + n))) ∧
    (Finset.card ((Finset.Ico 1 2007).filter (fun n => f n = 2 * n)) =
      solution_value) := by
  sorry

end UK2008R1P6
