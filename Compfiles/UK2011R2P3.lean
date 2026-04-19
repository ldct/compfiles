/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2011, Round 2, Problem 3

The function f is defined on the positive integers as follows:
f(1) = 1;
f(2n) = f(n) if n is even;
f(2n) = 2f(n) if n is odd;
f(2n + 1) = 2f(n) + 1 if n is even;
f(2n + 1) = f(n) if n is odd.
Find the number of positive integers n which are less than 2011 and have the
property that f(n) = f(2011).
-/

namespace UK2011R2P3

/-- The BMO function f defined on positive integers. -/
def f : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    let m := (n + 2) / 2
    if (n + 2) % 2 = 0 then
      -- n + 2 = 2 * m
      if m % 2 = 0 then f m else 2 * f m
    else
      -- n + 2 = 2 * m + 1, where m = (n+1)/2
      if m % 2 = 0 then 2 * f m + 1 else f m
  decreasing_by all_goals (simp_wf; omega)

determine solution_value : ℕ := sorry

problem uk2011_r2_p3 :
    (Finset.filter (fun n => f n = f 2011) (Finset.Ico 1 2011)).card =
      solution_value := by
  sorry

end UK2011R2P3
