/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2012, Round 2, Problem 2

A function f is defined on the positive integers by f(1) = 1 and, for n > 1,
f(n) = f(⌊(2n−1)/3⌋) + f(⌊2n/3⌋)
where ⌊x⌋ denotes the greatest integer less than or equal to x.
Is it true that f(n) − f(n − 1) ≤ n for all n > 1?
-/

namespace UK2012R2P2

/-- The BMO recursive function. -/
def f : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => f ((2 * (n + 2) - 1) / 3) + f ((2 * (n + 2)) / 3)
  decreasing_by all_goals (simp_wf; omega)

/-- The answer to whether f(n) - f(n-1) ≤ n holds for all n > 1. -/
determine solution_value : Prop := False

problem uk2012_r2_p2 :
    (∀ n : ℕ, 1 < n → f n - f (n - 1) ≤ (n : ℤ)) ↔ solution_value := by
  constructor
  · intro h
    have h242 : f 242 - f 241 ≤ (242 : ℤ) := h 242 (by norm_num)
    revert h242
    native_decide
  · intro h
    exact absurd h (fun h => h.elim)

end UK2012R2P2
