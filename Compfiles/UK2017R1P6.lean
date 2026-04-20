/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2017, Round 1, Problem 6

Consecutive positive integers m, m+1, m+2 and m+3 are divisible by consecutive
odd positive integers n, n + 2, n + 4 and n + 6 respectively. Determine the
smallest possible m in terms of n.
-/

namespace UK2017R1P6

/-- For each odd positive integer `n`, there is a smallest positive integer `m`
such that `n ∣ m`, `(n+2) ∣ (m+1)`, `(n+4) ∣ (m+2)` and `(n+6) ∣ (m+3)`. This
theorem asserts the existence (and uniqueness) of that minimum. -/
determine smallest_m (n : ℕ) : ℕ := 0 -- placeholder for the closed-form answer

problem uk2017_r1_p6 (n : ℕ) (_hn_odd : Odd n) (_hn_pos : 0 < n) :
    IsLeast { m : ℕ | 0 < m ∧ n ∣ m ∧ (n + 2) ∣ (m + 1) ∧
                       (n + 4) ∣ (m + 2) ∧ (n + 6) ∣ (m + 3) }
            (smallest_m n) := by
  sorry

end UK2017R1P6
