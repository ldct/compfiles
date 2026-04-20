/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2011, Round 2, Problem 2

Find all positive integers x and y such that x + y + 1 divides 2xy and
x + y − 1 divides x² + y² − 1.
-/

namespace UK2011R2P2

/-- The set of solutions is `{(k, k+1), (k+1, k) : k ≥ 1}` — all pairs of
    consecutive positive integers. -/
determine solution_set : Set (ℕ × ℕ) :=
  { xy : ℕ × ℕ | 0 < xy.1 ∧ 0 < xy.2 ∧ (xy.1 = xy.2 + 1 ∨ xy.2 = xy.1 + 1) }

problem uk2011_r2_p2 :
    { xy : ℕ × ℕ | 0 < xy.1 ∧ 0 < xy.2 ∧
        (xy.1 + xy.2 + 1) ∣ (2 * xy.1 * xy.2) ∧
        (xy.1 + xy.2 - 1) ∣ (xy.1^2 + xy.2^2 - 1) } = solution_set := by
  sorry

end UK2011R2P2
