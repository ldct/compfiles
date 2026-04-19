/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2006, Round 1, Problem 1

Let n be an integer greater than 6. Prove that if n − 1 and n + 1 are both
prime, then n²(n² + 16) is divisible by 720. Is the converse true?

(The converse is false; we state both directions, with the converse negated.)
-/

namespace UK2006R1P1

problem uk2006_r1_p1_forward :
    ∀ n : ℕ, 6 < n → Nat.Prime (n - 1) → Nat.Prime (n + 1) →
      720 ∣ n^2 * (n^2 + 16) := by
  sorry

/-- The converse is false: there exists n > 6 with 720 ∣ n²(n² + 16) but
    either n − 1 or n + 1 is not prime. -/
problem uk2006_r1_p1_converse_false :
    ∃ n : ℕ, 6 < n ∧ 720 ∣ n^2 * (n^2 + 16) ∧
      ¬ (Nat.Prime (n - 1) ∧ Nat.Prime (n + 1)) := by
  sorry

end UK2006R1P1
