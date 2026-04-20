/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2012, Round 2, Problem 4

Show that there is a positive integer k with the following property: if a, b,
c, d, e and f are integers and m is a divisor of aⁿ + bⁿ + cⁿ − dⁿ − eⁿ − fⁿ
for all integers n in the range 1 ≤ n ≤ k, then m is a divisor of
aⁿ + bⁿ + cⁿ − dⁿ − eⁿ − fⁿ for all positive integers n.
-/

namespace UK2012R2P4

problem uk2012_r2_p4 :
    ∃ k : ℕ, 0 < k ∧
      ∀ a b c d e f : ℤ, ∀ m : ℤ,
        (∀ n : ℕ, 1 ≤ n → n ≤ k →
          m ∣ (a^n + b^n + c^n - d^n - e^n - f^n)) →
        ∀ n : ℕ, 0 < n →
          m ∣ (a^n + b^n + c^n - d^n - e^n - f^n) := by
  sorry

end UK2012R2P4
