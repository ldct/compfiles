/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2025, Round 1, Problem 5

Let p be a prime number, and let n be the smallest positive integer, strictly
greater than 1, for which n⁶ − 1 is divisible by p. Prove that at least one of
(n + 1)⁶ − 1 and (n + 2)⁶ − 1 is divisible by p.
-/

namespace UK2025R1P5

problem uk2025_r1_p5 (p : ℕ) (_hp : p.Prime) (n : ℕ) (hn1 : 1 < n)
    (hndvd : (p : ℤ) ∣ ((n : ℤ) ^ 6 - 1))
    (hmin : ∀ m : ℕ, 1 < m → m < n → ¬ ((p : ℤ) ∣ ((m : ℤ) ^ 6 - 1))) :
    ((p : ℤ) ∣ ((n + 1 : ℤ) ^ 6 - 1)) ∨
    ((p : ℤ) ∣ ((n + 2 : ℤ) ^ 6 - 1)) := by
  sorry

end UK2025R1P5
