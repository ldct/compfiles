/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2010, Round 2, Problem 3

The integer x is at least 3 and n = x⁶ − 1. Let p be a prime and k be a
positive integer such that p^k is a factor of n. Show that p^{3k} < 8n.
-/

namespace UK2010R2P3

problem uk2010_r2_p3 :
    ∀ x : ℤ, 3 ≤ x →
    ∀ n : ℤ, n = x^6 - 1 →
    ∀ p : ℕ, p.Prime →
    ∀ k : ℕ, 0 < k →
      ((p : ℤ)^k ∣ n) →
      (p : ℤ)^(3 * k) < 8 * n := by
  sorry

end UK2010R2P3
