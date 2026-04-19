/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2020, Round 1, Problem 1

Show that there are at least three prime numbers p less than 200 for which
p + 2, p + 6, p + 8 and p + 12 are all prime. Show also that there is only
one prime number q for which q + 2, q + 6, q + 8, q + 12 and q + 14 are all
prime.
-/

namespace UK2020R1P1

/-- The unique prime q with q, q + 2, q + 6, q + 8, q + 12, q + 14 all prime
    is q = 5 (giving 5, 7, 11, 13, 17, 19). -/
determine solution_value : ℕ := 5

/-- Part (a): at least three primes p < 200 with p, p + 2, p + 6, p + 8, p + 12
    all prime. Part (b): the unique such prime with the extra condition
    p + 14 also prime is solution_value = 5. -/
problem uk2020_r1_p1 :
    (∃ S : Finset ℕ, S.card ≥ 3 ∧
      ∀ p ∈ S, p < 200 ∧ p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧
                 (p + 8).Prime ∧ (p + 12).Prime) ∧
    { q : ℕ | q.Prime ∧ (q + 2).Prime ∧ (q + 6).Prime ∧ (q + 8).Prime ∧
              (q + 12).Prime ∧ (q + 14).Prime } = { solution_value } := by
  sorry

end UK2020R1P1
