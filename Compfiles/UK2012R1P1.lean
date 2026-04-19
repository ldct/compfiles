/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2012, Round 1, Problem 1

Find all (positive or negative) integers n for which n² + 20n + 11 is a perfect
square. Remember that you must justify that you have found them all.
-/

namespace UK2012R1P1

/-- Completing the square: n² + 20n + 11 = (n + 10)² − 89. If this equals k²,
    then (n + 10 − k)(n + 10 + k) = 89 (prime), so the solutions come from
    the factorisations of 89. This gives n = 35 or n = −55. -/
determine solution_set : Set ℤ := { 35, -55 }

problem uk2012_r1_p1 :
    { n : ℤ | ∃ k : ℤ, n^2 + 20*n + 11 = k^2 } = solution_set := by
  ext n
  simp only [Set.mem_setOf_eq, solution_set, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk⟩
    -- (n+10)² - k² = 89. Factor: (n+10-k)(n+10+k) = 89.
    have h1 : (n + 10 - k) * (n + 10 + k) = 89 := by linarith
    -- 89 is prime. The divisor (n+10-k) must be ±1 or ±89 in ℤ.
    have hdvd : (n + 10 - k) ∣ 89 := ⟨n + 10 + k, h1.symm⟩
    have habs : (n + 10 - k).natAbs ∣ 89 := by
      rw [show (89 : ℕ) = (89 : ℤ).natAbs from rfl]
      exact Int.natAbs_dvd_natAbs.mpr hdvd
    have h89p : Nat.Prime 89 := by decide
    have hcase : (n + 10 - k).natAbs = 1 ∨ (n + 10 - k).natAbs = 89 :=
      (Nat.dvd_prime h89p).mp habs
    -- Also the sum (n+10-k)+(n+10+k) = 2(n+10), so n+10 = ((n+10-k)+(n+10+k))/2.
    -- We cases on the sign and value of (n+10-k).
    have heq : n + 10 - k + (n + 10 + k) = 2 * (n + 10) := by ring
    have heq' := Int.natAbs_eq (n + 10 - k)
    rcases hcase with h | h <;> rcases heq' with hp | hp <;>
      (rw [h] at hp; push_cast at hp) <;>
      [ ( -- n+10-k = 1
         have hp2 : n + 10 + k = 89 := by nlinarith [h1, hp]
         left; linarith );
        ( -- n+10-k = -1
         have hp2 : n + 10 + k = -89 := by nlinarith [h1, hp]
         right; linarith );
        ( -- n+10-k = 89
         have hp2 : n + 10 + k = 1 := by nlinarith [h1, hp]
         left; linarith );
        ( -- n+10-k = -89
         have hp2 : n + 10 + k = -1 := by nlinarith [h1, hp]
         right; linarith ) ]
  · rintro (rfl | rfl)
    · exact ⟨44, by ring⟩
    · exact ⟨44, by ring⟩

end UK2012R1P1
