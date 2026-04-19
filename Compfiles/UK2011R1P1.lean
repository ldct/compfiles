/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2011, Round 1, Problem 1

One number is removed from the set of integers from 1 to n. The average of
the remaining numbers is 40¾. Which integer was removed?
-/

namespace UK2011R1P1

determine solution_value : ℕ := 61

problem uk2011_r1_p1 :
    { x : ℕ | ∃ n : ℕ, 2 ≤ n ∧ 1 ≤ x ∧ x ≤ n ∧
        4 * (n * (n + 1) / 2 - x) = 163 * (n - 1) } = {solution_value} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨n, hn, hx1, hxn, heq⟩
    -- We need to show x = 61. First determine n.
    -- 4·(n(n+1)/2 - x) = 163(n-1)
    -- 2n(n+1) - 4x = 163(n-1)
    -- Since 1 ≤ x ≤ n and 2 ≤ n:
    -- 2n² + 2n - 163n + 163 = 4x, so 4x = 2n² - 161n + 163
    -- For x ∈ [1, n]: 4 ≤ 2n² - 161n + 163 ≤ 4n
    -- So 2n² - 161n + 159 ≥ 0 and 2n² - 165n + 163 ≤ 0
    -- The second gives n ≤ 82, first gives n ≥ 81 (for integers n ≥ 2)
    have hsum : n * (n + 1) / 2 = n * (n + 1) / 2 := rfl
    -- n * (n+1) is always even
    have heven : 2 ∣ n * (n + 1) := (Nat.even_mul_succ_self n).two_dvd
    obtain ⟨k, hk⟩ := heven
    have hdiv : n * (n + 1) / 2 = k := by rw [hk]; omega
    rw [hdiv] at heq
    -- Now 4(k - x) = 163(n-1), with 2k = n(n+1)
    have hkge : x ≤ k := by
      have hnk : n ≤ k := by
        have h2n : 2 * n ≤ 2 * k := by
          have : n * (n + 1) = 2 * k := hk
          nlinarith
        omega
      omega
    -- So 4k - 4x = 163(n-1), and 2k = n(n+1)
    have h1 : 4 * k = 163 * (n - 1) + 4 * x := by omega
    have h2 : 2 * k = n * (n + 1) := by omega
    -- 2·(4k) = 8k = 4·n(n+1) = 4n² + 4n
    -- 4n² + 4n = 2·(163(n-1) + 4x) = 326n - 326 + 8x
    have h3 : 4 * n * n + 4 * n + 326 = 326 * n + 8 * x := by
      have h4k' : 8 * k = 4 * n * n + 4 * n := by nlinarith [h2]
      -- from h1: 4k = 163(n-1) + 4x, but with Nat subtraction
      -- Since n ≥ 2, 163*(n-1) = 163*n - 163 as natural numbers
      have hn1 : 163 * (n - 1) = 163 * n - 163 := by
        rw [Nat.mul_sub_one]
      have hge : 163 ≤ 163 * n := by nlinarith
      have h1' : 4 * k + 163 = 163 * n + 4 * x := by
        rw [hn1] at h1
        omega
      -- Double: 8k + 326 = 326n + 8x
      have h1'' : 8 * k + 326 = 326 * n + 8 * x := by linarith
      linarith
    -- From h3: 4n² + 4n + 326 = 326n + 8x, so 8x = 4n² - 322n + 326
    -- 2x = n² - (322/4)n + ... messy. Use omega on inequalities.
    -- x ≥ 1 gives 4n² + 4n + 8 ≤ 326n, i.e. 4n² - 322n + 8 ≤ 0
    -- x ≤ n gives 4n² + 4n + 326 ≥ 326n + 8n · ... wait 8x ≤ 8n
    -- So 4n² + 4n ≥ 326n - 326 + 8x ≥ 326n - 326 + 8, i.e. 4n² - 322n + 318 ≥ 0
    --    and 4n² + 4n ≤ 326n - 326 + 8n = 334n - 326, i.e. 4n² - 330n + 326 ≤ 0
    -- 4n² - 322n + 318 ≥ 0: discriminant √(322²-16·318) ≈ √98596 ≈ 314, n ≥ (322+314)/8 ≈ 79.5
    --   so n ≥ 80
    -- 4n² - 330n + 326 ≤ 0: n ≤ (330+√(330²-16·326))/8 = (330+√103684)/8 ≈ (330+322)/8 = 81.5
    --   so n ≤ 81
    -- From h3 with hx1 : 1 ≤ x, we get 4n² + 4n + 326 ≥ 326n + 8
    -- i.e. 4n² - 322n + 318 ≥ 0. Since n ≥ 2, this forces n ≥ 80.
    have hn_lo : 80 ≤ n := by
      nlinarith [h3, hx1, sq_nonneg n]
    have hn_hi : n ≤ 81 := by
      nlinarith [h3, hxn, sq_nonneg n]
    show x = 61
    interval_cases n
    · -- n = 80: 8x = 166, not integer
      omega
    · -- n = 81: 8x = 488, x = 61
      omega
  · intro hx
    subst hx
    refine ⟨81, ?_, ?_, ?_, ?_⟩ <;> decide

end UK2011R1P1
