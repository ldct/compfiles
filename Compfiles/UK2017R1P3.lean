/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2017, Round 1, Problem 3

Determine all pairs (m, n) of positive integers which satisfy the equation
n² − 6n = m² + m − 10.
-/

namespace UK2017R1P3

/-- Rewriting: (n − 3)² − 9 = m² + m − 10, so (n − 3)² = m² + m − 1,
    giving 4(n − 3)² = (2m + 1)² − 5. Equivalently
    (2m + 1 − 2(n − 3))(2m + 1 + 2(n − 3)) = 5. Case analysis on the
    factorisation of 5 yields (m, n) = (1, 2) and (m, n) = (1, 4). -/
determine solution_set : Set (ℕ × ℕ) := { (1, 2), (1, 4) }

problem uk2017_r1_p3 :
    { mn : ℕ × ℕ | 0 < mn.1 ∧ 0 < mn.2 ∧
        (mn.2 : ℤ)^2 - 6 * mn.2 = (mn.1 : ℤ)^2 + mn.1 - 10 } = solution_set := by
  ext ⟨m, n⟩
  simp only [Set.mem_setOf_eq, solution_set, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.mk.injEq]
  constructor
  · rintro ⟨hm, hn, heq⟩
    -- (2m+1)² - (2(n-3))² = 5. Both factors differ by 2·2(n-3), same parity.
    -- Let a = 2m+1, b = 2n-6. Then a² - b² = 5, so (a-b)(a+b) = 5.
    -- a ≥ 3 since m ≥ 1.
    have ha : (2 * (m : ℤ) + 1) ≥ 3 := by
      have : (1 : ℤ) ≤ m := by exact_mod_cast hm
      linarith
    have key : (2 * (m : ℤ) + 1 - (2 * n - 6)) * (2 * m + 1 + (2 * n - 6)) = 5 := by
      nlinarith [heq]
    -- Factor pairs of 5: since a ≥ 3 > 0 and (a-b)(a+b) = 5 > 0, either both factors
    -- positive or both negative. If both negative, a+b < 0 with a ≥ 3, so b ≤ -4, b ≤ -4.
    -- But then a-b ≥ 7, so (a-b)(a+b) with a+b ≤ -1 gives product ≤ -7, can't be 5.
    -- Hence both positive. So (a-b, a+b) ∈ {(1,5),(5,1)}.
    set a := 2 * (m : ℤ) + 1 with ha_def
    set b := 2 * (n : ℤ) - 6 with hb_def
    have hpos_sum : 0 < a + b ∨ a + b ≤ 0 := by omega
    rcases hpos_sum with hs | hs
    · -- a + b > 0
      have hdiff_pos : 0 < a - b := by
        rcases lt_or_ge (a - b) 0 with hn1 | hn1
        · -- product would be negative
          have : (a - b) * (a + b) < 0 := mul_neg_of_neg_of_pos hn1 hs
          omega
        · rcases eq_or_lt_of_le hn1 with h0 | h0
          · rw [← h0] at key; simp at key
          · exact h0
      -- Both positive, product 5. Factor pairs (1,5) or (5,1).
      have hd : (a - b) ∣ 5 := ⟨a + b, key.symm⟩
      have hn2 : (a - b).natAbs ∣ 5 := by
        rw [show (5 : ℕ) = (5 : ℤ).natAbs from rfl]
        exact Int.natAbs_dvd_natAbs.mpr hd
      have h5p : Nat.Prime 5 := by decide
      have hc : (a - b).natAbs = 1 ∨ (a - b).natAbs = 5 := (Nat.dvd_prime h5p).mp hn2
      have hab_pos : a - b = (a - b).natAbs := by
        rw [Int.natAbs_of_nonneg hdiff_pos.le]
      rcases hc with h1 | h1
      · -- a - b = 1, then a + b = 5, so a = 3, b = 2 → m = 1, n = 4
        rw [h1] at hab_pos
        have hab_val : a - b = 1 := by rw [hab_pos]; norm_num
        have : a + b = 5 := by
          have := key
          rw [hab_val] at this; linarith
        right
        refine ⟨?_, ?_⟩ <;> [omega; omega]
      · -- a - b = 5, then a + b = 1, so a = 3, b = -2 → m = 1, n = 2
        rw [h1] at hab_pos
        have hab_val : a - b = 5 := by rw [hab_pos]; norm_num
        have : a + b = 1 := by
          have := key
          rw [hab_val] at this; linarith
        left
        refine ⟨?_, ?_⟩ <;> [omega; omega]
    · -- a + b ≤ 0. Then a + b < 0 or a+b = 0. a+b=0 gives product 0 ≠ 5.
      exfalso
      rcases eq_or_lt_of_le hs with h0 | h0
      · rw [h0] at key; simp at key
      · -- a+b < 0, so a < -b, so b < -a ≤ -3. Then a-b > a+3 ≥ 6 > 0.
        -- Product = (a-b)(a+b) < 0, not 5.
        have : a - b > 0 := by linarith
        have : (a - b) * (a + b) < 0 := mul_neg_of_pos_of_neg this h0
        omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> refine ⟨by norm_num, by norm_num, by norm_num⟩

end UK2017R1P3
