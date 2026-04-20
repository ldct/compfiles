/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2009, Round 1, Problem 4

Find all positive integers n such that both n + 2008 divides n² + 2008
and n + 2009 divides n² + 2009.
-/

namespace UK2009R1P4

determine solution_set : Set ℕ := {1}

problem uk2009_r1_p4 :
    { n : ℕ | 0 < n ∧ (n + 2008) ∣ (n^2 + 2008) ∧
              (n + 2009) ∣ (n^2 + 2009) } = solution_set := by
  ext n
  simp only [Set.mem_setOf_eq, solution_set, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hn, h1, h2⟩
    -- Key: (n+2008) | 2008·2009 and (n+2009) | 2009·2010.
    have hd1 : (n + 2008) ∣ 2008 * 2009 := by
      -- (n+2008)·(n+2008) - (n² + 2008) = 4016·n + 2008² - 2008 = 4016·n + 2008·2007
      -- Hmm, let's compute 2008·(n+2008) - (n² + 2008) - ... better:
      -- n² + 2008 = (n+2008)·n - 2008n + 2008 = (n+2008)·n - 2008·(n-1)
      -- so (n+2008) | 2008·(n-1)
      -- and (n+2008) | 2008·(n+2008), so subtract: (n+2008) | 2008·(n+2008) - 2008·(n-1) = 2008·2009.
      -- Work via integers to avoid ℕ subtraction.
      have h1' : ((n + 2008 : ℕ) : ℤ) ∣ ((n^2 + 2008 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h1
      have : ((n + 2008 : ℕ) : ℤ) ∣ ((n : ℤ)^2 + 2008) := by
        have heq : ((n^2 + 2008 : ℕ) : ℤ) = (n : ℤ)^2 + 2008 := by push_cast; ring
        rw [← heq]; exact h1'
      have hstep : ((n : ℤ) + 2008) ∣ 2008 * (n - 1) := by
        have hz : ((n + 2008 : ℕ) : ℤ) = (n : ℤ) + 2008 := by push_cast; ring
        rw [hz] at this
        have hkey : 2008 * ((n : ℤ) - 1) = ((n : ℤ) + 2008) * n - ((n : ℤ)^2 + 2008) := by ring
        rw [hkey]
        exact Dvd.dvd.sub (Dvd.intro n rfl) this
      have hfinal : ((n : ℤ) + 2008) ∣ 2008 * 2009 := by
        have h2008 : ((n : ℤ) + 2008) ∣ 2008 * ((n : ℤ) + 2008) := ⟨2008, by ring⟩
        have hsub : ((n : ℤ) + 2008) ∣ (2008 * ((n : ℤ) + 2008) - 2008 * (n - 1)) := h2008.sub hstep
        have heq : 2008 * ((n : ℤ) + 2008) - 2008 * (n - 1) = 2008 * 2009 := by ring
        rw [heq] at hsub; exact hsub
      have hpos : ((n + 2008 : ℕ) : ℤ) = (n : ℤ) + 2008 := by push_cast; ring
      rw [← hpos] at hfinal
      have hcastN : ((2008 * 2009 : ℕ) : ℤ) = 2008 * 2009 := by norm_cast
      have : ((n + 2008 : ℕ) : ℤ) ∣ ((2008 * 2009 : ℕ) : ℤ) := by rw [hcastN]; exact hfinal
      exact Int.natCast_dvd_natCast.mp this
    have hd2 : (n + 2009) ∣ 2009 * 2010 := by
      have h2' : ((n + 2009 : ℕ) : ℤ) ∣ ((n^2 + 2009 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h2
      have step1 : ((n : ℤ) + 2009) ∣ ((n : ℤ)^2 + 2009) := by
        have heq : ((n^2 + 2009 : ℕ) : ℤ) = (n : ℤ)^2 + 2009 := by push_cast; ring
        have hpos : ((n + 2009 : ℕ) : ℤ) = (n : ℤ) + 2009 := by push_cast; ring
        rw [← heq, ← hpos]; exact h2'
      have hstep : ((n : ℤ) + 2009) ∣ 2009 * ((n : ℤ) - 1) := by
        have hkey : 2009 * ((n : ℤ) - 1) = ((n : ℤ) + 2009) * n - ((n : ℤ)^2 + 2009) := by ring
        rw [hkey]
        exact Dvd.dvd.sub (Dvd.intro n rfl) step1
      have hfinal : ((n : ℤ) + 2009) ∣ 2009 * 2010 := by
        have h2009 : ((n : ℤ) + 2009) ∣ 2009 * ((n : ℤ) + 2009) := ⟨2009, by ring⟩
        have hsub : ((n : ℤ) + 2009) ∣ (2009 * ((n : ℤ) + 2009) - 2009 * (n - 1)) := h2009.sub hstep
        have heq : 2009 * ((n : ℤ) + 2009) - 2009 * (n - 1) = 2009 * 2010 := by ring
        rw [heq] at hsub; exact hsub
      have hpos : ((n + 2009 : ℕ) : ℤ) = (n : ℤ) + 2009 := by push_cast; ring
      rw [← hpos] at hfinal
      have hcastN : ((2009 * 2010 : ℕ) : ℤ) = 2009 * 2010 := by norm_cast
      have : ((n + 2009 : ℕ) : ℤ) ∣ ((2009 * 2010 : ℕ) : ℤ) := by rw [hcastN]; exact hfinal
      exact Int.natCast_dvd_natCast.mp this
    -- Now n + 2008 is a divisor of 2008 * 2009 that is ≥ 2009, and
    --   n + 2009 is a divisor of 2009 * 2010 that is ≥ 2010.
    have hnle1 : n + 2008 ≤ 2008 * 2009 := Nat.le_of_dvd (by norm_num) hd1
    -- We enumerate divisors d of 2008*2009 = 4034072 ≥ 2009 with (d+1) | 2009*2010.
    -- The only such is d = 2009, corresponding to n = 1.
    -- We prove this by checking d = n + 2008 is one of the 24 specific divisors, and among those,
    -- only d = 2009 has (d+1) | 2009*2010.
    have hn2008 : n + 2008 ∈ (Nat.divisors (2008 * 2009)) := by
      rw [Nat.mem_divisors]; exact ⟨hd1, by norm_num⟩
    have hn2009_dvd : (n + 2009) ∣ 2009 * 2010 := hd2
    -- We will case-split on n + 2008.
    -- Divisors of 2008*2009 ≥ 2009:
    --   2009, 2296, 3514, 4018, 7028, 8036, 10291, 12299, 14056, 16072, 20582, 24598, 41164,
    --   49196, 72037, 82328, 98392, 144074, 288148, 504259, 576296, 1008518, 2017036, 4034072.
    -- For each, check if (d + 1) | 2009*2010.
    -- Use: d = n + 2008, hd2 says (d+1) | 2009*2010.
    -- Approach: the set of divisors of 2008*2009 is finite and decidable; we compute the filter.
    -- Reduce to a decidable finite check: enumerate divisors d of 2008*2009, check
    -- whether d ≥ 2009 ∧ (d+1) ∣ 2009*2010 implies d = 2009.
    have key : ∀ d ∈ Nat.divisors (2008 * 2009),
        2009 ≤ d → (d + 1) ∣ 2009 * 2010 → d = 2009 := by
      native_decide
    have hmem : n + 2008 ∈ Nat.divisors (2008 * 2009) := by
      rw [Nat.mem_divisors]; exact ⟨hd1, by norm_num⟩
    have hdvd : (n + 2008 + 1) ∣ 2009 * 2010 := by
      have hrw : n + 2008 + 1 = n + 2009 := by ring
      rw [hrw]; exact hd2
    have : n + 2008 = 2009 := key (n + 2008) hmem (by omega) hdvd
    omega
  · rintro rfl
    refine ⟨by norm_num, ?_, ?_⟩ <;> decide

end UK2009R1P4
