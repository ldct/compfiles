/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2005, Round 1, Problem 1

Each of Paul and Jenny has a whole number of pounds. He says to her:
"If you give me £3, I will have n times as much as you". She says to him:
"If you give me £n, I will have 3 times as much as you". Given that all these
statements are true and that n is a positive integer, what are the possible
values for n?

The answer is n ∈ {1, 2, 3, 7}.
-/

namespace UK2005R1P1

determine solution_set : Set ℕ := {1, 2, 3, 7}

problem uk2005_r1_p1 (n : ℕ) :
    n ∈ solution_set ↔
      0 < n ∧ ∃ p j : ℕ, 3 ≤ j ∧ n ≤ p ∧
        p + 3 = n * (j - 3) ∧ j + n = 3 * (p - n) := by
  constructor
  · intro hn
    simp only [solution_set, Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · refine ⟨by norm_num, 5, 11, by decide, by decide, by decide, by decide⟩
    · refine ⟨by norm_num, 5, 7, by decide, by decide, by decide, by decide⟩
    · refine ⟨by norm_num, 6, 6, by decide, by decide, by decide, by decide⟩
    · refine ⟨by norm_num, 11, 5, by decide, by decide, by decide, by decide⟩
  · rintro ⟨hn, p, j, hj3, hpn, h1, h2⟩
    -- Derive: (3n-1) * j = 13n + 9 in ℤ
    have hj3' : ((j - 3 : ℕ) : ℤ) = (j : ℤ) - 3 := by
      rw [Nat.cast_sub hj3]; norm_num
    have hpn' : ((p - n : ℕ) : ℤ) = (p : ℤ) - n := by
      rw [Nat.cast_sub hpn]
    have h1' : (p : ℤ) + 3 = n * ((j : ℤ) - 3) := by
      have := h1
      have hc : ((p + 3 : ℕ) : ℤ) = ((n * (j - 3) : ℕ) : ℤ) := by exact_mod_cast this
      push_cast at hc
      rw [hj3'] at hc
      linarith
    have h2' : (j : ℤ) + n = 3 * ((p : ℤ) - n) := by
      have := h2
      have hc : ((j + n : ℕ) : ℤ) = ((3 * (p - n) : ℕ) : ℤ) := by exact_mod_cast this
      push_cast at hc
      rw [hpn'] at hc
      linarith
    -- From h1': p = n*j - 3n - 3. Substitute into h2':
    -- j + n = 3*(n*j - 3n - 3) - 3n = 3nj - 12n - 9
    -- So j(3n - 1) = 13n + 9
    have hkey : ((j : ℤ)) * (3 * n - 1) = 13 * n + 9 := by linarith
    -- Since n ≥ 1, 3n - 1 ≥ 2 > 0.
    have hn_pos : 1 ≤ n := hn
    have h3n1_pos : (0 : ℤ) < 3 * n - 1 := by
      have : (1 : ℤ) ≤ n := by exact_mod_cast hn_pos
      linarith
    -- So j = (13n + 9)/(3n-1). For n ≥ 8: 13n+9 < 5(3n-1) = 15n-5 requires 2n > 14, n > 7.
    -- And 13n + 9 > 4(3n-1) = 12n - 4 requires n > -13, always true for n > 0.
    -- So for n ≥ 8, j·(3n-1) = 13n+9 has no integer j solution.
    have hn_le : n ≤ 7 := by
      by_contra hlt
      push Not at hlt
      -- n ≥ 8
      have h8 : (8 : ℤ) ≤ n := by exact_mod_cast hlt
      -- Show j < 5 and j > 4 in integers → contradiction
      have hj_lt : (j : ℤ) < 5 := by
        -- j * (3n-1) = 13n+9 < 5(3n-1) for n ≥ 8
        have hh : (13 : ℤ) * n + 9 < 5 * (3 * n - 1) := by linarith
        rw [← hkey] at hh
        exact (mul_lt_mul_iff_of_pos_right h3n1_pos).mp hh
      have hj_gt : (4 : ℤ) < j := by
        -- j * (3n-1) = 13n+9 > 4(3n-1) always for n ≥ 1
        have hh : (4 : ℤ) * (3 * n - 1) < 13 * n + 9 := by linarith
        rw [← hkey] at hh
        exact (mul_lt_mul_iff_of_pos_right h3n1_pos).mp hh
      -- j is a natural number with 4 < j < 5, contradiction
      have : (j : ℤ) = 5 ∨ (j : ℤ) ≤ 4 := by omega
      omega
    -- Now interval check n ∈ {1..7}
    interval_cases n
    · left; rfl
    · right; left; rfl
    · right; right; left; rfl
    · -- n = 4: j*(11) = 61, no integer j
      exfalso
      have hk : (j : ℤ) * 11 = 61 := by
        have := hkey
        push_cast at this
        linarith
      omega
    · -- n = 5
      exfalso
      have hk : (j : ℤ) * 14 = 74 := by
        have := hkey
        push_cast at this
        linarith
      omega
    · -- n = 6
      exfalso
      have hk : (j : ℤ) * 17 = 87 := by
        have := hkey
        push_cast at this
        linarith
      omega
    · right; right; right; rfl

end UK2005R1P1
