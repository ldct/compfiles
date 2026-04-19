/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2024, Round 1, Problem 4

Find all positive integers n such that n × 2ⁿ + 1 is a square.

The answer is n = 2 and n = 3.
-/

namespace UK2024R1P4

determine SolutionSet : Set ℕ := {2, 3}

snip begin

/-- For n ≥ 5, n + 1 < 2^(n-2). -/
lemma two_pow_sub_two_gt (n : ℕ) (hn : 5 ≤ n) : n + 1 < 2 ^ (n - 2) := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have h : k + 1 - 2 = (k - 2) + 1 := by omega
    rw [h, pow_succ]
    omega

/-- The main lemma: for n ≥ 5, n·2ⁿ + 1 is not a perfect square. -/
lemma not_square_ge_five (n : ℕ) (hn : 5 ≤ n) : ¬ IsSquare (n * 2 ^ n + 1) := by
  rintro ⟨k, hk⟩
  -- hk : n * 2^n + 1 = k * k
  -- Step 1: extract n = (n-2) + 2 to write 2^n = 4 * 2^(n-2)
  have hn2 : 2 ^ n = 4 * 2 ^ (n - 2) := by
    conv_lhs => rw [show n = (n - 2) + 2 from by omega]
    rw [pow_add]; ring
  -- Step 2: 2^(n-2) > n + 1
  have hpow : n + 1 < 2 ^ (n - 2) := two_pow_sub_two_gt n hn
  -- Step 3: k * k is odd, hence k is odd, so k = 2*m+1 for some m
  have h_kk : k * k = n * 2 ^ n + 1 := hk.symm
  have h_k_odd : k % 2 = 1 := by
    have h_even : 2 ∣ n * 2 ^ n := by
      have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega : n ≠ 0)
      exact h2n.mul_left _
    have h_kk_odd : k * k % 2 = 1 := by
      rw [h_kk]
      obtain ⟨c, hc⟩ := h_even
      omega
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · exfalso
      have : (k * k) % 2 = 0 := by
        rw [Nat.mul_mod, h]
      omega
    · exact h
  obtain ⟨m, hm⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
  -- Step 4: from hk and hm, derive m*(m+1) = n * 2^(n-2)
  have h_main : m * (m + 1) = n * 2 ^ (n - 2) := by
    have h1 : 4 * (m * (m + 1)) + 1 = n * 2 ^ n + 1 := by
      have : k * k = 4 * (m * (m + 1)) + 1 := by rw [hm]; ring
      omega
    have h2 : 4 * (m * (m + 1)) = n * 2 ^ n := by omega
    rw [hn2] at h2
    have h3 : 4 * (m * (m + 1)) = 4 * (n * 2 ^ (n - 2)) := by linarith
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4) h3
  -- Step 5: m and m+1 are coprime, exactly one is even
  -- so 2^(n-2) divides whichever of m, m+1 is even
  have h_cop : Nat.Coprime m (m + 1) := by
    rw [Nat.coprime_self_add_right]; exact Nat.coprime_one_right _
  -- 2^(n-2) divides m * (m+1)
  have h_dvd : 2 ^ (n - 2) ∣ m * (m + 1) := ⟨n, by rw [h_main]; ring⟩
  -- Case split on parity of m
  have h_le : 2 ^ (n - 2) ≤ m + 1 := by
    rcases Nat.even_or_odd m with he | ho
    · -- m even, m+1 odd, so gcd(2^(n-2), m+1) = 1, hence 2^(n-2) | m
      have h_m1_odd : ¬ 2 ∣ (m + 1) := by
        rcases he with ⟨t, ht⟩
        rw [ht]; omega
      have h_m1_odd' : Odd (m + 1) := by
        rcases Nat.mod_two_eq_zero_or_one (m + 1) with h0 | h1
        · exfalso; apply h_m1_odd; omega
        · exact Nat.odd_iff.mpr h1
      have h_cop' : Nat.Coprime (2 ^ (n - 2)) (m + 1) :=
        (Nat.coprime_two_left.mpr h_m1_odd').pow_left _
      have h_dvd_m : 2 ^ (n - 2) ∣ m := h_cop'.dvd_of_dvd_mul_right h_dvd
      -- so m ≥ 2^(n-2) (m must be > 0 because m * (m+1) = n * 2^(n-2) > 0)
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · exfalso; subst h
          simp at h_main
          have : 0 < n * 2 ^ (n - 2) := by positivity
          omega
        · exact h
      have : 2 ^ (n - 2) ≤ m := Nat.le_of_dvd hm_pos h_dvd_m
      omega
    · -- m odd, m+1 even, so gcd(2^(n-2), m) = 1, hence 2^(n-2) | (m+1)
      have h_cop' : Nat.Coprime (2 ^ (n - 2)) m :=
        (Nat.coprime_two_left.mpr ho).pow_left _
      have h_dvd' : 2 ^ (n - 2) ∣ (m + 1) * m := by rw [Nat.mul_comm]; exact h_dvd
      have h_dvd_m1 : 2 ^ (n - 2) ∣ (m + 1) := h_cop'.dvd_of_dvd_mul_right h_dvd'
      exact Nat.le_of_dvd (by omega) h_dvd_m1
  -- Step 6: derive contradiction
  -- We have 2^(n-2) ≤ m+1 and m*(m+1) = n*2^(n-2)
  -- So m*(m+1) ≥ m * 2^(n-2) ≥ ((2^(n-2)) - 1) * 2^(n-2) (since m ≥ 2^(n-2) - 1)
  -- But m*(m+1) = n * 2^(n-2)
  -- So (2^(n-2) - 1) ≤ n, contradicting 2^(n-2) > n + 1
  have hm_ge : 2 ^ (n - 2) - 1 ≤ m := by omega
  have hpow_pos : 0 < 2 ^ (n - 2) := pow_pos (by norm_num) _
  have h_lb : (2 ^ (n - 2) - 1) * 2 ^ (n - 2) ≤ m * (m + 1) := by
    apply Nat.mul_le_mul hm_ge h_le
  rw [h_main] at h_lb
  -- Now: (2^(n-2) - 1) * 2^(n-2) ≤ n * 2^(n-2)
  -- Cancel 2^(n-2): 2^(n-2) - 1 ≤ n
  have h_cancel : 2 ^ (n - 2) - 1 ≤ n := by
    have := Nat.le_of_mul_le_mul_right h_lb hpow_pos
    exact this
  omega

snip end

problem uk2024_r1_p4 (n : ℕ) (hn : 0 < n) :
    n ∈ SolutionSet ↔ IsSquare (n * 2 ^ n + 1) := by
  constructor
  · rintro (rfl | rfl)
    · exact ⟨3, by norm_num⟩
    · exact ⟨5, by norm_num⟩
  · intro hsq
    by_cases h5 : 5 ≤ n
    · exact absurd hsq (not_square_ge_five n h5)
    · push Not at h5
      interval_cases n
      · exfalso
        obtain ⟨k, hk⟩ := hsq
        -- k * k = 3
        have hk3 : k * k = 3 := by simpa using hk.symm
        have hk_le : k ≤ 1 := by nlinarith
        interval_cases k <;> omega
      · left; rfl
      · right; rfl
      · exfalso
        obtain ⟨k, hk⟩ := hsq
        -- k * k = 65
        have hk65 : k * k = 65 := by simpa using hk.symm
        have hk_le : k ≤ 8 := by nlinarith
        have hk_ge : 9 ≤ k * k + 16 := by omega
        interval_cases k <;> omega

end UK2024R1P4
