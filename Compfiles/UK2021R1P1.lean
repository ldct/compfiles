/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2021, Round 1, Problem 1

Alice and Bob take it in turns to write numbers on a blackboard.
Alice starts by writing an integer a between −100 and 100 inclusive.
On each of Bob's turns he writes twice the number Alice wrote last.
On each of Alice's subsequent turns she writes the number 45 less
than the number Bob wrote last. At some point, the number a is
written on the board for a second time. Find the possible values of a.
-/

namespace UK2021R1P1

determine solution_set : Set ℤ := { 0, 30, 42, 45 }

/-- The sequence of numbers on the board: position 0 is Alice's initial
    value a, odd positions are Bob's (twice the previous), and even
    positions after 0 are Alice's (45 less than the previous). -/
def seqValue (a : ℤ) : ℕ → ℤ
  | 0 => a
  | n + 1 => if (n + 1) % 2 = 1 then 2 * seqValue a n else seqValue a n - 45

/-- Closed form: for k ≥ 0, seqValue a (2k) = 2^k · a − 45·(2^k − 1). -/
lemma seqValue_even (a : ℤ) (k : ℕ) :
    seqValue a (2 * k) = 2^k * a - 45 * (2^k - 1) := by
  induction k with
  | zero => simp [seqValue]
  | succ n ih =>
    -- 2 * (n+1) = 2*n + 2. seqValue a (2n+2) = seqValue a (2n+1) - 45.
    -- seqValue a (2n+1) = 2 * seqValue a (2n).
    have h1 : seqValue a (2 * n + 1) = 2 * seqValue a (2 * n) := by
      show (if (2 * n + 1) % 2 = 1 then 2 * seqValue a (2 * n) else seqValue a (2 * n) - 45)
        = 2 * seqValue a (2 * n)
      have : (2 * n + 1) % 2 = 1 := by omega
      rw [if_pos this]
    have h2 : seqValue a (2 * (n + 1)) = seqValue a (2 * n + 1) - 45 := by
      have hsuc : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      rw [hsuc]
      show (if (2 * n + 1 + 1) % 2 = 1 then 2 * seqValue a (2 * n + 1)
            else seqValue a (2 * n + 1) - 45) = seqValue a (2 * n + 1) - 45
      have : (2 * n + 1 + 1) % 2 ≠ 1 := by omega
      rw [if_neg this]
    rw [h2, h1, ih]
    ring

lemma seqValue_odd (a : ℤ) (k : ℕ) :
    seqValue a (2 * k + 1) = 2^(k+1) * a - 45 * (2^(k+1) - 2) := by
  have h1 : seqValue a (2 * k + 1) = 2 * seqValue a (2 * k) := by
    show (if (2 * k + 1) % 2 = 1 then 2 * seqValue a (2 * k) else seqValue a (2 * k) - 45)
      = 2 * seqValue a (2 * k)
    have : (2 * k + 1) % 2 = 1 := by omega
    rw [if_pos this]
  rw [h1, seqValue_even]
  ring

problem uk2021_r1_p1 :
    { a : ℤ | -100 ≤ a ∧ a ≤ 100 ∧
      ∃ n, 0 < n ∧ seqValue a n = a } = solution_set := by
  ext a
  simp only [Set.mem_setOf_eq, solution_set, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hal, hau, n, hn, hseq⟩
    -- Split on parity of n.
    by_cases hpar : Even n
    · -- n = 2k, k ≥ 1.
      obtain ⟨k, hk⟩ := hpar
      have hk_eq : n = 2 * k := by omega
      rw [hk_eq] at hseq
      have hk_pos : 0 < k := by omega
      rw [seqValue_even] at hseq
      -- 2^k · a - 45·(2^k - 1) = a ⟹ (2^k - 1)·(a - 45) = 0.
      have : ((2 : ℤ)^k - 1) * (a - 45) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exfalso
        have : (2 : ℤ)^k = 1 := by linarith
        have : (2 : ℤ)^k > 1 := by
          have : (1 : ℤ) < 2 := by norm_num
          exact one_lt_pow₀ this (by omega)
        omega
      · -- a = 45
        right; right; right; linarith
    · -- n = 2k + 1, k ≥ 0.
      rw [Nat.not_even_iff_odd] at hpar
      obtain ⟨k, hk⟩ := hpar
      have hk_eq : n = 2 * k + 1 := by omega
      rw [hk_eq] at hseq
      rw [seqValue_odd] at hseq
      -- 2^(k+1) · a - 45·(2^(k+1) - 2) = a ⟹ (2^(k+1) - 1)·(45 - a) = 45.
      have hfac : ((2 : ℤ)^(k+1) - 1) * (45 - a) = 45 := by linarith
      -- 2^(k+1) - 1 ≥ 1 and divides 45.
      have hpow_ge : (1 : ℤ) ≤ (2 : ℤ)^(k+1) - 1 := by
        have : (2 : ℤ)^(k+1) ≥ 2 := by
          calc (2 : ℤ)^(k+1) ≥ 2^1 := by
                  apply pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (by omega)
            _ = 2 := by norm_num
        linarith
      -- (2^(k+1) - 1) divides 45 in ℤ.
      have hdvd : ((2 : ℤ)^(k+1) - 1) ∣ 45 := ⟨45 - a, hfac.symm⟩
      -- And 45 - a must also equal 45 / (2^(k+1) - 1), and must be positive.
      have h45a_pos : 0 < 45 - a := by
        by_contra h
        rw [not_lt] at h
        have : ((2 : ℤ)^(k+1) - 1) * (45 - a) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) h
        linarith
      -- a ≤ 44 from h45a_pos.
      have ha_le44 : a ≤ 44 := by linarith
      -- (2^(k+1) - 1) ≤ 45 since it divides 45.
      have hpow_le : (2 : ℤ)^(k+1) - 1 ≤ 45 := Int.le_of_dvd (by norm_num) hdvd
      -- So 2^(k+1) ≤ 46.
      have hpow_le2 : (2 : ℤ)^(k+1) ≤ 46 := by linarith
      -- So k + 1 ≤ 5 (since 2^6 = 64 > 46).
      have hk_le : k ≤ 4 := by
        by_contra hc
        rw [not_le] at hc
        have h2p : (2 : ℤ)^(k+1) ≥ (2 : ℤ)^6 := by
          apply pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
          omega
        have h64 : (2 : ℤ)^6 = 64 := by norm_num
        linarith
      -- k ∈ {0, 1, 2, 3, 4}. Check each.
      interval_cases k
      · -- k = 0: 2^1 - 1 = 1. hfac: 1 · (45 - a) = 45 ⟹ a = 0.
        left
        have : (2 : ℤ)^(0+1) - 1 = 1 := by norm_num
        rw [this] at hfac
        linarith
      · -- k = 1: 2^2 - 1 = 3. 3·(45-a) = 45 ⟹ 45-a = 15 ⟹ a = 30.
        right; left
        have : (2 : ℤ)^(1+1) - 1 = 3 := by norm_num
        rw [this] at hfac
        linarith
      · -- k = 2: 2^3 - 1 = 7. 7·(45-a) = 45. 45/7 not integer: (45 - a) = 45/7, contradiction.
        exfalso
        have : (2 : ℤ)^(2+1) - 1 = 7 := by norm_num
        rw [this] at hfac
        omega
      · -- k = 3: 2^4 - 1 = 15. 15·(45-a) = 45 ⟹ 45-a = 3 ⟹ a = 42.
        right; right; left
        have : (2 : ℤ)^(3+1) - 1 = 15 := by norm_num
        rw [this] at hfac
        linarith
      · -- k = 4: 2^5 - 1 = 31. 31·(45-a) = 45. 45/31 not integer.
        exfalso
        have : (2 : ℤ)^(4+1) - 1 = 31 := by norm_num
        rw [this] at hfac
        omega
  · rintro (rfl | rfl | rfl | rfl)
    · -- a = 0. n = 1 works: seqValue 0 1 = 2·0 = 0.
      refine ⟨by norm_num, by norm_num, 1, by norm_num, ?_⟩
      show (if 1 % 2 = 1 then 2 * seqValue 0 0 else seqValue 0 0 - 45) = 0
      simp [seqValue]
    · -- a = 30. n = 3: seqValue 30 3 = 4·30 - 90 = 30.
      refine ⟨by norm_num, by norm_num, 3, by norm_num, ?_⟩
      have : seqValue 30 3 = 2^(1+1) * 30 - 45 * (2^(1+1) - 2) := seqValue_odd 30 1
      rw [this]; norm_num
    · -- a = 42. n = 7: seqValue 42 7 = 16·42 - 45·14 = 672 - 630 = 42.
      refine ⟨by norm_num, by norm_num, 7, by norm_num, ?_⟩
      have : seqValue 42 7 = 2^(3+1) * 42 - 45 * (2^(3+1) - 2) := seqValue_odd 42 3
      rw [this]; norm_num
    · -- a = 45. n = 2: seqValue 45 2 = 2·45 - 45 = 45.
      refine ⟨by norm_num, by norm_num, 2, by norm_num, ?_⟩
      have : seqValue 45 2 = 2^1 * 45 - 45 * (2^1 - 1) := seqValue_even 45 1
      rw [this]; norm_num

end UK2021R1P1
