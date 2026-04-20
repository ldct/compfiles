/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2015, Round 1, Problem 2

Positive integers p, a and b satisfy the equation p² + a² = b². Prove that if
p is a prime greater than 3, then a is a multiple of 12 and 2(p + a + 1) is a
perfect square.
-/

namespace UK2015R1P2

problem uk2015_r1_p2 :
    ∀ p a b : ℕ, 0 < p → 0 < a → 0 < b → p.Prime → 3 < p →
      p^2 + a^2 = b^2 →
      12 ∣ a ∧ ∃ k : ℕ, 2 * (p + a + 1) = k^2 := by
  intro p a b hp0 ha0 hb0 hpp hp3 heq
  -- From p² = (b-a)(b+a) with p prime and b > a (else b² ≤ a² < p²+a²), we get b-a = 1, b+a = p².
  -- Work in ℤ to avoid Nat subtraction issues.
  have hba : a < b := by
    have hab2 : a^2 < b^2 := by
      have : p^2 > 0 := pow_pos hp0 2
      omega
    by_contra hle
    have hle : b ≤ a := le_of_not_gt hle
    have : b^2 ≤ a^2 := Nat.pow_le_pow_left hle 2
    omega
  have hfac : (b - a) * (b + a) = p^2 := by
    have : b^2 - a^2 = p^2 := by omega
    have hba_le : a ≤ b := le_of_lt hba
    have : b * b - a * a = p * p := by
      have := this
      rw [show b^2 = b * b from by ring, show a^2 = a * a from by ring, show p^2 = p * p from by ring] at this
      exact this
    nlinarith [Nat.sub_add_cancel hba_le, this]
  -- b - a divides p². p prime, so b - a ∈ {1, p, p²}.
  have hdvd : (b - a) ∣ p^2 := ⟨b + a, hfac.symm⟩
  have hp2_dvd := (Nat.dvd_prime_pow hpp).mp hdvd
  obtain ⟨i, hile, hi⟩ := hp2_dvd
  -- b + a > 0 and b + a > b - a (since a > 0), so b - a < p (the square root of p²). Hmm actually
  -- more directly: b - a ≥ 1 and (b-a)(b+a) = p², and b-a < b+a. So b-a < p.
  -- Actually b-a and b+a have the same parity; their product is p² odd (p odd prime). So both odd.
  -- The factorizations of p² with first ≤ second: (1, p²) or (p, p).
  -- But b - a < b + a (strict, since a > 0), so (b-a, b+a) ≠ (p, p). Hence b-a=1, b+a=p².
  have hba_lt : b - a < b + a := by omega
  have hba_sq : b - a = 1 := by
    -- i can only be 0, 1, or 2. If i=1, b-a=p and b+a=p, contradicting strict.
    -- If i=2, b-a=p² and b+a=1, impossible since b+a ≥ 2.
    interval_cases i
    · simpa using hi
    · -- b - a = p, then b + a = p from (b-a)(b+a)=p². Contradicts strict.
      exfalso
      have hba_eq : b - a = p := by simpa using hi
      have hpa_eq : b + a = p := by
        have hp_pos : 0 < p := hp0
        have hfac' : (b - a) * (b + a) = p * p := by rw [hfac]; ring
        rw [hba_eq] at hfac'
        exact Nat.eq_of_mul_eq_mul_left hp_pos hfac'
      omega
    · exfalso
      have hsq : b - a = p^2 := by simpa using hi
      have hba_eq : b + a = 1 := by
        have hfac' : p^2 * (b + a) = p^2 * 1 := by
          rw [mul_one]
          have : (b - a) * (b + a) = p^2 := hfac
          rw [hsq] at this
          linarith
        have hp_pos : 0 < p^2 := pow_pos hp0 2
        exact Nat.eq_of_mul_eq_mul_left hp_pos hfac'
      omega
  have hba_add : b + a = p^2 := by
    have := hfac
    rw [hba_sq] at this; omega
  -- So 2a = b + a - (b - a) = p² - 1.
  have h2a : 2 * a = p^2 - 1 := by omega
  -- Now prove 12 ∣ a. We have 2a = (p-1)(p+1). Since p odd prime ≥ 5, p-1 and p+1 even.
  have hpp5 : 5 ≤ p := by
    -- p > 3 and prime, so p ≥ 5 (since 4 not prime).
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hp3) with h4 | h4
    · exfalso; rw [← h4] at hpp; exact absurd hpp (by decide)
    · omega
  -- 24 | p²-1 when p coprime to 6 (standard fact; we'll just prove it directly).
  -- p mod 12 ∈ {1, 5, 7, 11} since p coprime to 2, 3. In all cases p² ≡ 1 mod 24.
  have hp_mod_12 : p % 12 = 1 ∨ p % 12 = 5 ∨ p % 12 = 7 ∨ p % 12 = 11 := by
    -- p not divisible by 2 or 3.
    have hp_not_2 : ¬ (2 ∣ p) := by
      intro h
      rcases hpp.eq_one_or_self_of_dvd 2 h with h | h
      · omega
      · omega
    have hp_not_3 : ¬ (3 ∣ p) := by
      intro h
      rcases hpp.eq_one_or_self_of_dvd 3 h with h | h
      · omega
      · omega
    omega
  have h24 : 24 ∣ p^2 - 1 := by
    have hsq_mod : p^2 % 24 = 1 := by
      have hp_sq : p^2 % 24 = (p % 24) * (p % 24) % 24 := by rw [sq, Nat.mul_mod]
      have hp24 : p % 24 ∈ Finset.range 24 := by simp; omega
      -- Split into 24 cases on p % 24, but narrow by p % 12 ∈ {1,5,7,11}.
      have : p % 24 % 12 = p % 12 := Nat.mod_mod_of_dvd _ (by norm_num : (12 : ℕ) ∣ 24)
      -- Given p%12 ∈ {1,5,7,11}, p%24 ∈ {1,5,7,11,13,17,19,23}.
      have h_mod24 : p % 24 = 1 ∨ p % 24 = 5 ∨ p % 24 = 7 ∨ p % 24 = 11 ∨
                     p % 24 = 13 ∨ p % 24 = 17 ∨ p % 24 = 19 ∨ p % 24 = 23 := by
        rcases hp_mod_12 with h | h | h | h <;> omega
      rcases h_mod24 with h | h | h | h | h | h | h | h <;>
        (rw [hp_sq, h])
    omega
  -- Hence 24 | 2a, so 12 | a.
  have h12a : 12 ∣ a := by
    have : 24 ∣ 2 * a := by rw [h2a]; exact h24
    omega
  refine ⟨h12a, ?_⟩
  -- 2(p + a + 1) = p² + 2p + 1 = (p+1)².
  refine ⟨p + 1, ?_⟩
  have hp1_sq : (p + 1)^2 = p^2 + 2*p + 1 := by ring
  rw [hp1_sq]
  -- 2 * (p + a + 1) = 2p + 2a + 2 = 2p + (p²-1) + 2 = p² + 2p + 1.
  have : 2 * (p + a + 1) = 2 * p + 2 * a + 2 := by ring
  rw [this, h2a]
  have hp2_ge : 1 ≤ p^2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega

end UK2015R1P2
