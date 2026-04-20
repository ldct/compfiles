/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2006, Round 1, Problem 1

Let n be an integer greater than 6. Prove that if n − 1 and n + 1 are both
prime, then n²(n² + 16) is divisible by 720. Is the converse true?

(The converse is false; we state both directions, with the converse negated.)
-/

namespace UK2006R1P1

problem uk2006_r1_p1_forward :
    ∀ n : ℕ, 6 < n → Nat.Prime (n - 1) → Nat.Prime (n + 1) →
      720 ∣ n^2 * (n^2 + 16) := by
  intro n hn hp1 hp2
  -- Since n > 6 and n-1, n+1 both prime, neither equals 2,3,5. So 2,3,5 ∤ (n-1) and ∤ (n+1).
  -- Hence 2 | n (i.e. n even), 3 | n, 5 | n. So 30 | n.
  -- Then n² is a multiple of 900. Plus n²+16 ≡ 16 (mod n) so structure:
  -- n = 30k, n² = 900k², n²+16 = 900k²+16 = 4(225k²+4). Product n²(n²+16) = 3600 k² (225k²+4).
  -- 3600 / 720 = 5, so 720 | n²(n²+16). We need an extra factor; actually 3600k² is already divisible
  -- by 720 (since 3600 = 720 · 5). So done.
  have hn1 : 7 ≤ n := hn
  have hn_ge_8 : 8 ≤ n := by
    -- n - 1 is prime; if n = 7, n-1 = 6 not prime.
    rcases eq_or_lt_of_le hn1 with h7 | h8
    · exfalso; rw [← h7] at hp1; norm_num at hp1
    · omega
  -- n+1 ≥ 9. But n+1 must be prime, and primes ≥ 5 are not divisible by 2,3,5.
  have hn1_ge : n - 1 ≥ 7 := by omega
  have hn2_ge : n + 1 ≥ 9 := by omega
  -- n - 1 ≥ 7 is prime, so n - 1 coprime to 2,3,5.
  have h2_ndvd_n1 : ¬ (2 ∣ n - 1) := by
    intro h
    have : 2 = n - 1 := by
      have := (Nat.prime_def_lt.mp hp1).2 2 (by omega) h
      omega
    omega
  have h2_ndvd_n2 : ¬ (2 ∣ n + 1) := by
    intro h
    have : 2 = n + 1 := by
      have := (Nat.prime_def_lt.mp hp2).2 2 (by omega) h
      omega
    omega
  have h2_dvd : 2 ∣ n := by omega
  have h3_ndvd_n1 : ¬ (3 ∣ n - 1) := by
    intro h
    have : 3 = n - 1 := by
      have := (Nat.prime_def_lt.mp hp1).2 3 (by omega) h
      omega
    omega
  have h3_ndvd_n2 : ¬ (3 ∣ n + 1) := by
    intro h
    have : 3 = n + 1 := by
      have := (Nat.prime_def_lt.mp hp2).2 3 (by omega) h
      omega
    omega
  have h3_dvd : 3 ∣ n := by
    -- Of n-1, n, n+1, one is divisible by 3.
    have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases this with hh | hh | hh
    · exact Nat.dvd_of_mod_eq_zero hh
    · -- n % 3 = 1 → n+1 - wait, n % 3 = 1 → (n+1) % 3 = 2. Then (n-1) % 3 = 0, so 3 | n-1, contradiction.
      exfalso; apply h3_ndvd_n1; omega
    · -- n % 3 = 2 → n+1 % 3 = 0.
      exfalso; apply h3_ndvd_n2; omega
  have h5_ndvd_n1 : ¬ (5 ∣ n - 1) := by
    intro h
    have : 5 = n - 1 := by
      have := (Nat.prime_def_lt.mp hp1).2 5 (by omega) h
      omega
    omega
  have h5_ndvd_n2 : ¬ (5 ∣ n + 1) := by
    intro h
    have : 5 = n + 1 := by
      have := (Nat.prime_def_lt.mp hp2).2 5 (by omega) h
      omega
    omega
  -- 6 ∣ n.
  have h6_dvd : 6 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 2 3) h2_dvd h3_dvd
  -- 5 ∣ n²(n²+16).
  have h5_dvd_prod : 5 ∣ n^2 * (n^2 + 16) := by
    -- Work modulo 5.
    have : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
    rcases this with h | h | h | h | h
    · have h5n : 5 ∣ n := Nat.dvd_of_mod_eq_zero h
      exact dvd_mul_of_dvd_left (dvd_pow h5n (by norm_num)) _
    · exfalso; apply h5_ndvd_n1; omega
    · -- n ≡ 2 mod 5 → n²+16 ≡ 4+16 = 20 ≡ 0 mod 5.
      apply dvd_mul_of_dvd_right
      have : (n^2 + 16) % 5 = 0 := by
        have h1 : n^2 % 5 = 4 := by
          have : n^2 % 5 = (n%5 * (n%5)) % 5 := by rw [sq, Nat.mul_mod]
          rw [this, h]
        omega
      exact Nat.dvd_of_mod_eq_zero this
    · apply dvd_mul_of_dvd_right
      have : (n^2 + 16) % 5 = 0 := by
        have h1 : n^2 % 5 = 4 := by
          have : n^2 % 5 = (n%5 * (n%5)) % 5 := by rw [sq, Nat.mul_mod]
          rw [this, h]
        omega
      exact Nat.dvd_of_mod_eq_zero this
    · exfalso; apply h5_ndvd_n2; omega
  -- 144 ∣ n²(n²+16) since 6 | n.
  obtain ⟨k, hk⟩ := h6_dvd
  have h144_dvd : 144 ∣ n^2 * (n^2 + 16) := by
    subst hk
    have : (6 * k)^2 * ((6 * k)^2 + 16) = 144 * (k^2 * (9 * k^2 + 4)) := by ring
    rw [this]
    exact Dvd.intro _ rfl
  -- Combine: 720 = 144 · 5, gcd(144, 5) = 1.
  have : (720 : ℕ) = 144 * 5 := by norm_num
  rw [this]
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 144 5) h144_dvd h5_dvd_prod

/-- The converse is false: there exists n > 6 with 720 ∣ n²(n² + 16) but
    either n − 1 or n + 1 is not prime. -/
problem uk2006_r1_p1_converse_false :
    ∃ n : ℕ, 6 < n ∧ 720 ∣ n^2 * (n^2 + 16) ∧
      ¬ (Nat.Prime (n - 1) ∧ Nat.Prime (n + 1)) := by
  -- n = 90: n² = 8100, n²+16 = 8116, product = 65739600. 65739600 / 720 = 91305.
  -- n-1 = 89 (prime), n+1 = 91 = 7·13 (not prime).
  refine ⟨90, by norm_num, ?_, ?_⟩
  · decide
  · intro ⟨_, h⟩
    exact absurd h (by decide)

end UK2006R1P1
