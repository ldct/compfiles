/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2008, Round 2, Problem 4

Prove that there are infinitely many pairs of distinct positive integers x, y
such that x³ + y² divides x² + y³.
-/

namespace UK2008R2P4

/-- For each k ≥ 2, let x = k⁵ − k² − 1 and y = k·x. Then
    x³ + y² = x²(x + k²) = x²(k⁵ − 1) and
    x² + y³ = x²(1 + k³x) = x²(k⁵ − 1)(k³ − 1). -/
def X (k : ℕ) : ℕ := (k + 2)^5 - (k + 2)^2 - 1

lemma key_le (k : ℕ) : (k + 2)^2 + 1 ≤ (k + 2)^5 := by
  have h2 : (k + 2)^2 ≥ 4 := by
    calc (k + 2)^2 ≥ 2^2 := Nat.pow_le_pow_left (by omega) 2
      _ = 4 := by norm_num
  have h3 : (k + 2)^3 ≥ 8 := by
    calc (k + 2)^3 ≥ 2^3 := Nat.pow_le_pow_left (by omega) 3
      _ = 8 := by norm_num
  have h5 : (k + 2)^5 = (k + 2)^2 * (k + 2)^3 := by ring
  nlinarith [h5, h2, h3]

lemma X_pos (k : ℕ) : 0 < X k := by
  unfold X
  have := key_le k
  -- We need (k+2)^5 - (k+2)^2 - 1 > 0, i.e., (k+2)^5 > (k+2)^2 + 1
  -- which is `key_le` plus strictness.
  have h2 : (k + 2)^2 ≥ 4 := by
    calc (k + 2)^2 ≥ 2^2 := Nat.pow_le_pow_left (by omega) 2
      _ = 4 := by norm_num
  have h3 : (k + 2)^3 ≥ 8 := by
    calc (k + 2)^3 ≥ 2^3 := Nat.pow_le_pow_left (by omega) 3
      _ = 8 := by norm_num
  have h5 : (k + 2)^5 = (k + 2)^2 * (k + 2)^3 := by ring
  -- (k+2)^5 ≥ 4 * 8 = 32
  have hbig : (k + 2)^5 ≥ (k + 2)^2 * 8 := by nlinarith [h5, h3]
  omega

lemma X_succ_lt (k : ℕ) : X k < X (k + 1) := by
  -- Direct: show (k+2)^5 - (k+2)^2 - 1 < (k+3)^5 - (k+3)^2 - 1
  unfold X
  have h1 := key_le k
  have h2 := key_le (k + 1)
  -- Show (k + 1 + 2)^5 - (k + 1 + 2)^2 > (k + 2)^5 - (k + 2)^2.
  -- (k+3)^5 - (k+2)^5 is roughly 5(k+2)^4 ≈ big. (k+3)^2 - (k+2)^2 = 2k+5.
  -- Just expand.
  have exp3 : (k + 3 : ℕ) = (k + 1 + 2) := by ring
  rw [exp3]
  have rewrite_it : (k + 1 + 2) = (k + 2) + 1 := by ring
  rw [rewrite_it]
  set a := k + 2 with ha_def
  have ha : 2 ≤ a := by rw [ha_def]; omega
  -- Goal: a^5 - a^2 - 1 < (a + 1)^5 - (a + 1)^2 - 1
  -- i.e., a^5 - a^2 ≤ (a+1)^5 - (a+1)^2 - 1, hence (a+1)^5 - (a+1)^2 ≥ a^5 - a^2 + 1
  -- (a+1)^5 = a^5 + 5a^4 + 10a^3 + 10a^2 + 5a + 1
  -- (a+1)^2 = a^2 + 2a + 1
  -- Difference: ((a+1)^5 - (a+1)^2) - (a^5 - a^2) = 5a^4 + 10a^3 + 10a^2 + 5a + 1 - 2a - 1
  --   = 5a^4 + 10a^3 + 10a^2 + 3a.  For a ≥ 2, this ≥ 5·16 = 80 ≥ 1.
  have hexp1 : (a + 1)^5 = a^5 + 5*a^4 + 10*a^3 + 10*a^2 + 5*a + 1 := by ring
  have hexp2 : (a + 1)^2 = a^2 + 2*a + 1 := by ring
  have h1' : a^2 + 1 ≤ a^5 := by rw [ha_def]; exact key_le k
  have h2' : (a + 1)^2 + 1 ≤ (a + 1)^5 := by
    have hh : (a + 1 : ℕ) = (k + 1) + 2 := by rw [ha_def]
    rw [hh]; exact key_le (k + 1)
  have hbig : 5*a^4 + 10*a^3 + 10*a^2 + 3*a ≥ 1 := by
    have : a^4 ≥ 16 := by
      calc a^4 ≥ 2^4 := Nat.pow_le_pow_left ha 4
        _ = 16 := by norm_num
    nlinarith
  -- Use omega after providing concrete arithmetic
  have HA : (a + 1)^5 = a^5 + 5*a^4 + 10*a^3 + 10*a^2 + 5*a + 1 := hexp1
  have HB : (a + 1)^2 = a^2 + 2*a + 1 := hexp2
  -- a^5 - a^2 - 1 < (a+1)^5 - (a+1)^2 - 1
  -- All three are natural nums; since h2' gives (a+1)^2+1 ≤ (a+1)^5, the subtraction is safe.
  -- (a+1)^5 - (a+1)^2 - 1 - (a^5 - a^2 - 1) = big + positive.
  -- We have: (a+1)^5 = a^5 + Q where Q = 5a^4+10a^3+10a^2+5a+1
  --           (a+1)^2 = a^2 + R where R = 2a + 1
  -- So (a+1)^5 - (a+1)^2 - 1 = a^5 + Q - a^2 - R - 1 = (a^5 - a^2 - 1) + (Q - R)
  -- And Q - R = 5a^4+10a^3+10a^2+3a ≥ 1, so strict increase.
  have Qge : 5*a^4 + 10*a^3 + 10*a^2 + 5*a + 1 ≥ 2*a + 1 + 1 := by nlinarith [hbig]
  omega

lemma X_strictMono : StrictMono X := by
  intro m n hmn
  induction hmn with
  | refl => exact X_succ_lt m
  | step _ ih => exact lt_trans ih (X_succ_lt _)

problem uk2008_r2_p4 :
    ∃ f : ℕ → ℕ × ℕ,
      StrictMono f ∧
      ∀ k, 0 < (f k).1 ∧ 0 < (f k).2 ∧ (f k).1 ≠ (f k).2 ∧
           ((f k).1 ^ 3 + (f k).2 ^ 2) ∣ ((f k).1 ^ 2 + (f k).2 ^ 3) := by
  refine ⟨fun k => (X k, (k + 2) * X k), ?_, ?_⟩
  · intro i j hij
    refine Prod.lt_iff.mpr (Or.inl ⟨X_strictMono hij, ?_⟩)
    have hxi := X_strictMono hij
    have hij' : i + 2 ≤ j + 2 := by omega
    calc (i + 2) * X i ≤ (j + 2) * X i := Nat.mul_le_mul_right _ hij'
      _ ≤ (j + 2) * X j := Nat.mul_le_mul_left _ hxi.le
  · intro k
    show 0 < X k ∧ 0 < (k + 2) * X k ∧ X k ≠ (k + 2) * X k ∧
         (X k)^3 + ((k + 2) * X k)^2 ∣ (X k)^2 + ((k + 2) * X k)^3
    have hk'_pos : 0 < k + 2 := by omega
    have hx_pos : 0 < X k := X_pos k
    have hx_val : X k + (k + 2)^2 + 1 = (k + 2)^5 := by
      unfold X; have := key_le k; omega
    refine ⟨hx_pos, Nat.mul_pos hk'_pos hx_pos, ?_, ?_⟩
    · intro heq
      have h1 : 1 * X k = (k + 2) * X k := by omega
      have := Nat.eq_of_mul_eq_mul_right hx_pos h1
      omega
    · -- Divisibility
      have e1 : (X k)^3 + ((k + 2) * X k)^2 = (X k)^2 * (X k + (k + 2)^2) := by ring
      have e2 : (X k)^2 + ((k + 2) * X k)^3 = (X k)^2 * (1 + (k + 2)^3 * X k) := by ring
      rw [e1, e2]
      apply Nat.mul_dvd_mul_left
      use (k + 2)^3 - 1
      -- Show 1 + (k + 2)^3 * X k = (X k + (k + 2)^2) * ((k + 2)^3 - 1)
      have hk3 : 1 ≤ (k + 2)^3 := Nat.one_le_pow _ _ hk'_pos
      have hxZ : (X k : ℤ) = ((k : ℤ) + 2)^5 - ((k : ℤ) + 2)^2 - 1 := by
        have hh : ((X k + (k + 2)^2 + 1 : ℕ) : ℤ) = (((k + 2)^5 : ℕ) : ℤ) := by
          exact_mod_cast hx_val
        push_cast at hh; linarith
      have keyZ : (1 + (k + 2)^3 * X k : ℤ) =
                  ((X k + (k + 2)^2 : ℤ)) * ((k + 2)^3 - 1 : ℤ) := by
        rw [hxZ]; ring
      -- Move to ℕ
      have lhsZ : ((1 + (k + 2)^3 * X k : ℕ) : ℤ) = (1 + (k + 2)^3 * X k : ℤ) := by push_cast; ring
      have rhsZ : (((X k + (k + 2)^2) * ((k + 2)^3 - 1) : ℕ) : ℤ) =
                  ((X k + (k + 2)^2 : ℤ)) * ((k + 2)^3 - 1 : ℤ) := by
        push_cast [hk3]; ring
      have : ((1 + (k + 2)^3 * X k : ℕ) : ℤ) =
             (((X k + (k + 2)^2) * ((k + 2)^3 - 1) : ℕ) : ℤ) := by rw [lhsZ, rhsZ, keyZ]
      exact_mod_cast this

end UK2008R2P4
