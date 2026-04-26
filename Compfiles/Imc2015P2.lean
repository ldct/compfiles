/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Size

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Competition 2015, Problem 2

For a positive integer `n`, let `f(n)` be the number obtained by writing `n` in
binary and replacing every `0` with `1` and vice versa. (E.g. `n = 23 = 10111₂`,
`f(n) = 1000₂ = 8`.) Prove that
`∑_{k=1}^n f(k) ≤ n²/4`.
-/

namespace Imc2015P2

/-- Bit complement of `n` within its natural binary length:
`f(n) = 2^(size n) - 1 - n`. Equivalently `n + f(n) = 2^(size n) - 1`.
By convention `f(0) = 0`. -/
def f (n : ℕ) : ℕ := 2 ^ Nat.size n - 1 - n

-- snip begin

lemma f_zero : f 0 = 0 := rfl

lemma f_one : f 1 = 0 := rfl

lemma n_add_f_eq (n : ℕ) (hn : 1 ≤ n) : n + f n = 2 ^ Nat.size n - 1 := by
  have h1 : n < 2 ^ Nat.size n := Nat.lt_size_self n
  unfold f; omega

lemma f_lt_self_of_pos {n : ℕ} (hn : 1 ≤ n) : f n < n := by
  have hsize : 0 < Nat.size n := Nat.size_pos.mpr hn
  have hge : 2 ^ (Nat.size n - 1) ≤ n := by
    have : Nat.size n - 1 < Nat.size n := Nat.sub_lt hsize (by decide)
    exact Nat.lt_size.mp this
  have hpow : 2 ^ Nat.size n = 2 * 2 ^ (Nat.size n - 1) := by
    conv_lhs => rw [show Nat.size n = (Nat.size n - 1) + 1 from by omega]
    ring
  unfold f
  omega

/-- Recursion: `f(2m+1) = 2 f(m)` for all `m`. -/
lemma f_two_mul_add_one (m : ℕ) : f (2 * m + 1) = 2 * f m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · decide
  · have hsize_m : 0 < Nat.size m := Nat.size_pos.mpr hm
    have h2 : m < 2 ^ Nat.size m := Nat.lt_size_self m
    have h1 : 2 ^ (Nat.size m - 1) ≤ m :=
      Nat.lt_size.mp (by omega : Nat.size m - 1 < Nat.size m)
    have hpow : 2 ^ Nat.size m = 2 * 2 ^ (Nat.size m - 1) := by
      conv_lhs => rw [show Nat.size m = (Nat.size m - 1) + 1 from by omega]
      ring
    have h3 : 2 ^ Nat.size m ≤ 2 * m + 1 := by omega
    have h4 : 2 * m + 1 < 2 ^ (Nat.size m + 1) := by rw [pow_succ]; omega
    have hsize : Nat.size (2 * m + 1) = Nat.size m + 1 := by
      have hle : Nat.size (2 * m + 1) ≤ Nat.size m + 1 := Nat.size_le.mpr h4
      have hge : Nat.size m + 1 ≤ Nat.size (2 * m + 1) := Nat.lt_size.mpr h3
      omega
    show 2 ^ Nat.size (2 * m + 1) - 1 - (2 * m + 1) = 2 * (2 ^ Nat.size m - 1 - m)
    rw [hsize]
    have h5 : 2 ^ (Nat.size m + 1) = 2 * 2 ^ Nat.size m := by rw [pow_succ]; ring
    have h6 : 1 ≤ 2 ^ Nat.size m := Nat.one_le_two_pow
    have hm_le : m + 1 ≤ 2 ^ Nat.size m := h2
    omega

/-- Recursion: `f(2m) = 2 f(m) + 1` for `m ≥ 1`. -/
lemma f_two_mul (m : ℕ) (hm : 1 ≤ m) : f (2 * m) = 2 * f m + 1 := by
  have hsize_m : 0 < Nat.size m := Nat.size_pos.mpr hm
  have h2 : m < 2 ^ Nat.size m := Nat.lt_size_self m
  have h1 : 2 ^ (Nat.size m - 1) ≤ m :=
    Nat.lt_size.mp (by omega : Nat.size m - 1 < Nat.size m)
  have hpow : 2 ^ Nat.size m = 2 * 2 ^ (Nat.size m - 1) := by
    conv_lhs => rw [show Nat.size m = (Nat.size m - 1) + 1 from by omega]
    ring
  have h3 : 2 ^ Nat.size m ≤ 2 * m := by omega
  have h4 : 2 * m < 2 ^ (Nat.size m + 1) := by rw [pow_succ]; omega
  have hsize : Nat.size (2 * m) = Nat.size m + 1 := by
    have hle : Nat.size (2 * m) ≤ Nat.size m + 1 := Nat.size_le.mpr h4
    have hge : Nat.size m + 1 ≤ Nat.size (2 * m) := Nat.lt_size.mpr h3
    omega
  show 2 ^ Nat.size (2 * m) - 1 - 2 * m = 2 * (2 ^ Nat.size m - 1 - m) + 1
  rw [hsize]
  have h5 : 2 ^ (Nat.size m + 1) = 2 * 2 ^ Nat.size m := by rw [pow_succ]; ring
  have h6 : 1 ≤ 2 ^ Nat.size m := Nat.one_le_two_pow
  have hm_le : m + 1 ≤ 2 ^ Nat.size m := h2
  omega

/-- The summation `S n = ∑_{k=0}^{n} f k` (equals `∑_{k=1}^{n} f k` since `f 0 = 0`). -/
def S (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), f k

lemma S_zero : S 0 = 0 := by simp [S, f_zero]

lemma S_succ (n : ℕ) : S (n + 1) = S n + f (n + 1) := by
  unfold S
  rw [Finset.sum_range_succ]

/-- Recursion for `S` at odd arguments: `S(2m+1) = 4 S(m) + m`. -/
lemma S_two_mul_add_one (m : ℕ) : S (2 * m + 1) = 4 * S m + m := by
  induction m with
  | zero => simp [S, f_zero, f_one, Finset.sum_range_succ]
  | succ m ih =>
    have h1 : S (2 * (m + 1) + 1) = S (2 * m + 1) + f (2 * m + 2) + f (2 * m + 3) := by
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 from by ring, S_succ, S_succ]
    have hf1 : f (2 * m + 2) = 2 * f (m + 1) + 1 := by
      have : 2 * m + 2 = 2 * (m + 1) := by ring
      rw [this, f_two_mul (m + 1) (by omega)]
    have hf2 : f (2 * m + 3) = 2 * f (m + 1) := by
      have : 2 * m + 3 = 2 * (m + 1) + 1 := by ring
      rw [this, f_two_mul_add_one]
    rw [h1, ih, hf1, hf2]
    have : S (m + 1) = S m + f (m + 1) := S_succ m
    omega

/-- Recursion for `S` at positive even arguments: `4 S(m) + m = S(2m) + 2 f(m)`. -/
lemma S_two_mul (m : ℕ) (hm : 1 ≤ m) : 4 * S m + m = S (2 * m) + 2 * f m := by
  -- Write m = m' + 1 where m' = m - 1.
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hS2m : S (2 * (m' + 1)) = 4 * S m' + m' + (2 * f (m' + 1) + 1) := by
    have h2m : 2 * (m' + 1) = (2 * m' + 1) + 1 := by ring
    rw [h2m, S_succ]
    rw [S_two_mul_add_one m']
    have : (2 * m' + 1) + 1 = 2 * (m' + 1) := by ring
    rw [this, f_two_mul (m' + 1) (by omega)]
  have hS : S (m' + 1) = S m' + f (m' + 1) := S_succ m'
  rw [hS, hS2m]
  omega

/-- The core identity: `3(n² - 4 S n) = (n - 2 f n)(n - 2 f n + 2)`, working over `ℤ`. -/
lemma core_identity (n : ℕ) :
    3 * ((n : ℤ) ^ 2 - 4 * S n) = ((n : ℤ) - 2 * f n) * ((n : ℤ) - 2 * f n + 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [S_zero, f_zero]
    by_cases hodd : ∃ m, n = 2 * m + 1
    · obtain ⟨m, rfl⟩ := hodd
      have hS : S (2 * m + 1) = 4 * S m + m := S_two_mul_add_one m
      have hf : f (2 * m + 1) = 2 * f m := f_two_mul_add_one m
      have ihm := ih m (by omega)
      push_cast [hS, hf]
      push_cast at ihm
      ring_nf
      ring_nf at ihm
      linarith [ihm]
    · push Not at hodd
      have hev : Even n := by
        rcases Nat.even_or_odd n with h | h
        · exact h
        · exfalso; obtain ⟨k, hk⟩ := h
          exact hodd k (by omega)
      obtain ⟨m, hm⟩ := hev
      have hm' : n = 2 * m := by omega
      have hmpos : 1 ≤ m := by omega
      subst hm'
      have hSm : 4 * S m + m = S (2 * m) + 2 * f m := S_two_mul m hmpos
      have hf : f (2 * m) = 2 * f m + 1 := f_two_mul m hmpos
      have ihm := ih m (by omega)
      push_cast [hf]
      push_cast at ihm
      have hSm_cast : (4 : ℤ) * S m + m = S (2 * m) + 2 * f m := by exact_mod_cast hSm
      have : (S (2 * m) : ℤ) = 4 * S m + m - 2 * f m := by linarith
      rw [this]
      ring_nf
      ring_nf at ihm
      linarith [ihm]

/-- `n - 2 f n` is congruent to `0` or `1` mod `3`, never `2`. Hence
`(n - 2 f n)(n - 2 f n + 2) ≥ 0` as integers. -/
lemma prod_nonneg (n : ℕ) :
    0 ≤ ((n : ℤ) - 2 * f n) * ((n : ℤ) - 2 * f n + 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [f_zero]
  -- n + f n = 2^s - 1, so 2(n + f n) = 2^(s+1) - 2, i.e., 2^(s+1) = 2 n + 2 f n + 2.
  -- Hence n - 2 f n = 3 n - 2^(s+1) + 2.
  -- Also (n - 2 f n) mod 3 = (3n - 2^(s+1) + 2) mod 3 = (2 - 2^(s+1)) mod 3.
  -- 2^(s+1) mod 3 is either 1 or 2 (never 0 for s+1 ≥ 1). So (n - 2 f n) mod 3 is 0 or 1.
  -- Therefore n - 2 f n is never ≡ 2 (mod 3), so never equals -1.
  -- The product k(k+2) is negative only when k = -1.
  set k : ℤ := (n : ℤ) - 2 * f n with hk
  -- It suffices to show k ≠ -1.
  rcases le_or_gt (0 : ℤ) k with hpos | hneg
  · have : 0 ≤ k + 2 := by linarith
    exact mul_nonneg hpos this
  · -- k < 0. Show k ≤ -2, then k + 2 ≤ 0, so product ≥ 0.
    -- Claim: k ≠ -1. Uses 3 | (2^(s+1) - 2 - k).
    suffices hk_ne : k ≠ -1 by
      have : k ≤ -2 := by
        rcases lt_or_eq_of_le (show k ≤ -1 from by linarith) with h | h
        · linarith
        · exfalso; exact hk_ne h
      have : k + 2 ≤ 0 := by linarith
      have hk_neg : k < 0 := hneg
      nlinarith
    -- Prove k ≠ -1. k = n - 2 f n.
    intro hkeq
    have hadd : n + f n + 1 = 2 ^ Nat.size n := by
      have h1 : n < 2 ^ Nat.size n := Nat.lt_size_self n
      have := n_add_f_eq n hn
      omega
    -- From hkeq: (n : ℤ) = 2 f n - 1, i.e., n + 1 = 2 f n in ℤ.
    -- So n = 2 f n - 1 ≥ 0 means f n ≥ 1.
    have hfpos : 1 ≤ f n := by
      by_contra h
      push Not at h
      have hfz : f n = 0 := by omega
      -- Then n = -1 in ℤ, impossible.
      have hke : (n : ℤ) - 2 * (f n : ℤ) = -1 := by simp [← hk, hkeq]
      rw [hfz] at hke
      push_cast at hke
      have : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
      linarith
    -- From hkeq in ℕ: n = 2 f n - 1, so n + 1 = 2 f n, so 3 f n = (n + f n + 1) = 2^(size n).
    have hnat : n + 1 = 2 * f n := by
      have hn_eq : (n : ℤ) = 2 * f n - 1 := by linarith
      have : (n : ℤ) + 1 = 2 * f n := by linarith
      exact_mod_cast this
    have h3dvd_pow : 3 ∣ 2 ^ Nat.size n := by
      have : 3 * f n = 2 ^ Nat.size n := by omega
      exact ⟨f n, this.symm⟩
    -- 2^k mod 3 is always 1 or 2, never 0.
    have hnot3 : ¬ (3 ∣ 2 ^ Nat.size n) := by
      intro hd
      have h2mod3 : ∀ k : ℕ, 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
        intro k
        induction k with
        | zero => left; rfl
        | succ k ih =>
          rw [pow_succ, Nat.mul_mod]
          rcases ih with h | h
          · rw [h]; right; rfl
          · rw [h]; left; rfl
      rcases h2mod3 (Nat.size n) with h | h
      · omega
      · omega
    exact hnot3 h3dvd_pow

-- snip end

problem imc2015_p2 (n : ℕ) (_hn : 1 ≤ n) :
    4 * ∑ k ∈ Finset.Icc 1 n, f k ≤ n ^ 2 := by
  have hS : ∑ k ∈ Finset.Icc 1 n, f k = S n := by
    unfold S
    rw [show (Finset.range (n + 1) : Finset ℕ) = insert 0 (Finset.Icc 1 n) from by
      ext x; simp; omega]
    rw [Finset.sum_insert (by simp)]
    simp [f_zero]
  rw [hS]
  -- Use core_identity and prod_nonneg.
  have hid := core_identity n
  have hp := prod_nonneg n
  -- hid: 3 * (n² - 4 S n) = (n - 2 f n)(n - 2 f n + 2).
  -- hp: RHS ≥ 0. So n² - 4 S n ≥ 0 (divide by 3).
  have : (0 : ℤ) ≤ (n : ℤ) ^ 2 - 4 * S n := by linarith
  have hnat : (4 * S n : ℤ) ≤ (n : ℤ) ^ 2 := by linarith
  exact_mod_cast hnat

end Imc2015P2
