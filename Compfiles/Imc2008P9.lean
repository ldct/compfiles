/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Competition 2008, Problem 9
(IMC 2008, Day 2, Problem 3)

Let `n` be a positive integer. Prove that `2^(n-1)` divides

  `∑_{0 ≤ k < n/2} C(n, 2*k + 1) * 5^k`.
-/

namespace Imc2008P9

open Finset

snip begin

/-
The "even" and "odd" parts of the binomial expansion of `(1 + √5)^n`:

  `A n = ∑_{k} C(n, 2k) * 5^k`,
  `B n = ∑_{k} C(n, 2k+1) * 5^k`.

Formally, `(1 + √5)^n = A n + B n * √5`. We record the recurrence

  `A (n+1) = A n + 5 * B n`,   `B (n+1) = A n + B n`,

proved directly from Pascal's rule without ever mentioning `√5`.

Then a simultaneous induction gives

  `2^n ∣ 2 * B n`   and   `2^n ∣ A n - B n`  (over `ℤ`),

from which `2^(n-1) ∣ B n` for `n ≥ 1`, which is the desired statement.
-/

/-- The even-indexed part of the `(1+√5)^n` expansion, as a natural number.
Terms with `2k > n` vanish automatically, so we sum over a conservatively large range. -/
def A (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), n.choose (2 * k) * 5 ^ k

/-- The odd-indexed part of the `(1+√5)^n` expansion, as a natural number.
This is (essentially) the sum appearing in the problem. -/
def B (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), n.choose (2 * k + 1) * 5 ^ k

/-- Changing the upper bound on the range of `A n` doesn't matter, as long as it's ≥ n+1. -/
lemma A_eq_extend (n N : ℕ) (hN : n + 1 ≤ N) :
    A n = ∑ k ∈ range N, n.choose (2 * k) * 5 ^ k := by
  unfold A
  apply Finset.sum_subset (Finset.range_subset_range.mpr hN)
  intro k _ hk'
  rw [mem_range] at hk'
  have : n < 2 * k := by omega
  rw [Nat.choose_eq_zero_of_lt this, Nat.zero_mul]

/-- Changing the upper bound on the range of `B n` doesn't matter, as long as it's ≥ n+1. -/
lemma B_eq_extend (n N : ℕ) (hN : n + 1 ≤ N) :
    B n = ∑ k ∈ range N, n.choose (2 * k + 1) * 5 ^ k := by
  unfold B
  apply Finset.sum_subset (Finset.range_subset_range.mpr hN)
  intro k _ hk'
  rw [mem_range] at hk'
  have : n < 2 * k + 1 := by omega
  rw [Nat.choose_eq_zero_of_lt this, Nat.zero_mul]

/-- The key recurrence: `B (n+1) = A n + B n`. -/
lemma B_succ (n : ℕ) : B (n + 1) = A n + B n := by
  -- `B (n+1)` is a sum over `range (n+2)`. Extend `A n` and `B n` to `range (n+2)` too.
  rw [A_eq_extend n (n + 2) (by omega), B_eq_extend n (n + 2) (by omega)]
  show ∑ k ∈ range (n + 2), (n + 1).choose (2 * k + 1) * 5 ^ k
        = ∑ k ∈ range (n + 2), n.choose (2 * k) * 5 ^ k
        + ∑ k ∈ range (n + 2), n.choose (2 * k + 1) * 5 ^ k
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hpascal : (n + 1).choose (2 * k + 1) = n.choose (2 * k) + n.choose (2 * k + 1) := by
    rw [Nat.choose_succ_succ]
  rw [hpascal, Nat.add_mul]

/-- The key recurrence: `A (n+1) = A n + 5 * B n`. -/
lemma A_succ (n : ℕ) : A (n + 1) = A n + 5 * B n := by
  -- Expand A (n+1) into k=0 term plus a shifted sum, then apply Pascal's rule.
  rw [A_eq_extend n (n + 2) (by omega), B_eq_extend n (n + 2) (by omega)]
  show ∑ k ∈ range (n + 1 + 1), (n + 1).choose (2 * k) * 5 ^ k
        = (∑ k ∈ range (n + 2), n.choose (2 * k) * 5 ^ k)
          + 5 * ∑ k ∈ range (n + 2), n.choose (2 * k + 1) * 5 ^ k
  -- Split off k = 0 from A (n+1) and A n (both over range (n+2) = range (n+1+1)).
  rw [show (n + 2 : ℕ) = (n + 1) + 1 from rfl]
  rw [Finset.sum_range_succ' (fun k => (n + 1).choose (2 * k) * 5 ^ k) (n + 1)]
  rw [Finset.sum_range_succ' (fun k => n.choose (2 * k) * 5 ^ k) (n + 1)]
  simp only [Nat.mul_zero, Nat.choose_zero_right, Nat.pow_zero, Nat.mul_one]
  -- Now bring `5 *` inside the B n sum.
  rw [Finset.mul_sum]
  -- Remaining goal:
  -- ∑_{k<n+1} C(n+1, 2*(k+1))*5^(k+1) + 1
  -- = (∑_{k<n+1} C(n, 2*(k+1))*5^(k+1) + 1) + ∑_{k<n+2} 5 * (C(n, 2k+1)*5^k)
  -- Pascal: C(n+1, 2*(k+1)) = C(n, 2k+1) + C(n, 2*(k+1)).
  have key : ∀ k, (n + 1).choose (2 * (k + 1)) * 5 ^ (k + 1)
                = n.choose (2 * k + 1) * 5 ^ (k + 1)
                + n.choose (2 * (k + 1)) * 5 ^ (k + 1) := by
    intro k
    have hpascal : (n + 1).choose (2 * (k + 1))
                    = n.choose (2 * k + 1) + n.choose (2 * (k + 1)) := by
      have : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
      rw [this, Nat.choose_succ_succ]
    rw [hpascal, Nat.add_mul]
  simp_rw [key]
  rw [Finset.sum_add_distrib]
  -- Make the `5 * B n` sum also over range (n+1) by removing a zero term.
  have align : ∀ k, 5 * (n.choose (2 * k + 1) * 5 ^ k) = n.choose (2 * k + 1) * 5 ^ (k + 1) := by
    intro k
    rw [Nat.pow_succ]; ring
  simp_rw [align]
  -- Peel off last term (k = n+1) from the (range (n+2)) sum; it's zero.
  rw [Finset.sum_range_succ (fun k => n.choose (2 * k + 1) * 5 ^ (k + 1)) (n + 1)]
  have hlast : n.choose (2 * (n + 1) + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  rw [hlast, Nat.zero_mul, Nat.add_zero]
  -- Both sides now equal.
  ring

/-- Simultaneous invariant: `2^n ∣ 2 * B n` and `2^n ∣ A n - B n` (as integers). -/
lemma invariant (n : ℕ) :
    (2 ^ n : ℤ) ∣ (2 * (B n : ℤ)) ∧ (2 ^ n : ℤ) ∣ ((A n : ℤ) - (B n : ℤ)) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [B]
    · simp [A, B]
  | succ n ih =>
    obtain ⟨ihB, ihAB⟩ := ih
    refine ⟨?_, ?_⟩
    · -- 2^(n+1) ∣ 2 * B (n+1) = 2 A n + 2 B n
      --   = 2 (A n - B n) + 2 * (2 B n).
      rw [B_succ]
      have h1 : (2 * ((A n : ℤ) + (B n : ℤ)) : ℤ)
                = 2 * ((A n : ℤ) - (B n : ℤ)) + 2 * (2 * (B n : ℤ)) := by ring
      push_cast
      rw [h1, pow_succ, mul_comm ((2:ℤ)^n) 2]
      exact dvd_add (mul_dvd_mul_left 2 ihAB) (mul_dvd_mul_left 2 ihB)
    · -- A (n+1) - B (n+1) = (A n + 5 B n) - (A n + B n) = 4 B n = 2 * (2 B n).
      rw [A_succ, B_succ]
      have h1 : ((A n : ℤ) + 5 * (B n : ℤ)) - ((A n : ℤ) + (B n : ℤ))
                = 2 * (2 * (B n : ℤ)) := by ring
      push_cast
      rw [h1, pow_succ, mul_comm ((2:ℤ)^n) 2]
      exact mul_dvd_mul_left 2 ihB

snip end

problem imc2008_p9 (n : ℕ) (hn : 0 < n) :
    (2 ^ (n - 1) : ℤ) ∣ ∑ k ∈ Finset.range n, (n.choose (2 * k + 1) : ℤ) * 5 ^ k := by
  -- Rewrite the problem's sum as `B n`.
  have hsum : (∑ k ∈ Finset.range n, (n.choose (2 * k + 1) : ℤ) * 5 ^ k) = (B n : ℤ) := by
    unfold B
    push_cast
    rw [Finset.sum_range_succ]
    have : n.choose (2 * n + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [this]
    push_cast
    ring
  rw [hsum]
  -- Use the invariant: 2^n ∣ 2 * B n. Since n ≥ 1, conclude 2^(n-1) ∣ B n.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_add_cancel hn).symm⟩
  have hinv := (invariant (m + 1)).1
  show (2 : ℤ) ^ ((m + 1) - 1) ∣ (B (m + 1) : ℤ)
  rw [Nat.add_sub_cancel]
  -- 2^(m+1) ∣ 2 * B (m+1). Write 2^(m+1) = 2 * 2^m and cancel the 2.
  rw [pow_succ, mul_comm ((2:ℤ)^m) 2] at hinv
  have h2ne : (2 : ℤ) ≠ 0 := by norm_num
  exact (mul_dvd_mul_iff_left h2ne).mp hinv

end Imc2008P9
