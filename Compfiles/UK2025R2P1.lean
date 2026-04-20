/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2025, Round 2, Problem 1

Prove that if n is a positive integer, then 1/n can be written as a
finite sum of reciprocals of different triangular numbers.
(A triangular number is one of the form k(k+1)/2 for some positive
integer k.)
-/

namespace UK2025R2P1

/-- The k-th triangular number. -/
def tri (k : ℕ) : ℕ := k * (k + 1) / 2

-- For n ≥ 1, take S = {n, n+1, ..., N-1} ∪ {?} ... simpler: use telescoping
-- 1/T_k = 2/(k(k+1)) = 2/k - 2/(k+1)
-- So sum from k=n to k=2n-1 of 1/T_k = 2/n - 2/(2n) = 2/n - 1/n = 1/n.
-- So take S = Finset.Ico n (2n) when n ≥ 1, but for n=1 we need {1,...} — check:
--   n=1: S = {1}, 1/T_1 = 1/1 = 1 = 1/1. Works.
--   n=2: S = {2,3}, 1/T_2 + 1/T_3 = 1/3 + 1/6 = 1/2. Works.

lemma tri_pos (k : ℕ) (hk : 0 < k) : 0 < tri k := by
  unfold tri
  rcases k with _ | k
  · omega
  · simp [Nat.succ_mul, Nat.mul_succ]
    omega

lemma one_div_tri (k : ℕ) (hk : 0 < k) :
    (1 : ℚ) / tri k = 2 / k - 2 / (k + 1) := by
  unfold tri
  have h2dvd : (2 : ℕ) ∣ k * (k + 1) := by
    rcases Nat.even_or_odd k with he | ho
    · obtain ⟨m, rfl⟩ := he
      exact ⟨m * (2 * m + 1), by ring⟩
    · obtain ⟨m, rfl⟩ := ho
      exact ⟨(2 * m + 1) * (m + 1), by ring⟩
  have hcast : ((k * (k + 1) / 2 : ℕ) : ℚ) = (k : ℚ) * ((k : ℚ) + 1) / 2 := by
    rw [Nat.cast_div h2dvd (by norm_num : ((2 : ℕ) : ℚ) ≠ 0)]
    push_cast
    ring
  rw [hcast]
  have hk1 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hk)
  have hk2 : ((k : ℚ) + 1) ≠ 0 := by
    have : (0 : ℚ) < k + 1 := by positivity
    linarith
  field_simp
  ring

-- General telescoping lemma: for a ≤ b, sum over Ico a b of (f k - f (k+1)) = f a - f b
lemma telescope_sum (f : ℕ → ℚ) (a b : ℕ) (hab : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, (f k - f (k + 1)) = f a - f b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Ico_succ_top hm, ih]
    ring

problem uk2025_r2_p1 (n : ℕ) (hn : 0 < n) :
    ∃ S : Finset ℕ, (∀ k ∈ S, 0 < k) ∧
      (∑ k ∈ S, (1 : ℚ) / tri k) = 1 / n := by
  refine ⟨Finset.Ico n (2 * n), ?_, ?_⟩
  · intro k hk
    rw [Finset.mem_Ico] at hk
    omega
  · have hsum : ∑ k ∈ Finset.Ico n (2 * n), (1 : ℚ) / tri k
        = ∑ k ∈ Finset.Ico n (2 * n), (2 / (k : ℚ) - 2 / (k + 1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Ico] at hk
      exact one_div_tri k (by omega)
    rw [hsum]
    let f : ℕ → ℚ := fun k => 2 / (k : ℚ)
    have hf : ∀ k : ℕ, (2 / (k : ℚ) - 2 / (k + 1)) = f k - f (k + 1) := by
      intro k
      simp only [f]
      push_cast
      ring_nf
    have heq : ∑ k ∈ Finset.Ico n (2 * n), (2 / (k : ℚ) - 2 / (k + 1))
        = ∑ k ∈ Finset.Ico n (2 * n), (f k - f (k + 1)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact hf k
    rw [heq, telescope_sum f n (2 * n) (by omega)]
    simp only [f]
    have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
    push_cast
    field_simp
    ring

end UK2025R2P1
