/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2013, Round 2, Problem 1

Are there infinitely many pairs of positive integers (m, n) such that
both m divides n² + 1 and n divides m² + 1?
-/

namespace UK2013R2P1

/-- The sequence a_0 = 1, a_1 = 2, a_{n+2} = 3 a_{n+1} - a_n.
    Values: 1, 2, 5, 13, 34, ... (odd-indexed Fibonacci). -/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | (n + 2) => 3 * a (n + 1) - a n

lemma a_zero : a 0 = 1 := rfl
lemma a_one : a 1 = 2 := rfl
lemma a_two : a 2 = 5 := rfl

lemma a_succ_lt (n : ℕ) : a n < a (n + 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
    show a (k + 1) < a (k + 2)
    show a (k + 1) < 3 * a (k + 1) - a k
    have : a k < a (k + 1) := ih
    omega

lemma a_pos (n : ℕ) : 0 < a n := by
  induction n with
  | zero => decide
  | succ k ih => exact lt_trans ih (a_succ_lt k)

lemma a_mono_le {i j : ℕ} (h : i ≤ j) : a i ≤ a j := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (Nat.le_of_lt (a_succ_lt _))

lemma a_strictMono : StrictMono a := by
  intro i j hij
  induction hij with
  | refl => exact a_succ_lt i
  | step _ ih => exact lt_trans ih (a_succ_lt _)

/-- Key identity: a_{n+1}^2 + 1 = a_n * a_{n+2}. -/
lemma a_key (n : ℕ) : a (n + 1) ^ 2 + 1 = a n * a (n + 2) := by
  induction n with
  | zero => decide
  | succ k ih =>
    -- Cast to ℤ
    have h2 : a (k + 2) = 3 * a (k + 1) - a k := rfl
    have h3 : a (k + 3) = 3 * a (k + 2) - a (k + 1) := rfl
    have hle2 : a k ≤ 3 * a (k + 1) := by
      have := a_succ_lt k; omega
    have hle3 : a (k + 1) ≤ 3 * a (k + 2) := by
      have h := a_succ_lt (k + 1)
      show a (k + 1) ≤ 3 * a (k + 2)
      have h' : a (k + 1) < a (k + 2) := h
      omega
    have h2Z : (a (k + 2) : ℤ) = 3 * (a (k + 1) : ℤ) - (a k : ℤ) := by
      have : ((3 * a (k + 1) - a k : ℕ) : ℤ) = 3 * (a (k + 1) : ℤ) - (a k : ℤ) := by
        push_cast [hle2]; ring
      rw [show (a (k + 2) : ℤ) = ((3 * a (k + 1) - a k : ℕ) : ℤ) from by rw [← h2]]
      exact this
    have h3Z : (a (k + 3) : ℤ) = 3 * (a (k + 2) : ℤ) - (a (k + 1) : ℤ) := by
      have : ((3 * a (k + 2) - a (k + 1) : ℕ) : ℤ) = 3 * (a (k + 2) : ℤ) - (a (k + 1) : ℤ) := by
        push_cast [hle3]; ring
      rw [show (a (k + 3) : ℤ) = ((3 * a (k + 2) - a (k + 1) : ℕ) : ℤ) from by rw [← h3]]
      exact this
    have ihZ : (a (k + 1) : ℤ) ^ 2 + 1 = (a k : ℤ) * (a (k + 2) : ℤ) := by exact_mod_cast ih
    -- Want: a(k+2)^2 + 1 = a(k+1) * a(k+3)
    have goalZ : (a (k + 2) : ℤ) ^ 2 + 1 = (a (k + 1) : ℤ) * (a (k + 3) : ℤ) := by
      rw [h3Z, h2Z]
      -- target: (3*a1 - a0)^2 + 1 = a1 * (3*(3*a1 - a0) - a1) where a0=a k, a1=a(k+1)
      -- RHS = a1 * (9*a1 - 3*a0 - a1) = a1*(8*a1 - 3*a0) = 8*a1^2 - 3*a0*a1
      -- LHS = 9*a1^2 - 6*a0*a1 + a0^2 + 1
      -- Difference: LHS - RHS = a1^2 - 3*a0*a1 + a0^2 + 1 = (a1^2 + 1) - a0*(3*a1 - a0)
      -- = (a1^2 + 1) - a0 * a(k+2) = 0 by ih (with h2Z to express a(k+2))
      have : (a k : ℤ) * (3 * (a (k + 1) : ℤ) - (a k : ℤ)) = (a (k + 1) : ℤ)^2 + 1 := by
        rw [← h2Z]; linarith [ihZ]
      linarith [this]
    exact_mod_cast goalZ

problem uk2013_r2_p1 :
    ∃ f : ℕ → ℕ × ℕ, StrictMono f ∧
      ∀ k, 0 < (f k).1 ∧ 0 < (f k).2 ∧
           (f k).1 ∣ (f k).2 ^ 2 + 1 ∧
           (f k).2 ∣ (f k).1 ^ 2 + 1 := by
  refine ⟨fun k => (a k, a (k + 1)), ?_, ?_⟩
  · intro i j hij
    refine Prod.lt_iff.mpr (Or.inl ⟨a_strictMono hij, ?_⟩)
    exact a_mono_le (Nat.succ_le_succ (le_of_lt hij))
  · intro k
    refine ⟨a_pos k, a_pos (k + 1), ?_, ?_⟩
    · -- a k ∣ a(k+1)^2 + 1 : use a_key
      rw [a_key k]; exact Dvd.intro (a (k + 2)) rfl
    · -- a(k+1) ∣ a k^2 + 1
      match k with
      | 0 =>
        show a 1 ∣ a 0 ^ 2 + 1
        decide
      | k + 1 =>
        show a (k + 2) ∣ a (k + 1) ^ 2 + 1
        rw [a_key k]
        exact ⟨a k, by ring⟩

end UK2013R2P1
