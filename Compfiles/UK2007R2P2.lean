/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2007, Round 2, Problem 2

Show that there are infinitely many pairs of positive integers (m, n) such
that (m + 1)/n + (n + 1)/m is a positive integer.
-/

namespace UK2007R2P2

/-- A recursively-defined sequence: 1, 2, 6, 21, 77, … with a(k+2) = 4·a(k+1) − a(k) − 1.
    The pairs (a k, a (k+1)) all satisfy the divisibility condition with N = 4. -/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | (n + 2) => 4 * a (n + 1) - a n - 1

/-- Working invariant: a k is positive, a k < a (k+1), and the Vieta equation holds. -/
lemma a_invariant : ∀ k, 0 < a k ∧ a k < a (k + 1) ∧
    a k * a k + a k + a (k + 1) * a (k + 1) + a (k + 1) = 4 * (a k * a (k + 1)) := by
  intro k
  induction k with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · show 0 < 1; exact Nat.one_pos
    · show 1 < 2; decide
    · show 1 * 1 + 1 + 2 * 2 + 2 = 4 * (1 * 2); decide
  | succ n ih =>
    obtain ⟨hpos, hlt, heq⟩ := ih
    -- Show a (n+1) > 0 (immediate from hlt and hpos) ✓
    -- Show a (n+2) > a (n+1): a (n+2) = 4 a (n+1) - a n - 1 > a (n+1) iff 3 a (n+1) > a n + 1
    have hpos1 : 0 < a (n + 1) := lt_trans hpos hlt
    -- Establish a (n+2) = 4 a (n+1) - a n - 1 with the subtraction safe
    have hrec_nat : a (n + 2) + a n + 1 = 4 * a (n + 1) := by
      show 4 * a (n + 1) - a n - 1 + a n + 1 = 4 * a (n + 1)
      have h1 : a n + 1 ≤ 4 * a (n + 1) := by
        -- a n + 1 ≤ a (n+1) + 1 (from hlt) ≤ 4 a (n+1) since a (n+1) ≥ 1
        omega
      omega
    -- Second coord invariant in ℤ
    have heqZ : ((a n : ℤ) * a n + a n + a (n+1) * a (n+1) + a (n+1)) =
                4 * ((a n : ℤ) * a (n+1)) := by
      exact_mod_cast heq
    have hrec_int : (a (n + 2) : ℤ) = 4 * a (n + 1) - a n - 1 := by
      have : ((a (n + 2) + a n + 1 : ℕ) : ℤ) = ((4 * a (n + 1) : ℕ) : ℤ) := by exact_mod_cast hrec_nat
      push_cast at this; linarith
    -- Now check a (n+2) > a (n+1) and the new Vieta.
    refine ⟨hpos1, ?_, ?_⟩
    · -- a (n+1) < a (n+2). In ℤ: a(n+1) < 4 a(n+1) - a n - 1 ⟺ 3 a(n+1) > a n + 1.
      -- We have a n < a(n+1), so 3 a(n+1) > 3 a n ≥ 3 ≥ a n + 1 if a n ≥ 1 and a(n+1) ≥ a n + 1.
      -- Actually: 3 a(n+1) ≥ 3 (a n + 1) = 3 a n + 3 > a n + 1. ✓
      have : (a (n + 1) : ℤ) < a (n + 2) := by rw [hrec_int]; linarith
      exact_mod_cast this
    · -- Vieta: a(n+1)² + a(n+1) + a(n+2)² + a(n+2) = 4 a(n+1) a(n+2).
      -- Use a(n+2) = 4 a(n+1) - a n - 1, compute.
      -- Strategy: use the identity (over ℤ) from Vieta jumping:
      -- If m² + m + n² + n = 4 m n, and we define m' = 4 n - m - 1, then
      -- m² + m + n² + n = 4 m n and
      -- m'² + m' + n² + n = 4 m' n reduces to same.
      -- We need: a(n+1)² + a(n+1) + a(n+2)² + a(n+2) = 4 a(n+1) a(n+2).
      -- Verify in ℤ.
      have hVieta : ((a (n + 1) : ℤ) * a (n + 1) + a (n+1) + (a (n+2)) * a (n+2) + a (n+2)) =
             4 * ((a (n+1) : ℤ) * a (n+2)) := by
        -- Use heqZ and hrec_int, expand.
        have := heqZ
        have hr := hrec_int
        nlinarith [heqZ, hrec_int, sq_nonneg ((a n : ℤ))]
      exact_mod_cast hVieta

problem uk2007_r2_p2 :
    ∃ f : ℕ → ℕ × ℕ,
      StrictMono f ∧
      ∀ k, 0 < (f k).1 ∧ 0 < (f k).2 ∧
           ∃ N : ℕ, 0 < N ∧
             (f k).1 * ((f k).1 + 1) + (f k).2 * ((f k).2 + 1)
               = N * ((f k).1 * (f k).2) := by
  refine ⟨fun k => (a k, a (k + 1)), ?_, ?_⟩
  · -- StrictMono
    intro i j hij
    obtain ⟨_, hlti, _⟩ := a_invariant i
    obtain ⟨_, hltj, _⟩ := a_invariant j
    have : a i < a j := by
      -- Prove a is strictly monotone: a i < a (i+1) ≤ a j.
      have hmono : ∀ i j : ℕ, i < j → a i < a j := by
        intro i j hij
        induction j, hij using Nat.le_induction with
        | base => exact (a_invariant i).2.1
        | succ n hn ih =>
          exact lt_trans ih (a_invariant n).2.1
      exact hmono i j hij
    refine Prod.lt_iff.mpr (Or.inl ⟨this, ?_⟩)
    -- a (i+1) ≤ a (j+1)
    have hmono : ∀ p q : ℕ, p < q → a p < a q := by
      intro p q hpq
      induction q, hpq using Nat.le_induction with
      | base => exact (a_invariant p).2.1
      | succ n hn ih =>
        exact lt_trans ih (a_invariant n).2.1
    show a (i + 1) ≤ a (j + 1)
    exact le_of_lt (hmono (i + 1) (j + 1) (Nat.succ_lt_succ hij))
  · intro k
    obtain ⟨hpos, hlt, heq⟩ := a_invariant k
    have hpos1 : 0 < a (k + 1) := lt_trans hpos hlt
    refine ⟨hpos, hpos1, 4, by norm_num, ?_⟩
    -- (a k)(a k + 1) + (a (k+1))(a (k+1) + 1) = 4 a k a (k+1)
    have : a k * (a k + 1) + a (k+1) * (a (k+1) + 1) =
           a k * a k + a k + a (k+1) * a (k+1) + a (k+1) := by ring
    rw [this]; exact heq

end UK2007R2P2
