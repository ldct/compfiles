/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2024, Round 2, Problem 2

Find all functions f from the integers to the integers such that for all
integers n: 2f(f(n)) = 5f(n) − 2n.
-/

namespace UK2024R2P2

determine solution_set : Set (ℤ → ℤ) :=
  { fun n => 2 * n }

problem uk2024_r2_p2 :
    { f : ℤ → ℤ | ∀ n, 2 * f (f n) = 5 * f n - 2 * n } =
    solution_set := by
  ext f
  simp only [Set.mem_setOf_eq, solution_set, Set.mem_singleton_iff]
  constructor
  · intro h
    -- Define g(n) = f(n) - 2n. Then g(n) = 2 * g(f(n)).
    -- By iterating, 2^k divides g(n) for all k ≥ 0, so g(n) = 0.
    have key : ∀ n, f n - 2 * n = 2 * (f (f n) - 2 * f n) := by
      intro n
      have := h n
      linarith
    -- Iterate to show 2^k ∣ (f n - 2 * n) for all k
    have iterate : ∀ k n, (2^k : ℤ) ∣ (f n - 2 * n) := by
      intro k
      induction k with
      | zero => intro n; simp
      | succ k ih =>
        intro n
        rw [key n, pow_succ, mul_comm (2^k) 2]
        exact mul_dvd_mul_left 2 (ih (f n))
    -- Hence f n - 2 * n = 0
    funext n
    have habs : ∀ k : ℕ, (2^k : ℤ) ∣ (f n - 2 * n) := fun k => iterate k n
    -- If x ≠ 0, then |x| < 2^k for some k, contradicting 2^k ∣ x
    have hzero : f n - 2 * n = 0 := by
      set x := f n - 2 * n with hx_def
      by_contra hne'
      have hlt : |x| < 2 ^ (x.natAbs + 1) := by
        have h1 : (x.natAbs : ℤ) < 2 ^ (x.natAbs + 1) := by
          exact_mod_cast Nat.lt_two_pow_self.trans_le
            (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _))
        calc |x| = (x.natAbs : ℤ) := Int.abs_eq_natAbs _
          _ < 2 ^ (x.natAbs + 1) := h1
      have hdvd := habs (x.natAbs + 1)
      exact hne' (Int.eq_zero_of_abs_lt_dvd hdvd hlt)
    linarith
  · rintro rfl
    intro n; ring

end UK2024R2P2
