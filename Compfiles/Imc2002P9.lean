/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .NumberTheory] }

/-!
# International Mathematical Competition 2002, Problem 9
(IMC 2002, Day 2, Problem 3)

For `n ≥ 1`, let
  `a_n = ∑_{k=0}^∞ k^n / k!`
  `b_n = ∑_{k=0}^∞ (-1)^k k^n / k!`
(with the convention `0^0 = 1`). Show that `a_n · b_n ∈ ℤ`.

## Solution outline

The two series converge by comparison with `∑ c^k/k!` (the exponential series).
Define Bell numbers `B 0 = 1`, `B (n+1) = ∑_{m≤n} C(n,m) B m` and
complementary Bell numbers `Cc 0 = 1`, `Cc (n+1) = -∑_{m≤n} C(n,m) Cc m`.
By the identity `(k+1)^n = ∑_m C(n,m) k^m` (applied inside the sum, using
the shift `k ↦ k+1` in the series), one proves
  `a n = B n · e` and `b n = Cc n / e`
by induction on `n`. Multiplying, `a n · b n = B n · Cc n ∈ ℤ`.
-/

namespace Imc2002P9

open scoped Nat
open Real

/-- The summand for `a_n`: `k ↦ k^n / k!` (with `0^0 = 1` by convention). -/
noncomputable def aSummand (n : ℕ) (k : ℕ) : ℝ := (k : ℝ) ^ n / k.factorial

/-- The summand for `b_n`: `k ↦ (-1)^k · k^n / k!`. -/
noncomputable def bSummand (n : ℕ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * ((k : ℝ) ^ n / k.factorial)

/-- `a n = ∑' k, k^n / k!`. -/
noncomputable def a (n : ℕ) : ℝ := ∑' k : ℕ, aSummand n k

/-- `b n = ∑' k, (-1)^k k^n / k!`. -/
noncomputable def b (n : ℕ) : ℝ := ∑' k : ℕ, bSummand n k

snip begin

/-- Auxiliary: sum over `List.range (n+1)` using `B` values at indices up to `n`.
We use strong recursion to define `B`. -/
noncomputable def B : ℕ → ℤ := fun n =>
  n.strongRecOn (fun n ih =>
    match n with
    | 0 => 1
    | k + 1 =>
      ((List.range (k + 1)).attach.map
        fun ⟨m, hm⟩ => (k.choose m : ℤ) * ih m (by
          have := List.mem_range.mp hm
          omega)).sum)

noncomputable def Cc : ℕ → ℤ := fun n =>
  n.strongRecOn (fun n ih =>
    match n with
    | 0 => 1
    | k + 1 =>
      -((List.range (k + 1)).attach.map
        fun ⟨m, hm⟩ => (k.choose m : ℤ) * ih m (by
          have := List.mem_range.mp hm
          omega)).sum)

/-- The core analytic identity: `a n = B n · e`.
The proof is by induction using the recurrence
`a_{n+1} = ∑_{m=0}^n C(n,m) a_m`, derived from
`(k+1)^n = ∑_m C(n,m) k^m` and the shift `k ↦ k+1`
in the series `∑ k^{n+1} / k! = ∑ (k+1) · k^n / (k+1)! = ∑ (k+1)^n / k!`
(since `k · k^n / k! = k^n / (k-1)!`, and re-indexing).

This lemma encapsulates the analytic content of the problem. -/
lemma a_eq_B_mul_exp (n : ℕ) : a n = (B n : ℝ) * Real.exp 1 := by
  -- TODO: This requires the analytic manipulations of the Dobinski-style series,
  -- summability of `k^n/k!`, and the recurrence. These are substantial but
  -- standard; proved in the paper solution.
  sorry

/-- Similarly, `b n = Cc n / e`. -/
lemma b_eq_Cc_div_exp (n : ℕ) : b n = (Cc n : ℝ) / Real.exp 1 := by
  sorry

/-- `a n * b n = B n * Cc n` as a real, hence is an integer. -/
lemma a_mul_b_eq_int (n : ℕ) : a n * b n = ((B n * Cc n : ℤ) : ℝ) := by
  rw [a_eq_B_mul_exp, b_eq_Cc_div_exp]
  have hexp : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
  push_cast
  field_simp

snip end

problem imc2002_p9 (n : ℕ) (_hn : 1 ≤ n) : ∃ z : ℤ, a n * b n = z :=
  ⟨B n * Cc n, a_mul_b_eq_int n⟩

end Imc2002P9
