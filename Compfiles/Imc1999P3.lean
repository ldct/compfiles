/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1999, Problem 3 (Day 1)

Suppose `f : ℝ → ℝ` satisfies, for every `n ≥ 1` and all `x, y ∈ ℝ`,
`|∑_{k=1}^n 3^k (f(x+k·y) - f(x-k·y))| ≤ 1`. Prove that `f` is constant.

## Solution sketch (official)

Subtract the inequality at `n-1` from the inequality at `n`:
`|3^n (f(x+n·y) - f(x-n·y))| ≤ 2`, so `|f(x+n·y) - f(x-n·y)| ≤ 2/3^n`.

For any `u < v`, choose `x = (u+v)/2` and `y = (v-u)/(2n)`. Then
`x + n·y = v` and `x - n·y = u`, giving `|f(u) - f(v)| ≤ 2/3^n` for every
`n ≥ 1`. Letting `n → ∞` yields `f(u) = f(v)`.
-/

namespace Imc1999P3

open scoped BigOperators
open Finset

snip begin

/-- The key consequence of the hypothesis: telescoping the bound at `n` and
`n - 1` (for `n ≥ 1`) yields `|f(x + n·y) - f(x - n·y)| ≤ 2 / 3^n`. -/
lemma diff_bound
    (f : ℝ → ℝ)
    (hf : ∀ n : ℕ, ∀ x y : ℝ,
        |∑ k ∈ Finset.Icc 1 n, (3 : ℝ) ^ k * (f (x + k * y) - f (x - k * y))| ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) (x y : ℝ) :
    |f (x + n * y) - f (x - n * y)| ≤ 2 / (3 : ℝ) ^ n := by
  -- The sum at `n` minus the sum at `n - 1` equals `3^n (f(x+n·y) - f(x-n·y))`.
  set Sn : ℕ → ℝ := fun m =>
    ∑ k ∈ Finset.Icc 1 m, (3 : ℝ) ^ k * (f (x + k * y) - f (x - k * y))
  have hSn_succ : ∀ m : ℕ,
      Sn (m + 1) = Sn m + (3 : ℝ) ^ (m + 1) * (f (x + (m+1) * y) - f (x - (m+1) * y)) := by
    intro m
    show ∑ k ∈ Finset.Icc 1 (m + 1), (3 : ℝ) ^ k * (f (x + k * y) - f (x - k * y))
        = (∑ k ∈ Finset.Icc 1 m, (3 : ℝ) ^ k * (f (x + k * y) - f (x - k * y)))
          + (3 : ℝ) ^ (m + 1) * (f (x + (m+1) * y) - f (x - (m+1) * y))
    rw [show Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) from ?_]
    · rw [Finset.sum_insert (by simp), add_comm]
      push_cast
      ring
    · ext j
      simp only [Finset.mem_insert, Finset.mem_Icc]
      constructor
      · intro ⟨h1, h2⟩
        rcases eq_or_lt_of_le h2 with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h1, Nat.lt_succ_iff.mp h⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨by omega, le_refl _⟩
        · exact ⟨h1, by omega⟩
  -- Get the existence of n - 1
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  have hbound_n : |Sn (m + 1)| ≤ 1 := hf (m + 1) x y
  have hbound_m : |Sn m| ≤ 1 := hf m x y
  have heq : (3 : ℝ) ^ (m + 1) * (f (x + (m + 1) * y) - f (x - (m + 1) * y))
      = Sn (m + 1) - Sn m := by
    rw [hSn_succ]; ring
  have habs : |(3 : ℝ) ^ (m + 1) * (f (x + (m + 1) * y) - f (x - (m + 1) * y))| ≤ 2 := by
    rw [heq]
    calc |Sn (m + 1) - Sn m| ≤ |Sn (m + 1)| + |Sn m| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add hbound_n hbound_m
      _ = 2 := by norm_num
  -- Convert: |3^n * d| = 3^n * |d|, so |d| ≤ 2 / 3^n.
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ (m + 1) := by positivity
  rw [abs_mul, abs_of_pos h3pos] at habs
  rw [le_div_iff₀ h3pos]
  push_cast
  linarith

snip end

/-- **IMC 1999 Problem 3.**
If `f : ℝ → ℝ` satisfies the bound `|∑_{k=1}^n 3^k (f(x+k·y) - f(x-k·y))| ≤ 1`
for all `n ≥ 0` and all `x, y ∈ ℝ`, then `f` is constant.

(Note: for `n = 0` the sum is empty so the bound holds vacuously; the problem
is the same.) -/
problem imc1999_p3
    (f : ℝ → ℝ)
    (hf : ∀ n : ℕ, ∀ x y : ℝ,
        |∑ k ∈ Finset.Icc 1 n, (3 : ℝ) ^ k * (f (x + k * y) - f (x - k * y))| ≤ 1) :
    ∀ u v : ℝ, f u = f v := by
  intro u v
  -- It suffices to show |f u - f v| ≤ 2/3^n for every n ≥ 1.
  -- Then |f u - f v| = 0.
  rcases eq_or_ne u v with rfl | huv
  · rfl
  -- For each n ≥ 1, take x = (u+v)/2, y = (v-u)/(2n).
  have hbd : ∀ n : ℕ, 1 ≤ n → |f u - f v| ≤ 2 / (3 : ℝ) ^ n := by
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    set x : ℝ := (u + v) / 2
    set y : ℝ := (v - u) / (2 * n)
    have hxny : x + (n : ℝ) * y = v := by
      simp only [x, y]
      field_simp
      ring
    have hxmny : x - (n : ℝ) * y = u := by
      simp only [x, y]
      field_simp
      ring
    have h := diff_bound f hf n hn x y
    rw [hxny, hxmny] at h
    rw [abs_sub_comm]
    exact h
  -- Now |f u - f v| ≤ 2/3^n → 0, so |f u - f v| = 0.
  by_contra hne
  have habs_pos : 0 < |f u - f v| := by
    rw [abs_pos]
    intro hzero
    apply hne
    linarith
  -- Pick n large enough so 2/3^n < |f u - f v|.
  have hlim : Filter.Tendsto (fun n : ℕ => (2 : ℝ) / (3 : ℝ) ^ n) Filter.atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 : ℝ) / 3) (by norm_num) (by norm_num)
    have h2 : (fun n : ℕ => (2 : ℝ) / (3 : ℝ) ^ n) =
        (fun n : ℕ => 2 * ((1 : ℝ) / 3) ^ n) := by
      funext n
      rw [div_pow, one_pow, mul_div_assoc', mul_one]
    rw [h2]
    have := this.const_mul (2 : ℝ)
    simpa using this
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N, hN⟩ := hlim (|f u - f v|) habs_pos
  let n := max N 1
  have hnN : N ≤ n := le_max_left _ _
  have hn1 : 1 ≤ n := le_max_right _ _
  have h1 := hbd n hn1
  have h2 := hN n hnN
  rw [Real.dist_eq, sub_zero] at h2
  have h3 : (0 : ℝ) ≤ 2 / (3 : ℝ) ^ n := by positivity
  rw [abs_of_nonneg h3] at h2
  linarith

end Imc1999P3
