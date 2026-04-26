/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1999, Problem 10 (Day 2, Problem 4)

Prove that no function `f : (0, ∞) → (0, ∞)` satisfies
`f(x)^2 ≥ f(x + y) · (f(x) + y)` for all `x, y > 0`.

## Solution sketch (official)

From `f(x)^2 ≥ f(x+y) (f(x)+y)` we get
`f(x) - f(x+y) ≥ f(x) · y / (f(x) + y)`,
which shows `f` is strictly decreasing.

Fix `x > 0` and pick `n ≥ 1` with `n · f(x+1) ≥ 1`. Then for
`k = 0, …, n-1`, since `f` is decreasing and `f(x+k/n) ≥ f(x+1) ≥ 1/n`,
we have
  `f(x + k/n) - f(x + (k+1)/n) ≥ (f(x+k/n)·(1/n))/(f(x+k/n) + 1/n) ≥ 1/(2n)`.
Summing the telescoping sum gives `f(x) - f(x+1) ≥ 1/2`,
i.e. `f(x+1) ≤ f(x) - 1/2`. By induction, `f(x+m) ≤ f(x) - m/2`,
which is negative for large `m`, contradicting positivity of `f`.
-/

namespace Imc1999P10

open scoped BigOperators
open Finset

snip begin

/-- If `f(x)^2 ≥ f(x+y)·(f(x)+y)` with all values positive,
then `f(x) - f(x+y) ≥ f(x)·y / (f(x) + y)`. -/
lemma diff_lower_bound (f : ℝ → ℝ) (hpos : ∀ x, 0 < x → 0 < f x)
    (hineq : ∀ x y, 0 < x → 0 < y → f x ^ 2 ≥ f (x + y) * (f x + y))
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    f x - f (x + y) ≥ f x * y / (f x + y) := by
  have hfx : 0 < f x := hpos x hx
  have hsum : 0 < f x + y := by linarith
  have h1 : f x ^ 2 ≥ f (x + y) * (f x + y) := hineq x y hx hy
  -- f(x+y) ≤ f(x)^2 / (f x + y)
  have h2 : f (x + y) ≤ f x ^ 2 / (f x + y) := by
    rw [le_div_iff₀ hsum]
    linarith
  -- f(x) - f(x+y) ≥ f(x) - f(x)^2/(f(x)+y) = f(x)·y/(f(x)+y)
  have h3 : f x - f x ^ 2 / (f x + y) = f x * y / (f x + y) := by
    field_simp
    ring
  linarith [h3 ▸ (sub_le_sub_left h2 (f x))]

/-- `f` is strictly decreasing on positives. -/
lemma f_strict_anti (f : ℝ → ℝ) (hpos : ∀ x, 0 < x → 0 < f x)
    (hineq : ∀ x y, 0 < x → 0 < y → f x ^ 2 ≥ f (x + y) * (f x + y))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) : f b < f a := by
  set y := b - a with hy_def
  have hy : 0 < y := by simp [hy_def]; linarith
  have hxy : a + y = b := by simp [hy_def]
  have hfx : 0 < f a := hpos a ha
  have hsum : 0 < f a + y := by linarith
  have hbnd : f a - f (a + y) ≥ f a * y / (f a + y) :=
    diff_lower_bound f hpos hineq a y ha hy
  have hpos2 : 0 < f a * y / (f a + y) :=
    div_pos (mul_pos hfx hy) hsum
  rw [hxy] at hbnd
  linarith

snip end

problem imc1999_p10 :
    ¬ ∃ f : ℝ → ℝ, (∀ x, 0 < x → 0 < f x) ∧
      (∀ x y, 0 < x → 0 < y → f x ^ 2 ≥ f (x + y) * (f x + y)) := by
  rintro ⟨f, hpos, hineq⟩
  -- Step 1: f is strictly decreasing on positives.
  have hanti : ∀ {a b : ℝ}, 0 < a → a < b → f b < f a :=
    fun {a b} ha hab => f_strict_anti f hpos hineq ha hab
  -- Step 2: Show f(x+1) ≤ f(x) - 1/2 for all x > 0.
  have hkey : ∀ x : ℝ, 0 < x → f (x + 1) ≤ f x - 1 / 2 := by
    intro x hx
    have hfx1 : 0 < f (x + 1) := hpos (x + 1) (by linarith)
    -- Pick n ≥ 1 with n · f(x+1) ≥ 1.
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℝ) * f (x + 1) ≥ 1 := by
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / f (x + 1))
      refine ⟨n, ?_⟩
      have : 1 / f (x + 1) * f (x + 1) = 1 := by
        field_simp
      have hle : 1 / f (x + 1) ≤ n := le_of_lt hn
      have := mul_le_mul_of_nonneg_right hle (le_of_lt hfx1)
      linarith
    -- We need n ≥ 1.
    have hn_pos : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0
        simp at hn
        linarith
      · exact h0
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
    have hnR_pos : 0 < (n : ℝ) := by linarith
    -- For k = 0, …, n-1: f(x + k/n) - f(x + (k+1)/n) ≥ 1/(2n).
    -- Telescoping sum gives f(x) - f(x+1) ≥ 1/2.
    -- Define g k := f(x + k/n).
    set g : ℕ → ℝ := fun k => f (x + (k : ℝ) / n) with hg_def
    -- Domain points are positive.
    have hxk_pos : ∀ k : ℕ, 0 < x + (k : ℝ) / n := by
      intro k
      have : 0 ≤ (k : ℝ) / n := div_nonneg (Nat.cast_nonneg _) (le_of_lt hnR_pos)
      linarith
    have hgk_pos : ∀ k : ℕ, 0 < g k := fun k => hpos _ (hxk_pos k)
    -- Monotonicity: g k ≥ f(x+1) for k ≤ n.
    have hgk_ge : ∀ k : ℕ, k ≤ n → g k ≥ f (x + 1) := by
      intro k hk
      simp only [hg_def]
      rcases lt_or_eq_of_le hk with hlt | heq
      · -- k < n, so (k:ℝ)/n < 1, so x + k/n < x + 1, so f decreasing gives ≥
        have hkn : (k : ℝ) / n < 1 := by
          rw [div_lt_one hnR_pos]
          exact_mod_cast hlt
        have : x + (k : ℝ) / n < x + 1 := by linarith
        exact le_of_lt (hanti (hxk_pos k) this)
      · -- k = n, so (k:ℝ)/n = 1
        have : (k : ℝ) / n = 1 := by
          rw [heq, div_self (ne_of_gt hnR_pos)]
        rw [this]
    -- Pointwise step inequality.
    have hstep : ∀ k : ℕ, k < n → g k - g (k + 1) ≥ 1 / (2 * n) := by
      intro k hk
      have hxk := hxk_pos k
      have h1n : (0 : ℝ) < 1 / n := by positivity
      have hbnd : f (x + (k : ℝ) / n) - f (x + (k : ℝ) / n + 1 / n) ≥
          f (x + (k : ℝ) / n) * (1 / n) / (f (x + (k : ℝ) / n) + 1 / n) :=
        diff_lower_bound f hpos hineq _ (1/n) hxk h1n
      -- Simplify: x + k/n + 1/n = x + (k+1)/n
      have heq1 : x + (k : ℝ) / n + 1 / n = x + ((k + 1 : ℕ) : ℝ) / n := by
        push_cast
        field_simp
        ring
      rw [heq1] at hbnd
      -- Now bound the RHS from below by 1/(2n).
      -- We need f(x+k/n)/(f(x+k/n) + 1/n) ≥ 1/2, i.e., f(x+k/n) ≥ 1/n.
      have hg_ge_inv : g k ≥ 1 / n := by
        have h1 : g k ≥ f (x + 1) := hgk_ge k (le_of_lt hk)
        have h2 : (n : ℝ) * f (x + 1) ≥ 1 := hn
        have h3 : f (x + 1) ≥ 1 / n := by
          rw [ge_iff_le, div_le_iff₀ hnR_pos]
          linarith
        linarith
      -- So g k * (1/n) / (g k + 1/n) ≥ (1/n)/2 = 1/(2n).
      have hgk_pk : 0 < g k + 1 / n := by linarith [hgk_pos k]
      have hgk : 0 < g k := hgk_pos k
      have hRHS : g k * (1 / n) / (g k + 1 / n) ≥ 1 / (2 * n) := by
        rw [ge_iff_le, div_le_div_iff₀ (by positivity) hgk_pk]
        -- need: 1 * (g k + 1/n) ≤ g k * (1/n) * (2 * n)
        -- i.e., g k + 1/n ≤ 2 * g k, i.e., 1/n ≤ g k.
        have h_2n : g k * (1 / n) * (2 * (n : ℝ)) = 2 * g k := by
          field_simp
        rw [one_mul, h_2n]
        linarith
      show g k - g (k + 1) ≥ 1 / (2 * n)
      simp only [hg_def] at hbnd ⊢
      linarith
    -- Telescoping sum: f(x) - f(x+1) = g 0 - g n ≥ n · (1/(2n)) = 1/2.
    have hg0 : g 0 = f x := by simp [hg_def]
    have hgn : g n = f (x + 1) := by
      simp only [hg_def]
      congr 1
      rw [div_self (ne_of_gt hnR_pos)]
    -- Sum the telescoping differences.
    have htel : ∀ N : ℕ, g 0 - g N = ∑ k ∈ range N, (g k - g (k + 1)) := by
      intro N
      induction N with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, ← ih]
        ring
    have hsum_lb : ∑ k ∈ range n, (g k - g (k + 1)) ≥ ∑ _k ∈ range n, (1 / (2 * (n : ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      exact hstep k (Finset.mem_range.mp hk)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum_lb
    have h_simp : (n : ℝ) * (1 / (2 * (n : ℝ))) = 1 / 2 := by
      field_simp
    rw [h_simp] at hsum_lb
    have htel_n := htel n
    rw [hg0, hgn] at htel_n
    linarith
  -- Step 3: Iterate to get f(x + m) ≤ f(x) - m/2, contradicting positivity.
  -- Take x = 1. Then f(1 + m) ≤ f(1) - m/2.
  have hiter : ∀ m : ℕ, f (1 + m) ≤ f 1 - (m : ℝ) / 2 := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      have h1k_pos : (0 : ℝ) < 1 + k := by positivity
      have hk1 : f (1 + k + 1) ≤ f (1 + k) - 1 / 2 := hkey (1 + k) h1k_pos
      have heq : (1 : ℝ) + (↑(k + 1) : ℝ) = 1 + k + 1 := by push_cast; ring
      rw [heq]
      push_cast
      linarith
  -- Pick m large enough that f 1 - m/2 < 0.
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℝ) / 2 > f 1 := by
    obtain ⟨m, hm⟩ := exists_nat_gt (2 * f 1)
    refine ⟨m, ?_⟩
    linarith
  have : f (1 + m) ≤ f 1 - (m : ℝ) / 2 := hiter m
  have hlt : f 1 - (m : ℝ) / 2 < 0 := by linarith
  have hpos1m : 0 < f (1 + m) := by
    apply hpos
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  linarith

end Imc1999P10
