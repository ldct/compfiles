/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1995, Problem 10 (Day 2 Problem 4)

(a) Prove that for every `ε > 0` there exist `n` and reals
`λ₁, …, λₙ` such that
`max_{x ∈ [-1, 1]} |x - Σ_{k=1}^n λ_k x^{2k+1}| < ε`.

(b) Prove that for every continuous odd function `f` on `[-1, 1]` and every
`ε > 0` there exist `n` and reals `μ₁, …, μₙ` with
`max_{x ∈ [-1, 1]} |f(x) - Σ_{k=1}^n μ_k x^{2k+1}| < ε`.

## Proof outline (official solution)

(a) Choose `n` with `(1 - ε²)^n ≤ ε` (or similar). Then take
`λ_k = (-1)^{k+1} · binom(n, k)`. The identity
`x · (1 - x²)^n = x · Σ_{k=0}^n (-1)^k · binom(n,k) · x^{2k}
                = x - Σ_{k=1}^n λ_k · x^{2k+1}`
together with the elementary bound `|x · (1 - x²)^n| ≤ ε` on `[-1, 1]` (split
into `|x| ≤ ε` vs `|x| > ε`, using `1 - x² ≤ 1 - ε²` in the latter case) gives
the claim.

(b) By the Weierstrass approximation theorem, there is a polynomial `p ∈ ℝ[X]`
with `|f(x) - p(x)| < ε/2` on `[-1, 1]`. Let `q(x) = (p(x) - p(-x))/2` be the
odd part of `p`. Since `f` is odd,
`|f(x) - q(x)| ≤ (|f(x) - p(x)| + |f(-x) - p(-x)|)/2 < ε/2`.
Write `q(x) = b₀ x + Σ_{k=1}^m b_k x^{2k+1}`. If `b₀ = 0` we are done.
Otherwise apply (a) with tolerance `ε / (2|b₀|)` to obtain
`λ₁, …, λ_n` with `|x - Σ λ_k x^{2k+1}| < ε / (2 |b₀|)`, hence
`|b₀ x - Σ b₀ λ_k x^{2k+1}| < ε/2`, and combining with the previous bound
yields the desired approximation by an odd polynomial with only odd degrees
`≥ 3`.
-/

namespace Imc1995P10

open Real

/-- Bound: For `x ∈ [-1, 1]`, the function `x · (1 - x²)^n` satisfies
`|x · (1 - x²)^n| ≤ ε` whenever `(1 - ε²)^n ≤ ε` (and `0 < ε ≤ 1`). -/
private lemma part_a_bound (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (n : ℕ)
    (hn : (1 - ε ^ 2) ^ n ≤ ε) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |x * (1 - x ^ 2) ^ n| ≤ ε := by
  obtain ⟨hx1, hx2⟩ := hx
  have hxabs : |x| ≤ 1 := abs_le.mpr ⟨hx1, hx2⟩
  have hx2_le_1 : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x, sq_nonneg (1 - x), sq_nonneg (1 + x)]
  have hx2_nn : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  have hone_minus_x2_nn : (0 : ℝ) ≤ 1 - x ^ 2 := by linarith
  have hone_minus_x2_le_1 : 1 - x ^ 2 ≤ 1 := by linarith
  have hpow_nn : (0 : ℝ) ≤ (1 - x ^ 2) ^ n := pow_nonneg hone_minus_x2_nn n
  have hone_minus_eps_nn : (0 : ℝ) ≤ 1 - ε ^ 2 := by nlinarith [hε1, sq_nonneg (1 - ε), hε.le]
  by_cases h : |x| ≤ ε
  · have hpow_le_1 : (1 - x ^ 2) ^ n ≤ 1 := pow_le_one₀ hone_minus_x2_nn hone_minus_x2_le_1
    rw [abs_mul, abs_of_nonneg hpow_nn]
    calc |x| * (1 - x ^ 2) ^ n ≤ ε * 1 := by
            apply mul_le_mul h hpow_le_1 hpow_nn (le_of_lt hε)
      _ = ε := by ring
  · simp only [not_le] at h
    have hx2_gt : x ^ 2 > ε ^ 2 := by
      have habs : |x| ^ 2 = x ^ 2 := sq_abs x
      have hε_nn : 0 ≤ ε := le_of_lt hε
      nlinarith [habs, abs_nonneg x, h, hε_nn]
    have hone_minus : 1 - x ^ 2 < 1 - ε ^ 2 := by linarith
    have hpow_le : (1 - x ^ 2) ^ n ≤ (1 - ε ^ 2) ^ n :=
      pow_le_pow_left₀ hone_minus_x2_nn (le_of_lt hone_minus) n
    rw [abs_mul, abs_of_nonneg hpow_nn]
    calc |x| * (1 - x ^ 2) ^ n ≤ 1 * ((1 - ε ^ 2) ^ n) := by
            apply mul_le_mul hxabs hpow_le hpow_nn zero_le_one
      _ = (1 - ε ^ 2) ^ n := by ring
      _ ≤ ε := hn

/-- Existence of `n` with `(1 - ε²)^n ≤ ε` for `0 < ε < 1`. -/
private lemma exists_pow_le (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ n : ℕ, (1 - ε ^ 2) ^ n ≤ ε := by
  have hε2_pos : 0 < ε ^ 2 := by positivity
  have hε2_lt_1 : ε ^ 2 < 1 := by nlinarith
  have hbase_nn : (0 : ℝ) ≤ 1 - ε ^ 2 := by linarith
  have hbase_lt_1 : 1 - ε ^ 2 < 1 := by linarith
  have htends : Filter.Tendsto (fun n : ℕ => (1 - ε ^ 2) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase_nn hbase_lt_1
  rcases (htends.eventually (eventually_le_nhds hε)).exists with ⟨n, hn⟩
  exact ⟨n, hn⟩

/-- Identity: `x · (1 - x²)^n = x - Σ_{k=1}^n (-1)^{k+1} · binom(n,k) · x^{2k+1}`. -/
private lemma key_identity (x : ℝ) (n : ℕ) :
    x - ∑ k ∈ Finset.Icc 1 n,
        ((-1 : ℝ) ^ (k + 1) * (n.choose k)) * x ^ (2 * k + 1)
      = x * (1 - x ^ 2) ^ n := by
  -- Use binomial expansion: (1 + (-x²))^n = Σ_{k=0}^n binom(n,k) (-x²)^k.
  have hbinom : (1 - x ^ 2) ^ n =
      ∑ k ∈ Finset.range (n + 1), (n.choose k) * ((-1 : ℝ) ^ k) * (x ^ 2) ^ k := by
    have h := add_pow (-(x ^ 2)) (1 : ℝ) n
    simp only [one_pow, mul_one] at h
    rw [show (1 : ℝ) - x ^ 2 = -(x ^ 2) + 1 by ring, h]
    apply Finset.sum_congr rfl
    intro k _
    rw [neg_pow]
    ring
  rw [hbinom, Finset.mul_sum]
  -- Split off the k=0 term.
  rw [Finset.sum_range_succ' (fun k => x * ((n.choose k) * ((-1 : ℝ) ^ k) * (x ^ 2) ^ k)) n]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one]
  -- Reindex Icc 1 n to range n via k ↦ k+1.
  have hreindex : ∑ k ∈ Finset.Icc 1 n,
      ((-1 : ℝ) ^ (k + 1) * (n.choose k)) * x ^ (2 * k + 1)
      = ∑ k ∈ Finset.range n,
          ((-1 : ℝ) ^ (k + 2) * (n.choose (k + 1))) * x ^ (2 * (k + 1) + 1) := by
    refine Finset.sum_nbij' (fun k => k - 1) (fun k => k + 1) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      simp only [Finset.mem_range]
      omega
    · intro a ha
      simp only [Finset.mem_range] at ha
      simp only [Finset.mem_Icc]
      omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      show a - 1 + 1 = a
      omega
    · intro a ha
      simp only [Finset.mem_range] at ha
      show a + 1 - 1 = a
      omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      show ((-1 : ℝ) ^ (a + 1) * (n.choose a)) * x ^ (2 * a + 1)
        = ((-1 : ℝ) ^ ((a - 1) + 2) * (n.choose ((a - 1) + 1))) * x ^ (2 * ((a - 1) + 1) + 1)
      have hk1 : a - 1 + 1 = a := by omega
      have hk2 : a - 1 + 2 = a + 1 := by omega
      rw [hk1, hk2]
  rw [hreindex]
  -- Both sides as range-n sums; show termwise equality matches.
  have hpow_eq : ∀ k : ℕ, x ^ (2 * (k + 1) + 1) = x * (x ^ 2) ^ (k + 1) := fun k => by
    rw [show 2 * (k + 1) + 1 = 1 + 2 * (k + 1) by omega, pow_add, pow_one,
        ← pow_mul, mul_comm 2 (k + 1)]
  -- Show: x - Σ_{k} ((-1)^{k+2} * choose(n,k+1)) * x^{2(k+1)+1} = (Σ_k x * choose(n,k+1) * (-1)^{k+1} * (x²)^{k+1}) + x * 1
  have : ∑ k ∈ Finset.range n,
      ((-1 : ℝ) ^ (k + 2) * (n.choose (k + 1))) * x ^ (2 * (k + 1) + 1)
    = -∑ k ∈ Finset.range n,
        x * (↑(n.choose (k + 1)) * (-1) ^ (k + 1) * (x ^ 2) ^ (k + 1)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [hpow_eq]
    have : ((-1 : ℝ) ^ (k + 2)) = -((-1) ^ (k + 1)) := by
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
      ring
    rw [this]
    ring
  rw [this]
  ring

/-- Part (a) statement. -/
def PartA : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ (n : ℕ) (lam : ℕ → ℝ),
      ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        |x - ∑ k ∈ Finset.Icc 1 n, lam k * x ^ (2 * k + 1)| < ε

/-- Part (b) statement. -/
def PartB : Prop :=
  ∀ (f : ℝ → ℝ), ContinuousOn f (Set.Icc (-1 : ℝ) 1) →
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, f (-x) = -f x) →
    ∀ ε : ℝ, 0 < ε →
      ∃ (n : ℕ) (mu : ℕ → ℝ),
        ∀ x ∈ Set.Icc (-1 : ℝ) 1,
          |f x - ∑ k ∈ Finset.Icc 1 n, mu k * x ^ (2 * k + 1)| < ε

/-- Combined statement of Problem 10. -/
problem imc1995_p10 : PartA ∧ PartB := by
  refine ⟨?_, ?_⟩
  · -- Part (a)
    intro ε hε
    -- Choose ε' < ε with ε' < 1: take ε' = min(ε/2, 1/4).
    set ε' : ℝ := min (ε / 2) (1 / 4) with hε'_def
    have hε'_pos : 0 < ε' := lt_min (by linarith) (by norm_num)
    have hε'_lt_ε : ε' < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hε'_lt_1 : ε' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hε'_le_1 : ε' ≤ 1 := le_of_lt hε'_lt_1
    obtain ⟨n, hn⟩ := exists_pow_le ε' hε'_pos hε'_lt_1
    refine ⟨n, fun k => (-1 : ℝ) ^ (k + 1) * (n.choose k), ?_⟩
    intro x hx
    rw [show (∑ k ∈ Finset.Icc 1 n, ((-1 : ℝ) ^ (k + 1) * ↑(n.choose k)) * x ^ (2 * k + 1))
           = (∑ k ∈ Finset.Icc 1 n, ((-1 : ℝ) ^ (k + 1) * (n.choose k)) * x ^ (2 * k + 1))
           from rfl]
    have hidentity := key_identity x n
    have heq : x - ∑ k ∈ Finset.Icc 1 n,
        ((-1 : ℝ) ^ (k + 1) * ↑(n.choose k)) * x ^ (2 * k + 1)
        = x * (1 - x ^ 2) ^ n := hidentity
    rw [heq]
    have hbound := part_a_bound ε' hε'_pos hε'_le_1 n hn x hx
    linarith
  · -- Part (b): TODO. Sketch outlined in the file docstring.
    --
    -- Plan:
    --
    -- (1) Use `Polynomial.exists_polynomial_near_of_continuousOn` (Mathlib's
    --     Weierstrass approximation theorem on `[a, b]`) with `a = -1, b = 1`
    --     and tolerance `ε / 2` to obtain `p : ℝ[X]` with
    --     `|f x - p.eval x| < ε / 2` on `[-1, 1]`.
    --
    -- (2) Form the odd part `q := (p - p.comp (-X)) / 2`. Since `f` is odd,
    --     bound `|f x - q.eval x|
    --         ≤ (|f x - p.eval x| + |f (-x) - p.eval (-x)|)/2 < ε/2`.
    --
    -- (3) `q` has only odd-degree monomials, so write
    --       `q.eval x = b₀ x + Σ_{k=1}^m b_k x^{2k+1}`
    --     with `b₀ := q.coeff 1` and `b_k := q.coeff (2 k + 1)` for `k ≥ 1`.
    --     The even-degree coefficients of `q` all vanish.
    --
    -- (4) If `b₀ = 0`, return `μ_k := b_k`. Otherwise apply Part (a) with
    --     tolerance `ε / (2 |b₀|)` to obtain `n'` and `λ_k` with
    --     `|x - Σ_{k=1}^{n'} λ_k x^{2k+1}| < ε / (2 |b₀|)` on `[-1, 1]`.
    --     Multiplying by `|b₀|`,
    --     `|b₀ x - Σ_{k=1}^{n'} b₀ λ_k x^{2k+1}| < ε / 2`.
    --
    -- (5) Combine: define `μ_k := b_k + b₀ · λ_k` (with `λ_k = 0` for `k > n'`,
    --     and `b_k = 0` for `k > m`); take `n := max n' m`. By the triangle
    --     inequality,
    --       `|f x - Σ μ_k x^{2k+1}|
    --         ≤ |f x - q.eval x| + |b₀ x - Σ b₀ λ_k x^{2k+1}|
    --         < ε / 2 + ε / 2 = ε`.
    sorry

end Imc1995P10
