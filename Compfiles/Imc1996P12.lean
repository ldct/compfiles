/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1996, Problem 12
(Day 2, Problem 6) — **Carleman's inequality**.

(i) For every positive sequence `a : ℕ → ℝ` (with `a n > 0` for `n ≥ 1`)
such that `∑ a_n` converges,
  `∑_{n ≥ 1} (a_1 a_2 ⋯ a_n)^(1/n) < e · ∑_{n ≥ 1} a_n`.

(ii) The constant `e` is sharp: for every `ε > 0`, there exists a
positive sequence with `∑ a_n` convergent and
  `∑_{n ≥ 1} (a_1 ⋯ a_n)^(1/n) > (e - ε) · ∑ a_n`.

## Proof outline (official solution)

(i) Set `c_n = (n+1)^n / n^(n-1)`. Then `c_1 c_2 ⋯ c_n = (n+1)^n`.
By the AM-GM inequality on `a_1 c_1, …, a_n c_n`,
  `(a_1 c_1 ⋯ a_n c_n)^(1/n) ≤ (a_1 c_1 + ⋯ + a_n c_n) / n`,
so
  `(a_1 ⋯ a_n)^(1/n) = (a_1 c_1 ⋯ a_n c_n)^(1/n) / (n+1)`
                    `≤ (a_1 c_1 + ⋯ + a_n c_n) / (n(n+1))`.
Summing in `n` and switching the order of summation,
  `∑_{n ≥ 1} (a_1 ⋯ a_n)^(1/n)
     ≤ ∑_{n ≥ 1} a_n c_n · ∑_{m ≥ n} 1/(m(m+1))
     = ∑_{n ≥ 1} a_n c_n / n
     = ∑_{n ≥ 1} a_n (1 + 1/n)^n
     < e · ∑_{n ≥ 1} a_n`,
using the telescoping `∑_{m ≥ n} 1/(m(m+1)) = 1/n` and the strict
inequality `(1 + 1/n)^n < e`.

(ii) Construct `a_n = n^(n-1) (n+1)^(-n)` for `n ≤ N`, then
`a_n = 2^(-n)` for `n > N`. Then `(a_1 ⋯ a_n)^(1/n) = 1/(n+1)` for
`n ≤ N`, and the partial sum `∑_{n=1}^{N} 1/(n+1)` grows like
`log N → ∞`. With `(1 + 1/n)^n > e - ε/2` for `n` large, choosing `N`
large enough gives `∑(a_1 ⋯ a_n)^(1/n) > (e - ε) ∑ a_n`.

## Status

`sorry` skeleton for both parts, with the key auxiliary lemmas
`prod_c_eq` (the product `c_1 ⋯ c_n = (n+1)^n`),
`one_div_mul_succ_eq_sub` (the telescoping decomposition
`1/(m(m+1)) = 1/m − 1/(m+1)`), and `c_div_n` (the identity
`c(n+1)/(n+1) = (1 + 1/(n+1))^(n+1)`) all fully proved.
A full proof would additionally require:

* the strict inequality `(1 + 1/n)^n < e` (uniformly in `n ≥ 1`);
* an exchange-of-summation step on a doubly-indexed nonnegative series;
* divergence of the harmonic tail `∑_{n=K+1}^N 1/n → ∞` for the sharpness
  argument.
-/

namespace Imc1996P12

open scoped Topology BigOperators
open Filter Real

/-- The auxiliary sequence `c n = (n+1)^n / n^(n-1)` (with `c 1 = 4`,
`c 2 = 27/4`, …). We index from `n ≥ 1`; we set `c 0 = 0` for
convenience. -/
noncomputable def c : ℕ → ℝ
  | 0 => 0
  | n + 1 => ((n + 2 : ℝ)) ^ (n + 1) / ((n + 1 : ℝ)) ^ n

/-- Geometric mean `G a n = (a 1 · a 2 ⋯ a n)^(1/n)`. -/
noncomputable def G (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∏ k ∈ Finset.Ioc 0 n, a k) ^ ((n : ℝ)⁻¹)

snip begin

/-- The product `c 1 · c 2 ⋯ c n = (n+1)^n`. -/
lemma prod_c_eq (n : ℕ) :
    ∏ k ∈ Finset.Ioc 0 n, c k = ((n + 1 : ℝ)) ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_Ioc_succ_top (by omega), ih]
    -- LHS = (m+1)^m · c (m+1) = (m+1)^m · (m+2)^(m+1) / (m+1)^m = (m+2)^(m+1)
    unfold c
    push_cast
    have h1 : ((m + 1 : ℝ)) ≠ 0 := by positivity
    have h2 : ((m + 1 : ℝ)) ^ m ≠ 0 := pow_ne_zero _ h1
    field_simp
    ring

/-- Partial telescoping: for `n ≥ 1`, `1/(m(m+1)) = 1/m - 1/(m+1)`. -/
lemma one_div_mul_succ_eq_sub (m : ℕ) (hm : 1 ≤ m) :
    (1 : ℝ) / ((m : ℝ) * (m + 1)) = 1 / (m : ℝ) - 1 / ((m : ℝ) + 1) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hm1ne : ((m : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- Identity: `c (n+1) / (n+1) = (1 + 1/(n+1))^(n+1)`. -/
lemma c_div_n (n : ℕ) :
    c (n + 1) / ((n + 1 : ℝ)) = (1 + 1 / ((n + 1 : ℝ))) ^ (n + 1) := by
  have h1 : ((n + 1 : ℝ)) ≠ 0 := by positivity
  have h2 : ((n + 1 : ℝ)) ^ n ≠ 0 := pow_ne_zero _ h1
  unfold c
  rw [show (1 : ℝ) + 1 / (n + 1 : ℝ) = (n + 2) / (n + 1) by field_simp; ring]
  rw [div_pow]
  field_simp
  ring

/-- `c (n+1) > 0`. -/
lemma c_succ_pos (n : ℕ) : 0 < c (n + 1) := by
  unfold c
  apply div_pos
  · positivity
  · positivity

/-- `c 0 = 0`. -/
@[simp] lemma c_zero : c 0 = 0 := rfl

snip end

/-- Carleman's inequality (forward direction).
For any positive sequence `a : ℕ → ℝ` with `a n > 0` for all `n ≥ 1`
and `∑ a_n` (over `n ≥ 1`) summable, we have
  `∑_{n ≥ 1} (a_1 ⋯ a_n)^(1/n) < e · ∑_{n ≥ 1} a_n`,
where the geometric mean uses the `n`-th root.
-/
problem imc1996_p12_part_i
    (a : ℕ → ℝ) (ha_pos : ∀ n, 1 ≤ n → 0 < a n)
    (ha_sum : Summable (fun n => a (n + 1))) :
    Summable (fun n => G a (n + 1)) ∧
    (∑' n : ℕ, G a (n + 1)) < Real.exp 1 * ∑' n : ℕ, a (n + 1) := by
  -- TODO: full formalization. Outline:
  --
  -- Set `c n = (n+1)^n / n^(n-1)`, so `c_1 ⋯ c_n = (n+1)^n` (`prod_c_eq`).
  --
  -- Step 1. AM-GM on the `n` numbers `a_1 c_1, …, a_n c_n` (with all
  --   `a_k c_k > 0`):
  --     (∏_{k=1..n} a_k c_k)^(1/n) ≤ (∑_{k=1..n} a_k c_k) / n,
  --   i.e.
  --     (a_1 ⋯ a_n)^(1/n) · (n+1) ≤ (∑ a_k c_k) / n,
  --   so
  --     G a n = (a_1 ⋯ a_n)^(1/n) ≤ (∑_{k=1..n} a_k c_k) / (n (n+1))
  --                                = ∑_{k=1..n} a_k c_k · (1/n - 1/(n+1)).
  --
  -- Step 2. Sum over `n ≥ 1` and exchange order of summation:
  --     ∑_{n ≥ 1} G a n
  --        ≤ ∑_{n ≥ 1} ∑_{k=1..n} a_k c_k / (n(n+1))
  --        = ∑_{k ≥ 1} a_k c_k · ∑_{n ≥ k} 1/(n(n+1))
  --        = ∑_{k ≥ 1} a_k c_k · (1/k)        [telescoping]
  --        = ∑_{k ≥ 1} a_k · (1 + 1/k)^k       [by `c_div_n`]
  --        < e · ∑_{k ≥ 1} a_k                  [since `(1 + 1/k)^k < e`].
  --
  -- The last strict inequality uses `(1 + 1/k)^k < e` for all `k ≥ 1`,
  -- combined with summability (one strict term suffices, and all are
  -- ≤ e). Summability of `G a` follows from the comparison.
  sorry

/-- Sharpness of Carleman's inequality.
For every `ε > 0`, there exists a positive summable sequence `a` such
that
  `∑_{n ≥ 1} (a_1 ⋯ a_n)^(1/n) > (e - ε) · ∑_{n ≥ 1} a_n`.
-/
problem imc1996_p12_part_ii :
    ∀ ε : ℝ, 0 < ε →
      ∃ (a : ℕ → ℝ),
        (∀ n, 1 ≤ n → 0 < a n) ∧
        Summable (fun n => a (n + 1)) ∧
        Summable (fun n => G a (n + 1)) ∧
        (Real.exp 1 - ε) * (∑' n : ℕ, a (n + 1)) < ∑' n : ℕ, G a (n + 1) := by
  -- TODO: full formalization. Outline:
  --
  -- Choose `K` so that `(1 + 1/n)^n > e - ε/2` for all `n > K`.
  -- For a parameter `N > K`, set
  --   a n = n^(n-1) / (n+1)^n           for 1 ≤ n ≤ N,
  --   a n = 2^(-n)                       for n > N.
  -- Then for `1 ≤ n ≤ N`,
  --   (a_1 ⋯ a_n)^(1/n)
  --     = ( ∏_{k=1..n} k^(k-1) / (k+1)^k )^(1/n)
  --     = ( 1 / (n+1)^n )^(1/n) · ( ∏ k^(k-1) / k^(k-1) )
  --     = 1 / (n+1)
  -- (the products of `k^(k-1)` cancel in numerator and denominator after
  -- shifting the index in the denominator: ∏ k^(k-1) ∏ (k+1)^k =
  -- ∏_{k=1..n} k^(k-1) · ∏_{k=2..n+1} k^(k-1) = (n+1)^n ∏ k^(k-1)·k^(k-1)/…).
  --
  -- Hence ∑_{n=1..N} G a n ≥ ∑_{n=1..N} 1/(n+1) ≥ ∑_{n=K+1..N} 1/(n+1).
  --
  -- For the denominator: ∑_{n=1..K} a_n + ∑_{n>N} 2^(-n) is uniformly
  -- small, so by choosing `N` large enough so that `∑_{n=K+1..N} 1/n`
  -- dominates, we obtain
  --   ∑ G ≥ (e - ε/2) ∑_{n=K+1..N} a_n - O(ε)
  --       > (e - ε) · ∑ a_n.
  sorry

end Imc1996P12
