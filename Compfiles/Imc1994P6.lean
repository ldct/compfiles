/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1994, Problem 6

Let `f ∈ C²[0, N]` with `|f'(x)| < 1` and `f''(x) > 0` on `[0, N]`.
Let `0 ≤ m₀ < m₁ < ⋯ < m_k ≤ N` be integers with `nᵢ = f(mᵢ)` also integers.
Set `bᵢ = nᵢ - n_{i-1}`, `aᵢ = mᵢ - m_{i-1}`.

(a) Prove `-1 < b₁/a₁ < b₂/a₂ < ⋯ < b_k/a_k < 1`.

(b) For `A > 1`, show there are at most `N/A` indices `j` with `aⱼ > A`.

(c) Show `k ≤ 3 N^{2/3}`.

## Proof outline (official solution)

(a) By MVT there exists `xᵢ ∈ (m_{i-1}, mᵢ)` with
`bᵢ = f(mᵢ) - f(m_{i-1}) = (mᵢ - m_{i-1}) f'(xᵢ) = aᵢ f'(xᵢ)`,
hence `bᵢ/aᵢ = f'(xᵢ)`. From `|f'| < 1` we get `-1 < bᵢ/aᵢ < 1`.
Convexity of `f` (i.e. `f'' > 0`) makes `f'` strictly increasing, and
`x_i < mᵢ ≤ m_i < x_{i+1}` (in fact `x_i < mᵢ < x_{i+1}`) gives
`bᵢ/aᵢ = f'(xᵢ) < f'(x_{i+1}) = b_{i+1}/a_{i+1}`.

(b) Let `S_A = {j : aⱼ > A}`. Then
`N ≥ m_k - m₀ = ∑ᵢ aᵢ ≥ ∑_{j ∈ S_A} aⱼ > A · |S_A|`,
so `|S_A| < N / A`.

(c) The values `bᵢ/aᵢ` are distinct rationals in `(-1, 1)` by (a). The
number of rationals `p/q ∈ (-1,1)` with `1 ≤ q ≤ A` is at most `2A²`
(at most `2q - 1 < 2q ≤ 2A` choices of numerator for each denominator,
summed gives `≤ 2A · A`). Combining with (b), the number of indices
with `aᵢ ≤ A` is at most `2A²`, and the number with `aᵢ > A` is at most
`N/A`, hence `k ≤ N/A + 2A²`. Setting `A = N^{1/3}` gives `k ≤ 3 N^{2/3}`.
-/

namespace Imc1994P6

open scoped BigOperators

/-- Part (b): a clean form. If we have a list of positive reals `a₁, …, a_k`
with sum bounded by `N`, then the number of `aⱼ` exceeding `A > 0` is at most
`N / A`. -/
problem imc1994_p6_partb
    (k : ℕ) (a : Fin k → ℝ) (N A : ℝ) (_hA : 0 < A)
    (hpos : ∀ i, 0 < a i)
    (hsum : ∑ i, a i ≤ N) :
    ((Finset.univ : Finset (Fin k)).filter (fun j => A < a j)).card * A ≤ N := by
  -- Let S = {j : A < a j}.  Then ∑_{j ∈ S} a j ≥ |S| * A, while
  -- ∑_{j ∈ S} a j ≤ ∑ all a j ≤ N, since all a j > 0.
  set S : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter (fun j => A < a j)
    with hSdef
  have hge : ∑ j ∈ S, a j ≥ S.card * A := by
    have : ∀ j ∈ S, A ≤ a j := by
      intro j hj
      have : A < a j := (Finset.mem_filter.mp hj).2
      exact le_of_lt this
    calc S.card * A
        = ∑ _j ∈ S, A := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ S, a j := Finset.sum_le_sum this
  have hle : ∑ j ∈ S, a j ≤ ∑ j, a j := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) ?_
    intro j _ _
    exact (hpos j).le
  linarith

/-- Part (a) — the key MVT step. If `f` is differentiable on the closed
interval `[m, n]` with `m < n` and continuous on it, there is a point `x ∈ (m, n)`
with `f n - f m = (n - m) * f' x`. -/
problem imc1994_p6_parta_mvt
    (f f' : ℝ → ℝ) (m n : ℝ) (hmn : m < n)
    (hf : ∀ x ∈ Set.Icc m n, HasDerivAt f (f' x) x) :
    ∃ x ∈ Set.Ioo m n, f n - f m = (n - m) * f' x := by
  -- Standard MVT.
  have hcont : ContinuousOn f (Set.Icc m n) := by
    intro x hx
    exact (hf x hx).continuousAt.continuousWithinAt
  have hdiff : ∀ x ∈ Set.Ioo m n, HasDerivAt f (f' x) x := by
    intro x hx
    exact hf x (Set.Ioo_subset_Icc_self hx)
  obtain ⟨x, hx, hxe⟩ := exists_hasDerivAt_eq_slope f f' hmn hcont hdiff
  refine ⟨x, hx, ?_⟩
  -- hxe : f' x = (f n - f m) / (n - m)
  have hne : n - m ≠ 0 := sub_ne_zero.mpr hmn.ne'
  field_simp at hxe ⊢
  linarith [hxe]

/-- Part (c) — a clean form of the rational-count statement we need.
The number of rationals `p/q ∈ (-1, 1)` written in lowest terms with
`1 ≤ q ≤ A` is at most `2A²`.

We give the bound here in terms of arbitrary natural-number numerators and
denominators; this is the input to the final counting argument.

For each integer denominator `q` with `1 ≤ q`, the numerators `p` with
`-q < p < q` give `2q - 1` rationals `p/q ∈ (-1,1)`. Summing over
`q = 1, …, A` we get
`∑_{q=1}^A (2q - 1) = A²`.
However, different denominators can produce the *same* rational (e.g.
`1/2 = 2/4`), so we must mod out by lowest-terms equivalence. This gives
the bound `≤ 2 A²` quoted in the official solution.

The statement and full proof of (c) are left for future formalization;
see the TODO inside `imc1994_p6_partc`.
-/
problem imc1994_p6_partc
    (N : ℝ) (hN : (1 : ℝ) ≤ N) (k : ℕ)
    -- The problem data: integer points (m_i, n_i) on the graph of an
    -- increasing C² function f with |f'| < 1, f'' > 0, with m_i ∈ [0, N].
    -- Encoded abstractly via the conclusions of (a) and (b):
    (m n : Fin (k + 1) → ℤ)
    (_hm_mono : StrictMono m)
    (_hm_range : ∀ i, 0 ≤ m i ∧ (m i : ℝ) ≤ N)
    -- distinct rationals in (-1,1) for each i ∈ Fin k
    (r : Fin k → ℚ)
    (_hr_mem : ∀ i, -1 < r i ∧ r i < 1)
    (_hr_inj : Function.Injective r)
    -- The denominator `aᵢ = m_{i+1} - m_i > 0` matches the rational
    -- step `bᵢ/aᵢ`:
    (_hr_eq : ∀ i : Fin k,
      (r i).den = ((m i.succ - m i.castSucc).toNat) ∨
      (r i).den ≤ ((m i.succ - m i.castSucc).toNat)) :
    (k : ℝ) ≤ 3 * N ^ ((2 : ℝ) / 3) := by
  -- TODO: full formalization of the counting argument.
  --   1. By part (b), the number of indices i with aᵢ = m_{i+1} - m_i > A
  --      is at most N/A (apply imc1994_p6_partb to a := i ↦ aᵢ, summed
  --      telescopically against m_k - m_0 ≤ N).
  --   2. The number of indices i with aᵢ ≤ A is at most the number of
  --      distinct rationals p/q ∈ (-1,1) with 1 ≤ q ≤ A, which is at most
  --      2A² (the bound coming from |{p/q : -q < p < q, 1 ≤ q ≤ A}| ≤ 2A²).
  --   3. Combining: k ≤ N/A + 2A².  Optimise by choosing A = N^{1/3}:
  --        N/A + 2A² = N^{2/3} + 2N^{2/3} = 3 N^{2/3}.
  --   4. This requires an integer choice of A; the official argument
  --      handles this either by taking A = ⌈N^{1/3}⌉ and absorbing the
  --      rounding into the constant, or by working with real A and then
  --      noting that the statement is monotone in A.
  sorry

end Imc1994P6
