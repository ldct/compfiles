/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1997, Problem 2 (Day 1)

Let `∑ aₙ` be a convergent series of real numbers. Decide, for each of the
following two specific permutations of the index set `ℕ`, whether the
permuted series still converges (and to the same value, if so).

* (a) Permutation `σₐ`: write the indices in blocks
    `{1}, {2}, {3,4}, {5,...,8}, {9,...,16}, …`
  (block `k ≥ 1` is the dyadic interval `[2^{k-1}+1, 2^k]`), and within
  each block reverse the order. So the rearranged series begins
    `a₁ + a₂ + a₄ + a₃ + a₈ + a₇ + a₆ + a₅ + a₁₆ + ⋯ + a₉ + a₃₂ + ⋯`.
  *Claim:* the rearranged series converges to the same sum `S`.

* (b) Permutation `σᵦ`: write the indices in the same blocks, and within
  each block list the odd indices first (in increasing order) followed
  by the even indices (in increasing order). So the rearranged series
  begins
    `a₁ + a₂ + a₃ + a₄ + a₅ + a₇ + a₆ + a₈ + a₉ + a₁₁ + a₁₃ + a₁₅ + a₁₀ + a₁₂ + a₁₄ + a₁₆ + ⋯`.
  *Claim:* the rearranged series need not converge — for instance with
  `aₙ = (-1)^{n+1}/√n` the original alternating series converges (Leibniz)
  but the permuted one diverges.

## Proof outline (official solution)

(a) Let `S` be the sum of `∑ aₙ` and `Sₙ = ∑_{k=1}^{n} aₖ` its partial sums.
The new partial sums `Lₘ` agree with `Sₘ` whenever `m = 2^n` for some `n`,
since each block `[2^{n-1}+1, 2^n]` is permuted internally. For `m` inside
block `n`, write `m = 2^{n-1} + j` with `0 ≤ j ≤ 2^{n-1}`. Then
  `Lₘ = S_{2^{n-1}} + (a_{2^n} + a_{2^n - 1} + ⋯ + a_{2^n - j + 1})`
      = `S_{2^{n-1}} + (S_{2^n} - S_{2^n - j})`,
giving `Lₘ - S = (S_{2^{n-1}} - S) + (S_{2^n} - S) - (S_{2^n - j} - S)`.
Each of the three summands is bounded by `ε` once `n` is large, so
`|Lₘ - S| < 3ε` for all sufficiently large `m`.

(b) For `aₙ = (-1)^{n+1}/√n`: the original series converges by the
alternating series test. For the permuted series, consider the partial
sum at the position where, inside block `[2^{n-1}+1, 2^n]`, all the
`2^{n-2}` odd indices have been listed (assume `n ≥ 2`). The contribution
of those odd terms is
  `∑_{j=0}^{2^{n-2}-1} 1 / √(2^{n-1} + 2j + 1) ≥ 2^{n-2} / √(2^n) = √(2^n)/4`,
which tends to `+∞`. After subtracting `S_{2^{n-1}}` (which is bounded by
the convergence of the original series), the partial sum at this
intermediate position diverges to `+∞`, so the permuted series does not
converge.

## Status

`sorry` skeleton. We give the precise definitions of both permutations,
state both subproblems, and leave both proofs as `sorry`.

## TODO

* Part (a): formalize the partial-sum identity and the standard
  three-`ε` argument. Mathlib has `Equiv.tsum_eq` for *unconditional*
  convergence (i.e. summability), but here `∑ aₙ` is only assumed to
  converge in the partial-sum sense (i.e. `Tendsto (fun N => ∑ k in
  Finset.range N, a k) atTop (𝓝 S)`), which is strictly weaker. The proof
  requires the explicit boundary computation rather than a general
  rearrangement theorem.

* Part (b): construct the explicit `aₙ = (-1)^{n+1}/√(n+1)` (0-indexed),
  show its partial sums converge (via `tendsto_alternating_series` /
  Leibniz test in Mathlib — see `Real.tendsto_sum_alternating_of_*` or
  the `Antitone.tendsto_alternating_series` family), then exhibit the
  divergent subsequence of the permuted partial sums via the lower bound
  `√(2^n)/4`.
-/

namespace Imc1997P2

open scoped Topology BigOperators
open Filter

/-- Permutation (a) on `ℕ` (positions `p ≥ 1`).

The problem partitions the positive integers into blocks
`B_0 = {1}, B_1 = {2}, B_2 = {3,4}, B_3 = {5,…,8}, B_4 = {9,…,16}, …`,
where `B_k = [2^{k-1}+1, 2^k]` for `k ≥ 1`. Within each block the order
is reversed: position `2^{k-1} + 1 + j` (`0 ≤ j < 2^{k-1}`) maps to
value `2^k - j`.

We index from `0` and let `σₐ 0 = 0` (an unused slot). For position
`p = n + 1 ≥ 1`, the block index is `k = Nat.log2 n + 1` (so
`2^{k-1} ≤ n < 2^k`, i.e. `2^{k-1}+1 ≤ p ≤ 2^k`). Then
`j = p - 2^{k-1} - 1 = n - 2^{k-1}` and the output is
`2^k - j = 2^k - n + 2^{k-1} = 3·2^{k-1} - n`. For `p = 1` (i.e.
`n = 0`), we use the convention `Nat.log2 0 = 0`, which gives `k = 1`,
`j = 0 - 1 = 0` (truncated subtraction), output `3·1 - 0 = 3`. That is
wrong for `p = 1` so we special-case `p = 1 ↦ 1`. -/
noncomputable def sigmaA : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | (n+2) =>
    let k := Nat.log2 (n+1) + 1   -- block index, ≥ 1
    3 * 2^(k-1) - (n + 1)         -- output value

/-- Permutation (b) on `ℕ` (positions `p ≥ 1`).

Same block structure as (a): `B_k = [2^{k-1}+1, 2^k]`. Within block
`B_k` (for `k ≥ 2`, when the block has `≥ 2` elements), the first
`2^{k-2}` slots are filled with the *odd* members in increasing order,
and the next `2^{k-2}` slots with the *even* members in increasing
order. The odd members of `B_k` are `2^{k-1}+1, 2^{k-1}+3, …, 2^k - 1`
and the evens are `2^{k-1}+2, 2^{k-1}+4, …, 2^k`. So within-block
position `j ∈ [0, 2^{k-1})`:
* if `j < 2^{k-2}`, output `= 2^{k-1} + 2j + 1`;
* else, output `= 2^{k-1} + 2(j - 2^{k-2}) + 2`.

For `k = 0` (singleton `{1}`) and `k = 1` (singleton `{2}`) the block
has one element, so the permutation acts trivially. -/
noncomputable def sigmaB : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | 2     => 2
  | (n+3) =>
    let k := Nat.log2 (n+2) + 1   -- block index, ≥ 2 since n+2 ≥ 2
    let j := (n+2) - 2^(k-1)      -- 0 ≤ j < 2^{k-1}
    let h := 2^(k-2)
    if j < h then 2^(k-1) + 2*j + 1
    else 2^(k-1) + 2*(j - h) + 2

/-- An explicit witness for part (b): `aₙ = (-1)^{n+1}/√(n+1)`
(`0`-indexed, so `a 0 = 1/√1 = 1`, `a 1 = -1/√2`, etc.). The original
series converges (alternating Leibniz) but its `σᵦ`-rearrangement does
not. -/
noncomputable def witnessB (n : ℕ) : ℝ :=
  (-1) ^ (n + 1) / Real.sqrt (n + 1)

snip begin

/-- (Sanity check.) `σₐ` reproduces the first few values of the
permutation in the problem statement: positions `1,2,3,4,5,6,7,8` map
to `1,2,4,3,8,7,6,5`. -/
example : sigmaA 1 = 1 ∧ sigmaA 2 = 2 ∧ sigmaA 3 = 4 ∧ sigmaA 4 = 3 ∧
    sigmaA 5 = 8 ∧ sigmaA 6 = 7 ∧ sigmaA 7 = 6 ∧ sigmaA 8 = 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (unfold sigmaA; decide)

/-- (Sanity check.) `σᵦ` reproduces the first few values of the
permutation in the problem statement. Positions `1,…,8` map to
`1,2,3,4,5,7,6,8`; positions `9,…,16` map to `9,11,13,15,10,12,14,16`. -/
example : sigmaB 1 = 1 ∧ sigmaB 2 = 2 ∧ sigmaB 3 = 3 ∧ sigmaB 4 = 4 ∧
    sigmaB 5 = 5 ∧ sigmaB 6 = 7 ∧ sigmaB 7 = 6 ∧ sigmaB 8 = 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (unfold sigmaB; decide)

snip end

/-- Part (a): For every convergent real series `∑ aₙ` (in the partial-sum
sense), the rearrangement under `σₐ` converges to the same limit.

We index everything by `ℕ` and ignore the `n = 0` slot (`σₐ 0 = 0`,
so this slot is fixed and contributes the same to both sums). -/
problem imc1997_p2_a (a : ℕ → ℝ) (S : ℝ)
    (hS : Tendsto (fun N => ∑ k ∈ Finset.range N, a k) atTop (𝓝 S)) :
    Tendsto (fun N => ∑ k ∈ Finset.range N, a (sigmaA k)) atTop (𝓝 S) := by
  -- TODO: see file-level outline. Three-ε boundary argument.
  sorry

/-- Part (b): There exists a convergent real series `∑ aₙ` whose
rearrangement under `σᵦ` does *not* converge.

We exhibit the alternating series `aₙ = (-1)^{n+1}/√(n+1)`. -/
problem imc1997_p2_b :
    ∃ a : ℕ → ℝ,
      (∃ S : ℝ, Tendsto (fun N => ∑ k ∈ Finset.range N, a k) atTop (𝓝 S)) ∧
      ¬ ∃ T : ℝ,
        Tendsto (fun N => ∑ k ∈ Finset.range N, a (sigmaB k)) atTop (𝓝 T) := by
  refine ⟨witnessB, ?_, ?_⟩
  -- TODO: provide the alternating-series limit (Leibniz test):
  -- the partial sums of `(-1)^{n+1}/√(n+1)` converge.
  · sorry
  -- TODO: show the permuted partial sums diverge by exhibiting the
  -- subsequence at "all odd indices in block n consumed", which has
  -- value at least  S_{2^{n-1}} + √(2^n)/4 → +∞.
  · sorry

end Imc1997P2
