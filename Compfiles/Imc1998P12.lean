/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1998, Problem 12 (Day 2, Problem 6)

Let `a₁, a₂, …` be a sequence of distinct real numbers in `(0, 1)` and let
`b₁, b₂, …` be a sequence of nonnegative reals. Define `f : (0, 1) → [0, ∞)`
by `f(aₙ) = bₙ` and `f(x) = 0` for `x ∉ {aₙ}`.

* (a) Prove that if `∑ bₙ < ∞`, then `f` is differentiable at some
  point `x ∈ (0, 1)`.
* (b) Prove that for every nonnegative sequence `(bₙ)` with `∑ bₙ = ∞`, there
  exists a sequence `(aₙ)` of distinct points in `(0, 1)` such that the
  associated `f` is nowhere differentiable on `(0, 1)`.

## Solution sketch (official IMC solution)

**Part (a).** Let `B = ∑ bₙ`. Choose increasing indices `0 = N₀ < N₁ < N₂ < ⋯`
such that `∑_{n ≥ Nₖ} bₙ ≤ B / 4ᵏ`. Set `cₙ = 2ᵏ / (5 B)` for `Nₖ ≤ n < Nₖ₊₁`.
Then `cₙ → ∞` while
`∑ cₙ bₙ = ∑ₖ ∑_{Nₖ ≤ n < Nₖ₊₁} cₙ bₙ ≤ ∑ₖ (2ᵏ / (5B)) (B / 4ᵏ) = 2/5`.

Form open intervals `Iₙ = (aₙ - cₙ bₙ, aₙ + cₙ bₙ)`; the total length is at
most `2 · 2/5 = 4/5 < 1`. Hence there exists `x₀ ∈ (0, 1)` with `x₀ ∉ ⋃ Iₙ`
(in particular, `x₀` is not any `aₙ` so `f(x₀) = 0`).

For any `x ≠ x₀` in `(0, 1)` we estimate `(f(x) - f(x₀)) / (x - x₀)`:
* if `x` is not an `aₙ`, the difference quotient is `0`;
* if `x = aₙ`, then `|aₙ - x₀| ≥ cₙ bₙ` since `x₀ ∉ Iₙ`, so the absolute value
  of the difference quotient is `bₙ / |aₙ - x₀| ≤ 1 / cₙ`.

Since `cₙ → ∞`, given `ε > 0`, only finitely many `n` have `1/cₙ ≥ ε`, and
those `aₙ` are at distance `≥ cₙ bₙ > 0` from `x₀`. So there is a punctured
neighbourhood of `x₀` on which the difference quotient has absolute value
`< ε`, proving `f'(x₀) = 0`.

**Part (b).** Suppose `∑ bₙ = ∞`. Choose `0 < βₙ ≤ bₙ` with `βₙ → 0` and
`∑ βₙ = ∞` (any tail-decreasing rescaling works; e.g., `βₙ = min(bₙ, 1/n)`
after pruning the zero-`bₙ` indices). Now choose `aₙ ∈ (0, 1)` so that the
intervals `(aₙ - βₙ, aₙ + βₙ) ∩ (0, 1)` cover every point of `(0, 1)`
infinitely often (since `∑ βₙ = ∞`, we can place them in successive sweeps
across `(0, 1)`); the `aₙ` can be chosen distinct.

If `f` were differentiable at `x₀ ∈ (0, 1)` then in particular `f` would be
continuous at `x₀`, forcing `f(x₀) = 0` (otherwise, pick `x` not in the
sequence with `f(x) = 0` near `x₀`). The derivative `f'(x₀)` would then be
some real number `L`; for the difference quotient to remain bounded near
`x₀` we need points with `f(x) ≠ 0` to satisfy `b_n ≤ (|L| + 1) |a_n - x₀|`
for `aₙ` close to `x₀`. But by construction, infinitely many `n` have
`x₀ ∈ (aₙ - βₙ, aₙ + βₙ)` and `βₙ` arbitrarily small. For those `n`,
`|aₙ - x₀| < βₙ ≤ bₙ`, so the difference quotient
`bₙ / |aₙ - x₀| > 1`, and `aₙ → x₀` along this subsequence, contradicting
`f'(x₀) = L`.

## Status

This is a sorry-skeleton. The statements of both parts are formalised. Both
proofs are involved analytic arguments and are left as `sorry` with detailed
TODOs.

The statement in part (b) is given the form: for every sequence `b : ℕ → ℝ`
of strictly positive reals with `∑ b = ∞`, there exists an injective
`a : ℕ → ℝ` with each `a n ∈ (0, 1)` such that the associated function `f`
is not differentiable at any point of `(0, 1)`.
-/

namespace Imc1998P12

open Set Filter Topology

open Classical in
/-- The function `f : ℝ → ℝ` associated to sequences `a : ℕ → ℝ` and
`b : ℕ → ℝ`: `f(aₙ) = bₙ` for the smallest such `n`, and `f(x) = 0` for `x`
not in the range of `a`. (We choose `f(x) = 0` outside `(0,1)` as well.) -/
noncomputable def fSeq (a b : ℕ → ℝ) (x : ℝ) : ℝ :=
  if h : ∃ n, a n = x then b (Nat.find h) else 0

/-- On the range of `a` (with `a` injective), `fSeq a b (a n) = b n`. -/
lemma fSeq_apply_of_injective {a b : ℕ → ℝ} (ha : Function.Injective a) (n : ℕ) :
    fSeq a b (a n) = b n := by
  classical
  unfold fSeq
  have h : ∃ m, a m = a n := ⟨n, rfl⟩
  rw [dif_pos h]
  have hfind : a (Nat.find h) = a n := Nat.find_spec h
  exact congrArg b (ha hfind)

/-- Outside the range of `a`, `fSeq a b x = 0`. -/
lemma fSeq_apply_of_notMem_range {a b : ℕ → ℝ} {x : ℝ}
    (hx : ∀ n, a n ≠ x) : fSeq a b x = 0 := by
  classical
  unfold fSeq
  have h : ¬ ∃ n, a n = x := fun ⟨n, hn⟩ => hx n hn
  rw [dif_neg h]

/-- IMC 1998 P12, part (a). If `(bₙ)` is a nonnegative summable sequence and
`(aₙ)` is an injective sequence in `(0, 1)`, then the associated function
`f = fSeq a b` is differentiable at some point `x ∈ (0, 1)`. -/
problem imc1998_p12a (a b : ℕ → ℝ)
    (_ha_inj : Function.Injective a)
    (_ha_mem : ∀ n, a n ∈ Ioo (0 : ℝ) 1)
    (_hb_nonneg : ∀ n, 0 ≤ b n)
    (_hb_summable : Summable b) :
    ∃ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ (fSeq a b) x := by
  -- TODO: Formalise the official solution.
  --
  -- Step 1: Let B := ∑' n, b n. If B = 0 then b n = 0 for all n, so
  -- fSeq a b ≡ 0 and any x ∈ (0,1) works.
  --
  -- Step 2: Otherwise choose strictly increasing N : ℕ → ℕ with N 0 = 0 and
  -- ∑' n with n ≥ N k, b n ≤ B / 4 ^ k. Define c : ℕ → ℝ on the partition
  --   c n = 2 ^ k / (5 * B)   when N k ≤ n < N (k+1).
  -- Show c n → ∞ (Filter.Tendsto c atTop atTop) and ∑ n, c n * b n ≤ 2/5.
  --
  -- Step 3: Form intervals I n := Ioo (a n - c n * b n) (a n + c n * b n).
  -- Their total length is ∑ 2 * c n * b n ≤ 4/5 < 1. By measure / outer
  -- measure, the union ⋃ I n cannot cover the unit interval (0,1), so there
  -- exists x₀ ∈ Ioo 0 1 with x₀ ∉ ⋃ n, I n.
  --
  -- Step 4: Show fSeq a b is differentiable at x₀ with derivative 0.
  -- For any sequence x_k → x₀ with x_k ≠ x₀, write each x_k as either
  --   (a) not in range(a), so (fSeq a b x_k - fSeq a b x₀) / (x_k - x₀) = 0,
  --   (b) x_k = a (n_k), in which case |x_k - x₀| ≥ c (n_k) * b (n_k), so
  --       |(fSeq a b x_k - fSeq a b x₀) / (x_k - x₀)| ≤ 1 / c (n_k).
  -- Combined with c n → ∞ we get that the difference quotient tends to 0.
  --
  -- A clean Lean phrasing uses `HasDerivAt (fSeq a b) 0 x₀`, which unfolds to
  -- a `Filter.Tendsto` statement; one then bounds the difference quotient by
  -- `max 0 (sSup_{n with a n ∈ Ioo (x₀ - δ) (x₀ + δ), a n ≠ x₀} 1 / c n)`
  -- and sends `δ → 0`.
  sorry

/-- IMC 1998 P12, part (b). For every strictly positive sequence `(bₙ)` with
`∑ bₙ = ∞`, there exists an injective sequence `(aₙ)` of points in `(0, 1)`
such that the associated function `f = fSeq a b` is differentiable at no
point of `(0, 1)`. -/
problem imc1998_p12b (b : ℕ → ℝ)
    (_hb_pos : ∀ n, 0 < b n)
    (_hb_not_summable : ¬ Summable b) :
    ∃ a : ℕ → ℝ, Function.Injective a ∧ (∀ n, a n ∈ Ioo (0 : ℝ) 1) ∧
      ∀ x ∈ Ioo (0 : ℝ) 1, ¬ DifferentiableAt ℝ (fSeq a b) x := by
  -- TODO: Formalise the official solution.
  --
  -- Step 1: Construct a sequence β : ℕ → ℝ with 0 < β n ≤ b n, β n → 0, and
  -- ∑ β n = ∞ (i.e. ¬ Summable β). For example, set β n := min (b n) (1 / (n+1));
  -- then ∑ β n ≥ ∑ ?  needs care. A clean construction: re-index so that
  -- ∑_{n=Nₖ}^{Nₖ₊₁ - 1} b n ≥ 1 for all k, then let β n = (1 / 2^k) on each
  -- block; this makes β n → 0 and ∑ β n = ∑_k (1/2^k)(Nₖ₊₁ - Nₖ) which can be
  -- arranged to diverge while β n ≤ b n on the block. (Care: must ensure each
  -- β n ≤ b n; pick β n = min (b n) (1/2^k).)
  --
  -- Step 2: Construct a : ℕ → ℝ of distinct points in (0,1) such that for each
  -- x ∈ (0,1) and each ε > 0, infinitely many n satisfy
  -- |a n - x| < β n  and  β n < ε.
  -- Concretely: process n in successive sweeps; in sweep k, place the points
  -- a_{Nₖ},…,a_{Nₖ₊₁-1} so that the intervals (a n - β n, a n + β n) cover
  -- (0, 1). This is possible since ∑_{n ∈ block k} 2 β n ≥ 1 for the right
  -- choice of blocks. Distinctness is ensured by perturbing each chosen point
  -- slightly within the slack, since the interiors of (0,1) have measure-zero
  -- removed at each prior step.
  --
  -- Step 3: Show fSeq a b is nowhere differentiable. Suppose for contradiction
  -- that fSeq a b is differentiable at some x₀ ∈ (0,1) with derivative L.
  -- By the construction, for every ε > 0 we find n with β n < ε and
  -- |a n - x₀| < β n ≤ b n. Then |a n - x₀| < b n, so the difference quotient
  --   (fSeq a b (a n) - fSeq a b x₀) / (a n - x₀)
  -- has absolute value > 1 (using fSeq a b x₀ = 0, which follows from
  -- continuity at x₀ and the function vanishing on a dense set). Since we
  -- can take a n → x₀, this contradicts the existence of the limit L.
  --
  -- A clean Lean phrasing: encode `differentiable_at_imp_continuous_at` to
  -- get `f x₀ = 0`, then derive a contradiction from the bound `|a n - x₀| < b n`
  -- combined with `a n → x₀` along the produced subsequence and `L ∈ ℝ`.
  sorry

end Imc1998P12
