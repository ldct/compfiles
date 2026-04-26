/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra, .Combinatorics] }

/-!
# International Mathematical Competition 1998, Problem 9 (Day 2, Problem 3)

Let `0 < c < 1` and let `f : [0,1] → [0,1]` be the tent map

  `f(x) = x/c` for `x ∈ [0, c]`,
  `f(x) = (1-x)/(1-c)` for `x ∈ [c, 1]`.

Show that the set of `n`-periodic points of `f` (i.e. `{x : f^n x = x}`) is
finite and non-empty.

In fact the official solution proves a stronger statement: the set
`{x ∈ [0,1] : f^n x = x}` has cardinality exactly `2^n`, and the set of points
of *exact* period `n` (i.e. `f^n x = x` but `f^k x ≠ x` for `0 < k < n`) is
non-empty.

## Solution sketch

`f^n` is piecewise linear with `2^n` monotone pieces, each going from height
`0` to `1` or from height `1` to `0` over a sub-interval of `[0,1]` of positive
length. The graph of `y = x` therefore intersects each piece in exactly one
point, giving exactly `2^n` solutions to `f^n x = x`. In particular the set of
`n`-periodic points is finite.

The points of period exactly `n` are obtained from the `2^n` solutions of
`f^n x = x` by removing those `x` for which already `f^k x = x` for some
`1 ≤ k < n`. Such excluded `x` are themselves fixed points of `f^k` for some
proper divisor (or any earlier value) `k`, and the total count is bounded by
`∑_{k=1}^{n-1} 2^k = 2^n - 2 < 2^n`, so at least two points of exact period
`n` remain.
-/

namespace Imc1998P9

open Set

/-- The tent map with parameter `c ∈ (0,1)`. -/
noncomputable def tent (c x : ℝ) : ℝ :=
  if x ≤ c then x / c else (1 - x) / (1 - c)

/-- The `n`-fold iterate of the tent map. -/
noncomputable def tentIter (c : ℝ) : ℕ → ℝ → ℝ
  | 0     => id
  | n + 1 => tent c ∘ tentIter c n

/-- `tent c` maps `[0,1]` into `[0,1]`. -/
lemma tent_mem_Icc {c : ℝ} (hc : 0 < c) (hc' : c < 1) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    tent c x ∈ Icc (0:ℝ) 1 := by
  obtain ⟨hx0, hx1⟩ := hx
  unfold tent
  split_ifs with h
  · refine ⟨div_nonneg hx0 hc.le, ?_⟩
    rw [div_le_one hc]; exact h
  · have hgt : c < x := lt_of_not_ge h
    have h1c : 0 < 1 - c := by linarith
    refine ⟨div_nonneg (by linarith) h1c.le, ?_⟩
    rw [div_le_one h1c]; linarith

/-- Iterates of the tent map preserve `[0,1]`. -/
lemma tentIter_mem_Icc {c : ℝ} (hc : 0 < c) (hc' : c < 1) (n : ℕ) {x : ℝ}
    (hx : x ∈ Icc (0:ℝ) 1) : tentIter c n x ∈ Icc (0:ℝ) 1 := by
  induction n with
  | zero => exact hx
  | succ n ih => exact tent_mem_Icc hc hc' ih

/-- The set of fixed points of the `n`-th iterate, viewed as a subset of `[0,1]`. -/
noncomputable def fixedSet (c : ℝ) (n : ℕ) : Set ℝ :=
  {x ∈ Icc (0:ℝ) 1 | tentIter c n x = x}

/-- The set of points of exact period `n` (with `n ≥ 1`). -/
noncomputable def exactPeriodSet (c : ℝ) (n : ℕ) : Set ℝ :=
  {x ∈ fixedSet c n | ∀ k, 0 < k → k < n → tentIter c k x ≠ x}

/-- Part 1 (finiteness): for `n ≥ 1`, the set of fixed points of `tentIter c n`
in `[0,1]` is finite (in fact has cardinality `2^n`).

TODO: Full proof requires a careful piecewise-linear analysis of `tentIter c n`.
Specifically, `tentIter c n` is continuous and piecewise linear on `[0,1]`,
with `2^n` linear pieces, each having absolute slope `≥ 1` (hence non-constant)
and mapping its sub-interval onto either `[0,1]` (slope ≥ 0) or `[1,0]` (slope
≤ 0). The graph of `y = x` then intersects each piece in exactly one point, so
the fixed-point set has exactly `2^n` elements.

A formal Lean proof would inductively construct the partition of `[0,1]` into
`2^n` sub-intervals on which `tentIter c n` is affine, and then on each piece
solve the linear equation `f^n x = x` to extract a unique solution. -/
problem imc1998_p9_finite (c : ℝ) (_hc : 0 < c) (_hc' : c < 1) (n : ℕ) (_hn : 1 ≤ n) :
    (fixedSet c n).Finite := by
  sorry

/-- Part 2 (non-emptiness of exact period `n`): for `n ≥ 1`, the set of points
of exact period `n` is non-empty.

TODO: Once the cardinality `#(fixedSet c n) = 2^n` is established, the points of
exact period `n` are obtained by removing `⋃_{k=1}^{n-1} fixedSet c k` from
`fixedSet c n`. The cardinality of this union is at most
`∑_{k=1}^{n-1} 2^k = 2^n - 2 < 2^n`, so at least two points of exact period `n`
remain. The case `n = 1` is special: any fixed point of `f` itself has exact
period `1` (interpreting the "for all `0 < k < 1`" condition vacuously), and
the tent map has the obvious fixed point `x = 0` (and another at
`x = 1/(2 - c)`). -/
problem imc1998_p9_exact_nonempty
    (c : ℝ) (_hc : 0 < c) (_hc' : c < 1) (n : ℕ) (_hn : 1 ≤ n) :
    (exactPeriodSet c n).Nonempty := by
  sorry

end Imc1998P9
