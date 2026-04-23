/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2021, Problem 2

Let `n` and `k` be fixed positive integers, and let `a` be an arbitrary
non-negative integer. Choose a random `k`-element subset `X` of
`{1, 2, …, k + a}` uniformly, and independently a random `n`-element
subset `Y` of `{1, …, k + n + a}` uniformly. Prove that
`P(min(Y) > max(X))` does not depend on `a`.

We express the "probability" concretely as a ratio of finite cardinalities.
The claim is that

  (# favorable pairs) / (|X-space| · |Y-space|) = 1 / C(n+k, k),

independent of `a`.
-/

namespace Imc2021P2

open Finset

/-- The set of pairs `(X, Y)` where `X` is a `k`-subset of `Icc 1 (k+a)` and
`Y` is an `n`-subset of `Icc 1 (k+n+a)`. -/
noncomputable def allPairs (n k a : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  ((Icc 1 (k + a)).powersetCard k) ×ˢ ((Icc 1 (k + n + a)).powersetCard n)

/-- The subset of `allPairs` for which `max X < min Y`. -/
noncomputable def goodPairs (n k a : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  (allPairs n k a).filter (fun p => p.1.max < p.2.min)

/-- The problem: the ratio

  `|goodPairs| / |allPairs| = 1 / C(n+k, k)`,

independent of `a`. We state this in cleared form:

  `|goodPairs| * C(n+k, k) = |allPairs|`.

The solution proceeds as follows. Total outcomes:
`|X-space| = C(k+a, k)`, `|Y-space| = C(n+k+a, n)`. Favorable outcomes:
for each `S ⊆ {1,…, n+k+a}` with `|S| = n+k`, taking `X` to be the
`k` smallest elements of `S` and `Y` to be the `n` largest gives a
bijection with `goodPairs` (restricted to the case where `max X < min Y`).
So `|goodPairs| = C(n+k+a, n+k)`. The identity
`C(n+k+a, n+k) · C(n+k, k) = C(k+a, k) · C(n+k+a, n)` gives the result.

TODO: the proof requires a careful bijection. We leave it as a `sorry`.
-/
problem imc2021_p2 (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (a : ℕ) :
    ((goodPairs n k a).card : ℚ) * (Nat.choose (n + k) k) =
    ((allPairs n k a).card : ℚ) := by
  sorry

end Imc2021P2
