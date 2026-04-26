/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2009, Problem 3

In a town, every two non-friends have a common friend, and no one is friends
with everyone. Let `a_i` be the number of friends of resident `i`. Suppose
`∑ a_i^2 = n^2 - n`. Determine the length `k` of the shortest cycle in the
friendship graph (with `k ≥ 3`).

Answer: `k = 5`.

The argument: the number of walks of length 2 equals `∑ a_i^2 = n^2 - n`. There
is an injection from ordered pairs of distinct vertices into walks of length 2
(adjacent pairs map to closed walks `(u,v,u)`; non-adjacent pairs use the
required common neighbor). Since both sets have size `n^2 - n`, this is a
bijection, which rules out triangles `C_3` and `C_4`. The graph is not a forest
(no vertex of degree `n - 1`), so it has cycles, and the shortest has length at
least `5`. Conversely, any cycle of length `≥ 6` can be shortened using the
common-friend property, so the girth is exactly `5`. The pentagon `C_5` realizes
this.
-/

namespace Imc2009P3

open SimpleGraph

determine answer : ℕ := 5

problem imc2009_p3 (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (hCommon : ∀ u v : V, u ≠ v → ¬ G.Adj u v →
      ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (hNotAll : ∀ v : V, ∃ u : V, u ≠ v ∧ ¬ G.Adj v u)
    (hSum : ∑ v : V, (G.degree v) ^ 2 = Fintype.card V ^ 2 - Fintype.card V)
    (hCycle : ¬ G.IsAcyclic) :
    G.girth = answer := by
  -- TODO: full combinatorial proof.
  -- Key steps:
  --   (1) Number of walks of length 2 is `∑ a_i^2`.
  --   (2) Build an injection from ordered distinct pairs into such walks
  --       using `hCommon` (and the diagonal embedding for adjacent pairs).
  --   (3) `n^2 - n` ordered distinct pairs vs `n^2 - n` walks ⇒ bijection ⇒
  --       no `C_3` and no `C_4`.
  --   (4) `hCycle` and the previous step ⇒ girth ≥ 5.
  --   (5) Any cycle of length `≥ 6` can be shortened via `hCommon` ⇒ girth = 5.
  sorry

end Imc2009P3
