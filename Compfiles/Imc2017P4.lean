/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2017, Problem 4

There are `n` people in a city, and each of them has exactly `1000`
friends (friendship is symmetric). Prove that it is possible to select
a group `S` of people such that at least `n / 2017` persons in `S` have
exactly two friends in `S`.

## Proof sketch (official solution)

Let `d = 1000`. Select each vertex independently into `S` with
probability `p ∈ (0, 1)`. The probability that a fixed vertex `v` is in
`S` and has exactly two of its `d` friends in `S` is
  `q = C(d,2) · p³ · (1 - p)^{d-2}`.
Choosing `p = 3 / (d + 1)` and using `(1 + 3/(d-2))^{-(d-2)} > e^{-3}`
yields `q > 1 / 2017`. Hence the expected number of vertices in `S`
having exactly two `S`-friends exceeds `n / 2017`, and so some
deterministic choice of `S` realises the bound.
-/

namespace Imc2017P4

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of friends of `v` lying in `S`. -/
noncomputable def friendsIn (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) : ℕ :=
  (S.filter fun u => G.Adj v u).card

/-- Statement of IMC 2017 Problem 4.

For any finite friendship graph `G` on `V` in which every vertex has
exactly `1000` friends, there is a subset `S ⊆ V` for which the number
of vertices of `S` having exactly two friends in `S` is at least
`(card V) / 2017`. -/
problem imc2017_p4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v : V, (Finset.univ.filter fun u => G.Adj v u).card = 1000) :
    ∃ S : Finset V,
      (Fintype.card V : ℚ) / 2017 ≤
        ((S.filter fun v => friendsIn G S v = 2).card : ℚ) := by
  -- TODO: formalize the probabilistic argument from the official solution.
  -- Sketch: select `S` by independent Bernoulli(p) trials with
  -- `p = 3 / 1001`. The expectation of
  --   `f(S) = #{v ∈ S : friendsIn G S v = 2}`
  -- equals `n · C(1000, 2) · p³ · (1 - p)^{998}`,
  -- which exceeds `n / 2017`. Therefore some realisation `S` attains
  -- a value of `f` at least as large as this expectation, and that `S`
  -- witnesses the desired bound.
  sorry

end Imc2017P4
