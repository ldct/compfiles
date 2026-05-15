/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 1999, Problem 5 (Day 1)

Suppose that `2n` points are marked on an `n × n` grid (with `n ≥ 1`).
Show that there exists `k > 1` and `2k` distinct marked points
`a_1, a_2, …, a_{2k}` such that `a_{2i-1}` and `a_{2i}` lie in the same row
for each `i = 1, …, k`, and `a_{2i}` and `a_{2i+1}` (indices mod `2k`) lie
in the same column.

## Solution sketch (official solution)

Build a bipartite graph `G` whose vertices are the `n` rows together with
the `n` columns of the grid (a total of `2n` vertices), with an edge
between row `r` and column `c` whenever `(r, c)` is a marked point.
Then `G` has `2n` vertices and `2n` edges. Any forest on `V` vertices has
at most `V - 1` edges, so `G` is not a forest and contains a cycle. Such
a cycle alternates between row-vertices and column-vertices, and its
sequence of edges (= marked points) traverses points sharing a row,
then a column, then a row, etc., exactly as required.

## Status of this formalization

Statement: complete. Proof: a `sorry` placeholder — see TODO below.
-/

namespace Imc1999P5

open scoped BigOperators
open Finset

/-- **IMC 1999 Problem 5.**
Given `n ≥ 1` and a finset `S ⊆ Fin n × Fin n` with `|S| = 2n`, there
exists an integer `k ≥ 2` and a function `a : ℕ → Fin n × Fin n`
which, restricted to `{0, 1, …, 2k - 1}`, is injective, takes values in
`S`, and satisfies for each index `i ∈ {0, …, 2k - 1}`:

* if `i` is even, then `a i` and `a ((i+1) mod 2k)` share a row (equal
  first coordinate); and
* if `i` is odd, then `a i` and `a ((i+1) mod 2k)` share a column (equal
  second coordinate).

The modular `(i+1) mod 2k` makes the final pair
`(a (2k - 1), a 0)` the column-sharing pair that closes the cycle. -/
problem imc1999_p5 (n : ℕ) (hn : 1 ≤ n) (S : Finset (Fin n × Fin n))
    (hS : S.card = 2 * n) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ a : ℕ → Fin n × Fin n,
      Set.InjOn a (Finset.range (2 * k)) ∧
      (∀ i, i < 2 * k → a i ∈ S) ∧
      (∀ i, i < 2 * k → Even i → (a i).1 = (a ((i + 1) % (2 * k))).1) ∧
      (∀ i, i < 2 * k → Odd i → (a i).2 = (a ((i + 1) % (2 * k))).2) := by
  -- TODO: Full proof.
  --
  -- Construction:
  -- (1) Let `V := Fin n ⊕ Fin n` be the disjoint union of rows and
  --     columns; |V| = 2n.
  -- (2) Define a `SimpleGraph V` whose adjacency is
  --     `Adj (Sum.inl r) (Sum.inr c) := (r, c) ∈ S` (and the symmetric
  --     case `Sum.inr` / `Sum.inl`); no edges within either side.
  -- (3) The edge set is in bijection with `S`, so |E| = |S| = 2n = |V|.
  -- (4) A forest (acyclic graph) on a finite vertex set satisfies
  --     `|E| ≤ |V| - 1` (sum over connected components of
  --     `IsTree.card_edgeFinset`); since |E| = |V| ≥ 1, the graph is
  --     not acyclic, so by `SimpleGraph.IsAcyclic` negation there is a
  --     closed walk that is a cycle.
  -- (5) Take any cycle. Its support has length `2k` for some `k ≥ 2`
  --     (cycles in a bipartite graph have even length ≥ 4). Let
  --     `v_0 = inl r_0, v_1 = inr c_0, v_2 = inl r_1, v_3 = inr c_1, …`
  --     be the support (alternating because the graph is bipartite).
  -- (6) Set `a (2i)   := (r_i, c_{i-1 mod k})` and
  --         `a (2i+1) := (r_i, c_i)` for `i = 0, …, k-1`. Each `a j`
  --     corresponds to an edge of the cycle hence is in `S`. The
  --     row/column sharing pattern follows by construction. Injectivity
  --     of `a` follows from the cycle being a (vertex-)simple cycle.
  sorry

end Imc1999P5
