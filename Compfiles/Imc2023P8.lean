/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2023, Problem 8

Let `T` be a tree with `n` vertices. For every pair `{u, v}` of vertices, let
`d(u, v)` denote the distance between them. Consider

  `W(T) = ∑_{{u,v}} d(u,v)`,        `H(T) = ∑_{{u,v}} 1/d(u,v)`.

Prove that `W(T) · H(T) ≥ (n - 1)³ (n + 2) / 4`.
-/

namespace Imc2023P8

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The statement. Requires the graph to be a tree (connected and acyclic). -/
problem imc2023_p8 (G : SimpleGraph V) (hT : G.IsTree) [DecidableRel G.Adj] :
    let n : ℕ := Fintype.card V
    let W : ℚ := (∑ e ∈ (Finset.univ.filter fun p : V × V => p.1 ≠ p.2),
                    (G.dist e.1 e.2 : ℚ)) / 2
    let H : ℚ := (∑ e ∈ (Finset.univ.filter fun p : V × V => p.1 ≠ p.2),
                    (1 : ℚ) / (G.dist e.1 e.2)) / 2
    W * H ≥ ((n - 1 : ℚ) ^ 3 * (n + 2)) / 4 := by
  -- TODO: Cauchy-Schwarz on the n-1 edges (distance 1) and ≥ 2 for remaining
  -- pairs; equality at star graph.
  sorry

end Imc2023P8
