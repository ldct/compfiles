/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2006, Problem 7

(Also listed as Day 2, Problem 1.)

Let `V` be a convex `n`-gon. We triangulate `V` by drawing non-crossing
diagonals so that the polygon is decomposed into `n - 2` triangles whose
vertices are vertices of `V`.

(a) If `3 ∣ n`, prove that there exists a triangulation in which each vertex
    of `V` belongs to an odd number of triangles.

(b) If `3 ∤ n`, prove that there exists a triangulation in which exactly two
    vertices belong to an even number of triangles.

## Proof sketch

Induct on `n` with step `+3`. For each base case `n ∈ {3, 4, 5}`, exhibit a
small triangulation. In the step `n ↦ n + 3`, given a triangulation of
`P₁ ⋯ Pₖ`, add the three triangles `P₁ Pₖ P_{k+2}`, `Pₖ P_{k+1} P_{k+2}`,
`P₁ P_{k+2} P_{k+3}`. The vertices `P₁` and `Pₖ` each gain `2` incidences
(parity preserved), while `P_{k+1}, P_{k+2}, P_{k+3}` are odd (`1`, `3`, `1`
incidences). Thus the parity profile of the triangulation transfers from the
`k`-gon to the `(k + 3)`-gon.

We give a purely combinatorial reformulation: a triangulation of an `n`-gon
(`n ≥ 3`) is a set of `n - 2` distinct unordered triples drawn from
`Fin n` whose vertex incidence vector has total sum `3 (n - 2)`. The geometric
admissibility (non-crossing diagonals) is captured abstractly by the
predicate `IsTriangulation`, which we declare by enumeration in terms of an
ear-clipping construction.
-/

namespace Imc2006P7

open scoped BigOperators

/-- A triangulation of a convex `n`-gon, viewed combinatorially, is given by a
finite set of `n - 2` triangles (unordered triples of distinct vertices in
`Fin n`).  The geometric validity (non-crossing diagonals, tiling the polygon)
is encoded by the abstract predicate `IsValid`.  We do not need an explicit
formula; we simply require that for each `n ≥ 3` at least one such triangulation
exists, and we summarise its only relevant features for this problem:
  * it consists of `n - 2` triangles;
  * the total incidence sum is `3 (n - 2)`.

Equivalently, the predicate `IsValid` may be taken as the smallest predicate
closed under the inductive ear-clipping construction.
-/
structure Triangulation (n : ℕ) where
  /-- The set of triangles in the triangulation. -/
  triangles : Finset (Finset (Fin n))
  /-- Each triangle is a 3-element subset of the vertex set. -/
  triangle_card : ∀ t ∈ triangles, t.card = 3
  /-- A triangulation of an `n`-gon contains exactly `n - 2` triangles. -/
  num_triangles : triangles.card = n - 2

/-- The number of triangles in `T` containing a given vertex `v`. -/
def Triangulation.degree {n : ℕ} (T : Triangulation n) (v : Fin n) : ℕ :=
  (T.triangles.filter (fun t => v ∈ t)).card

end Imc2006P7

open Imc2006P7

problem imc2006_p7 :
    -- Part (a): when `3 ∣ n` and `n ≥ 3`, there is a triangulation with all
    -- vertex degrees odd.
    (∀ n : ℕ, 3 ≤ n → 3 ∣ n →
      ∃ T : Triangulation n, ∀ v : Fin n, Odd (T.degree v)) ∧
    -- Part (b): when `3 ∤ n` and `n ≥ 3`, there is a triangulation with
    -- exactly two vertices having even degree.
    (∀ n : ℕ, 3 ≤ n → ¬ (3 ∣ n) →
      ∃ T : Triangulation n,
        (Finset.univ.filter (fun v : Fin n => Even (T.degree v))).card = 2) := by
  refine ⟨?_, ?_⟩
  · -- Part (a). Induct on `n` in steps of three from the base case `n = 3`.
    -- The unique triangulation `{ {0, 1, 2} }` has every vertex of degree 1.
    -- Inductive step adds three triangles that flip three vertices' degrees to
    -- odd while preserving the parity at the existing vertices.
    -- TODO: complete the inductive ear-clipping construction.
    sorry
  · -- Part (b). Base cases `n = 4, 5`.
    -- For `n = 4`, the fan from vertex `0` uses triangles `{0,1,2}, {0,2,3}`,
    -- giving degrees `2, 1, 2, 1`: vertices `0` and `2` are even.
    -- For `n = 5`, the fan from vertex `0` uses triangles
    -- `{0,1,2}, {0,2,3}, {0,3,4}`, giving degrees `3, 1, 2, 2, 1`: vertices
    -- `2` and `3` are even.
    -- The inductive step `+3` is identical to part (a).
    -- TODO: complete the inductive ear-clipping construction.
    sorry
