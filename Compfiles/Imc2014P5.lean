/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2014, Problem 5

Let `A_1 A_2 … A_{3n}` be a closed broken line consisting of `3n` line segments
in the Euclidean plane. Suppose no three vertices are collinear, and for each
`i = 1, 2, …, 3n`, the triangle `A_i A_{i+1} A_{i+2}` has counterclockwise
orientation and `∠ A_i A_{i+1} A_{i+2} = 60°` (indices mod `3n`).

Prove that the number of self-intersections of the broken line is at most
`(3/2) n² - 2 n + 1`.

## Proof outline (official solution)

Place the broken line in an equilateral triangle `T` whose sides are parallel
to the three directions of the segments. Let `x_i` denote the (signed) distance
from segment `A_i A_{i+1}` to the parallel side of `T`.

Two sub-polylines `A_i A_{i+1} A_{i+2}` and `A_j A_{j+1} A_{j+2}` with
`i ≡ j (mod 3)` intersect at most once, and only if the pair `(i, j)` satisfies
the staircase condition

  (*)  i ≡ j (mod 3) and either
       (x_i < x_{i+1} and x_j > x_{j+1}) or
       (x_i > x_{i+1} and x_j < x_{j+1}).

All self-intersections give such pairs. There are `3 * C(n, 2)` index pairs
with `i ≡ j (mod 3)`.

For every `1 ≤ k < n / 2`, at least one of the pairs `(i, i + 6k)` fails
condition (*). Indeed, assume WLOG `x_0` is the minimum. If pairs
`(-6k, 0), (-6k+1, 1), …, (0, 6k)` all satisfied (*), one would deduce
`x_{-6k+j} > x_j` for `j` even and `x_{-6k+j} < x_j` for `j` odd, ending in
`x_0 > x_{6k}`, contradicting the minimality of `x_0`.

So at least `⌊(n-1)/2⌋` pairs fail, giving at most
`3 * C(n, 2) - ⌊(n-1)/2⌋ ≤ (3/2) n² - 2 n + 1` intersections.
-/

namespace Imc2014P5

open EuclideanGeometry

/-- The Euclidean plane as `EuclideanSpace ℝ (Fin 2)`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Twice the signed area of the triangle `A B C`. Positive iff `A B C` is
counterclockwise. -/
noncomputable def signedArea (A B C : Plane) : ℝ :=
  (B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0)

/-- Three points are collinear iff their signed area vanishes. -/
def Collinear3 (A B C : Plane) : Prop := signedArea A B C = 0

/-- The closed segment from `P` to `Q` in the plane. -/
noncomputable def segment (P Q : Plane) : Set Plane :=
  {X | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ X = (1 - t) • P + t • Q}

/-- For a closed broken line of length `m`, the `i`-th segment goes from
vertex `i` to vertex `i + 1` (cyclically, with `m` understood from context). -/
noncomputable def edge {m : ℕ} [NeZero m] (A : Fin m → Plane) (i : Fin m) :
    Set Plane :=
  segment (A i) (A (i + 1))

/-- A self-intersection of the broken line is an unordered pair of *distinct*,
*non-adjacent* edge indices `(i, j)` whose corresponding segments share a
common point. -/
def IsSelfIntersection {m : ℕ} [NeZero m] (A : Fin m → Plane) (i j : Fin m) :
    Prop :=
  i ≠ j ∧ i + 1 ≠ j ∧ j + 1 ≠ i ∧
    (edge A i ∩ edge A j).Nonempty

/-- Number of self-intersections of the broken line, defined as the cardinality
of the set of unordered pairs `{i, j}` of edge indices forming a
self-intersection. -/
noncomputable def numSelfIntersections {m : ℕ} [NeZero m]
    (A : Fin m → Plane) : ℕ :=
  {p : Fin m × Fin m | p.1 < p.2 ∧ IsSelfIntersection A p.1 p.2}.ncard

/--
**IMC 2014 P5.** Let `A_1 A_2 … A_{3n}` be a closed broken line in the plane
with `3n` segments. Suppose no three vertices are collinear, and that for each
index `i`, the triangle `A_i A_{i+1} A_{i+2}` (indices mod `3n`) has
counterclockwise orientation and angle `60°` at the vertex `A_{i+1}`. Then the
number of self-intersections of the broken line is at most
`(3/2) n² - 2 n + 1`.

We index the vertices by `Fin (3 * n)` rather than by `1, …, 3n`, with cyclic
indexing built in via the `+ 1` and `+ 2` shifts on `Fin`.
-/
problem imc2014_p5 (n : ℕ) (hn : 1 ≤ n)
    (A : Fin (3 * n) → Plane)
    (h_inj : Function.Injective A)
    (h_no3 : ∀ i j k : Fin (3 * n),
      i ≠ j → j ≠ k → i ≠ k → ¬ Collinear3 (A i) (A j) (A k))
    (h_ccw : haveI : NeZero (3 * n) := ⟨by positivity⟩;
      ∀ i : Fin (3 * n), 0 < signedArea (A i) (A (i + 1)) (A (i + 2)))
    (h_angle : haveI : NeZero (3 * n) := ⟨by positivity⟩;
      ∀ i : Fin (3 * n),
        EuclideanGeometry.angle (A i) (A (i + 1)) (A (i + 2)) = Real.pi / 3) :
    haveI : NeZero (3 * n) := ⟨by positivity⟩;
    (numSelfIntersections A : ℝ) ≤ (3 / 2 : ℝ) * (n : ℝ)^2 - 2 * n + 1 := by
  -- Outline of the proof:
  -- 1. Use the 60° / counterclockwise hypotheses to show that the segments fall
  --    into exactly three direction classes (according to `i mod 3`), each
  --    parallel to one side of an enclosing equilateral triangle `T`.
  -- 2. Define `x_i` as the signed distance from segment `i` to the side of `T`
  --    parallel to it.
  -- 3. For pairs with `i ≡ j (mod 3)`, show that crossing implies the
  --    "staircase" condition (*) on `x_i, x_{i+1}, x_j, x_{j+1}`.
  -- 4. Count: there are `3 * C(n, 2)` pairs with `i ≡ j (mod 3)`. For each
  --    `1 ≤ k < n/2`, show at least one pair `(i, i + 6k)` violates (*),
  --    using the minimality argument on `x_0`.
  -- 5. Sum over `k` to get `⌊(n-1)/2⌋` excluded pairs, yielding
  --    `3 * C(n, 2) - ⌊(n-1)/2⌋ ≤ (3/2) n^2 - 2 n + 1`.
  -- TODO: complete the proof.
  sorry

end Imc2014P5
