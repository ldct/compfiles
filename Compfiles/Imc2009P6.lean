/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2009, Problem 6
(Day 2, Problem 1)

Let `ℓ` be a line and `P` a point in `ℝ^3`. Let `S` be the set of `X` such that
`dist(X, ℓ) ≥ 2 * dist(X, P)`. If `dist(P, ℓ) = d > 0`, find `vol(S)`.

Answer: `vol(S) = 16π d^3 / (27 √3)`.

We formalize the problem in a convenient coordinate system: `ℓ` is the `z`-axis
and `P = (d, 0, 0)`, so that `dist(P, ℓ) = d`. This is without loss of
generality since the Euclidean volume is invariant under isometries of `ℝ^3`.
In the chosen coordinates, `dist(X, ℓ)^2 = X_0^2 + X_1^2` and
`dist(X, P)^2 = (X_0 - d)^2 + X_1^2 + X_2^2`, so the condition
`dist(X, ℓ) ≥ 2 dist(X, P)` is equivalent (for nonnegative quantities) to
`X_0^2 + X_1^2 ≥ 4 ((X_0 - d)^2 + X_1^2 + X_2^2)`.
-/

namespace Imc2009P6

open MeasureTheory

/-- The set `S` for a given `d > 0`, in the coordinate system where the line
is the `z`-axis and `P = (d, 0, 0)`. A point `X = (x, y, z)` is in `S` when the
distance to the `z`-axis, `√(x² + y²)`, is at least twice the distance to
`P`, `√((x-d)² + y² + z²)`. We phrase this using the squared inequality. -/
def S (d : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {X | X 0 ^ 2 + X 1 ^ 2 ≥ 4 * ((X 0 - d) ^ 2 + X 1 ^ 2 + X 2 ^ 2)}

/-- The answer: `vol(S) = 16π d^3 / (27 √3)`. -/
noncomputable determine answer (d : ℝ) : ℝ := 16 * Real.pi * d ^ 3 / (27 * Real.sqrt 3)

snip begin

/-- Algebraic rewrite: `x² + y² ≥ 4((x-d)² + y² + z²)` iff
`3(x - 4d/3)² + 3y² + 4z² ≤ 4d²/3`.

This exhibits `S d` as an ellipsoid centered at `(4d/3, 0, 0)` with principal
semi-axes `(2d/3, 2d/3, d/√3)`. -/
lemma S_eq_ellipsoid (d : ℝ) :
    S d = {X : EuclideanSpace ℝ (Fin 3) |
      3 * (X 0 - 4 * d / 3) ^ 2 + 3 * X 1 ^ 2 + 4 * X 2 ^ 2 ≤ 4 * d ^ 2 / 3} := by
  ext X
  simp only [S, Set.mem_setOf_eq, ge_iff_le]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- For all `d`, the set `S d` is nonempty: it contains `(4d/3, 0, 0)`. -/
lemma S_nonempty (d : ℝ) : (S d).Nonempty := by
  refine ⟨(!₂[4 * d / 3, 0, 0] : EuclideanSpace ℝ (Fin 3)), ?_⟩
  simp only [S, Set.mem_setOf_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, show (Fin.succ 0 : Fin 2) = 1 from rfl]
  nlinarith

snip end

/-- The IMC 2009 Problem 6 (Day 2, Problem 1): the volume of `S d` is
`16π d^3 / (27 √3)`. Formally, we interpret `S d` as a subset of Euclidean
3-space with the Lebesgue measure and equate
`volume (S d) = ENNReal.ofReal (answer d)`.

Solution outline:
`S d` is (by `S_eq_ellipsoid`) the closed ellipsoid
`E = {X | 3(X_0 - 4d/3)² + 3X_1² + 4X_2² ≤ 4d²/3}`.
Translating by `-(4d/3, 0, 0)` (volume-preserving) and then applying the
linear change of coordinates `X ↦ (X_0 · 3/(2d), X_1 · 3/(2d), X_2 · √3/d)`
(Jacobian determinant `9 · √3 / (4 d³)`) reduces `E` to the closed unit ball.
Since `vol(closedBall (0:ℝ^3) 1) = 4π/3` (from
`EuclideanSpace.volume_closedBall_fin_three`), we get
`vol(S d) = (4d³ · √3 / 27) · (4π/3) · (1 / √3) · √3 = 16π d³ / (27 √3)`.

The full formalization proceeds through `MeasureTheory.Measure.addHaar_preimage_linearMap`
and `MeasureTheory.measure_preimage_add`. -/
problem imc2009_p6 (d : ℝ) (hd : 0 < d) :
    volume (S d) = ENNReal.ofReal (answer d) := by
  -- TODO: reduce to closed unit ball via `addHaar_preimage_linearMap` and
  -- translation invariance, then use `EuclideanSpace.volume_closedBall_fin_three`.
  sorry

end Imc2009P6
