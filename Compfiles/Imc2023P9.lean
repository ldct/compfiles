/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Convex.Basic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2023, Problem 9

We say a real number `V` is *good* if there exist two closed convex
subsets `X, Y` of the unit cube in `ℝ³`, each of volume `V`, such that
for each of the three coordinate planes the projections of `X` and `Y`
onto that plane are disjoint.

Find `sup { V | V is good }`.

Answer: `1/4`.
-/

namespace Imc2023P9

open MeasureTheory

/-- The unit cube `[0, 1]³` in `ℝ³`. -/
def unitCube : Set (Fin 3 → ℝ) :=
  {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}

/-- Projection onto the plane `x_i = 0` (drop coordinate `i`). -/
def proj (i : Fin 3) (x : Fin 3 → ℝ) : Fin 2 → ℝ :=
  fun j => x (if j.val < i.val then ⟨j.val, by omega⟩ else ⟨j.val + 1, by omega⟩)

/-- `V` is good if there exist closed convex `X, Y ⊆ unitCube` each of
volume `V`, with disjoint projections onto each coordinate plane. -/
def IsGood (V : ℝ) : Prop :=
  ∃ X Y : Set (Fin 3 → ℝ),
    IsClosed X ∧ IsClosed Y ∧ Convex ℝ X ∧ Convex ℝ Y ∧
    X ⊆ unitCube ∧ Y ⊆ unitCube ∧
    (volume X).toReal = V ∧ (volume Y).toReal = V ∧
    ∀ i : Fin 3, Disjoint (proj i '' X) (proj i '' Y)

noncomputable determine answer : ℝ := 1 / 4

problem imc2023_p9 : sSup {V : ℝ | IsGood V} = answer := by
  -- TODO: Following the official solution.
  -- Lower bound: X = [0,1/2] × [0,1/2-ε] × [0,1], Y = [1/2+ε,1] × [1/2,1] × [0,1]
  -- work after an affine shift; volumes → 1/4.
  -- Upper bound: for P with nonzero signed coordinates, the 8 sign-reflections
  -- intersect X ∪ Y in at most 4 points; integrate.
  sorry

end Imc2023P9
