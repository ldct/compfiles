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
  -- TODO: Following the official solution (IMC 2023, Day 2, Problem 9).
  --
  -- LOWER BOUND (sSup ≥ 1/4):
  --   For each ε ∈ (0, 1/2), take (after shifting from [-1/2,1/2]^3 to [0,1]^3):
  --     X = [0, 1/2] × [0, 1/2 - ε] × [0, 1]
  --     Y = [1/2 + ε, 1] × [1/2, 1] × [0, 1]
  --   Both are closed, convex, in the unit cube. The projections:
  --     onto x_3=0 plane: X_proj = [0,1/2] × [0,1/2-ε], Y_proj = [1/2+ε,1] × [1/2,1]  -- disjoint
  --     onto x_2=0 plane: X_proj = [0,1/2] × [0,1],     Y_proj = [1/2+ε,1] × [0,1]    -- disjoint (x-coords)
  --     onto x_1=0 plane: X_proj = [0,1/2-ε] × [0,1],   Y_proj = [1/2,1] × [0,1]      -- disjoint (y-coords)
  --   Volume of each = (1/2)(1/2 - ε)(1) = 1/4 - ε/2 → 1/4 as ε → 0.
  --   So 1/4 - ε/2 ∈ {V | IsGood V} for all small ε > 0, giving sSup ≥ 1/4.
  --
  -- UPPER BOUND (sSup ≤ 1/4):
  --   Use cube U = [-1/2, 1/2]^3 (translate by (1/2,1/2,1/2)).
  --   For P = (x,y,z) ∈ U with xyz ≠ 0, let \bar{P} = {(±x, ±y, ±z)} (8 sign-reflections).
  --   Key claim: |\bar{P} ∩ (X ∪ Y)| ≤ 4 for all such P.
  --   Then integrating the indicator of X ∪ Y over U via the symmetry group action gives
  --     8 · vol(X ∪ Y) = ∫_U ∑_{σ ∈ {±1}^3} 𝟙[σP ∈ X ∪ Y] dP ≤ 4 · vol(U) = 4,
  --   so vol(X) + vol(Y) = vol(X ∪ Y) ≤ 1/2 (X, Y disjoint by disjoint projections),
  --   hence V ≤ 1/4.
  --
  --   Proof of key claim (Claims 1 & 2 in solution):
  --     Claim 1: If |\bar{P} ∩ (X ∪ Y)| ≥ 5, pigeonhole forces an antipodal pair in
  --       one body, and case analysis (each pair of points whose projection coincides
  --       must lie in the same body) makes one body, say X, contain 4 mutually-symmetric
  --       points, so X is "thick" (all 3 projections contain origin in their closures).
  --     Claim 2: If X is thick, replace X by -Y (same volume, projections of -Y are
  --       reflections of Y's, still disjoint from Y's since Y's miss origin). The
  --       symmetry then shows |\bar{P} ∩ Y'| ≥ 3 leads to projection conflict.
  sorry

end Imc2023P9
