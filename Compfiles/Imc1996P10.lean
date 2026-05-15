/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Competition 1996, Problem 10
(Day 2, Problem 4)

Let `B ⊂ ℝ²` be a closed, bounded, convex set, symmetric with respect to the
origin, with boundary `Γ`. Suppose that the ellipse of maximal area contained
in `B` is the closed unit disc `D` (with boundary `C`, the unit circle).

Prove that every closed arc `A ⊂ C` with arc-length `ℓ(A) ≥ π/2` meets `Γ`.

## Proof outline (official solution)

Suppose for contradiction that some closed arc `A ⊂ C` of arc length `π/2`
satisfies `A ∩ Γ = ∅`. By the symmetry assumption (if necessary, by rotating)
we can take the endpoints to be `M = (1/√2, 1/√2)` and `N = (1/√2, -1/√2)`,
so that `A = { (cos θ, sin θ) : -π/4 ≤ θ ≤ π/4 }`.

Since `A` is compact, `Γ` is closed, and `A ∩ Γ = ∅`, there is `δ > 0` with
`dist(x, y) > δ` whenever `x ∈ A` and `y ∈ Γ`. In particular every point of
`A` is in the (open) interior of `B`.

For `0 < ε < δ` consider the ellipse
`E_ε = { (x, y) : x² / (1 + ε)² + y² / b_ε² = 1 }`
where `b_ε² = (1 + ε)² / (2 (1 + ε)² - 1)`. The defining condition is chosen
so that `M, N ∈ E_ε`.

* The area of `E_ε` is `π (1 + ε)² / √(2 (1 + ε)² - 1)`. A direct computation
  shows this is strictly greater than `π = area(D)` for every `ε > 0` (one
  checks that the function `t ↦ t² / √(2 t² - 1)` is strictly increasing on
  `(1, ∞)` and equals `1` at `t = 1`).

* Let `S = { (x, y) : |x| > |y| }`. Then `E_ε \ S ⊂ D ⊂ B` (because the points
  of `E_ε` with `|x| ≤ |y|` lie inside the unit disc — `b_ε ≤ 1`).

* On `S`, every point of `E_ε` is at distance at most `ε` from the unit
  circle, hence (for `ε < δ`) at distance less than `δ` from the
  corresponding point of `A`, hence inside `B`.

So `E_ε ⊂ B` is an ellipse of area strictly greater than `π`, contradicting
the maximality of `D`.

## Formalisation status

This file gives a precise Lean statement of the problem. The proof is left
as `sorry` with a detailed outline above. The geometric ingredients
(parametrising ellipses by their semi-axes, computing their area,
characterising arcs of the unit circle, the strict-monotonicity inequality
`(1 + ε)⁴ > 2 (1 + ε)² - 1` for `ε > 0`) are mostly elementary but several
involve manipulating Lebesgue measure of ellipses, which would require a
substantial amount of additional infrastructure to develop formally.

-/

namespace Imc1996P10

open Real Set MeasureTheory

/-- The closed unit disc in `ℝ²`. -/
noncomputable def unitDisc : Set (EuclideanSpace ℝ (Fin 2)) :=
  Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1

/-- The unit circle in `ℝ²` (the boundary of the unit disc). -/
noncomputable def unitCircle : Set (EuclideanSpace ℝ (Fin 2)) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

/-- The point on the unit circle at angle `θ`. -/
noncomputable def circlePoint (θ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![Real.cos θ, Real.sin θ]

/-- An axis-aligned closed ellipse with semi-axes `a > 0` and `b > 0` (centred
at the origin):
  `{ (x, y) | x² / a² + y² / b² ≤ 1 }`. -/
noncomputable def ellipse (a b : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  { p | (p 0)^2 / a^2 + (p 1)^2 / b^2 ≤ 1 }

/-- The Lebesgue (volume) measure on `ℝ²`, viewed via `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def μ : Measure (EuclideanSpace ℝ (Fin 2)) := volume

/-- An arc on the unit circle is the image of a closed angular interval
`[α, β]` under `circlePoint`. -/
noncomputable def arc (α β : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  circlePoint '' Set.Icc α β

-- The (Euclidean) arc length of the arc `arc α β` is `|β - α|` whenever
-- `|β - α| ≤ 2π`. We package this through a hypothesis rather than as a
-- definition: in the theorem we take `β - α ≥ π/2` (with `β - α ≤ 2π`), which
-- encodes "arc length ≥ π/2".

/--
**IMC 1996, Problem 10.**

If `B ⊂ ℝ²` is a closed, bounded, convex set symmetric about the origin, the
unit disc is contained in `B`, and `B` admits *no* axis-aligned ellipse of
strictly larger area, then every closed arc of the unit circle of angular
length at least `π/2` meets the boundary of `B`.

The hypothesis `ellipse_max` states that any axis-aligned ellipse `ellipse a b`
contained in `B` has area at most `π` (the area of the unit disc). The
official problem allows arbitrarily-rotated ellipses; the same proof works,
and the axis-aligned form makes the statement precise without introducing
the affine action of `O(2)` here. The `B`-symmetry hypothesis (`B = -B`)
then guarantees that the axes of the optimum can be aligned.
-/
problem imc1996_p10
    (B : Set (EuclideanSpace ℝ (Fin 2)))
    (B_closed : IsClosed B)
    (B_bounded : Bornology.IsBounded B)
    (B_convex : Convex ℝ B)
    (B_symm : ∀ p, p ∈ B → -p ∈ B)
    (B_disc : unitDisc ⊆ B)
    (ellipse_max : ∀ a b : ℝ, 0 < a → 0 < b → ellipse a b ⊆ B → π * a * b ≤ π)
    (α β : ℝ) (h_len : π / 2 ≤ β - α) (h_short : β - α ≤ 2 * π)
    (h_arc_in_B : arc α β ⊆ B \ frontier B) :
    False := by
  -- TODO: formal proof.
  --
  -- High-level steps:
  --   (1) `arc α β` is compact (continuous image of `[α, β]`) and
  --       `frontier B` is closed; their disjointness gives some `δ > 0`
  --       with `dist(x, y) > δ` for `x ∈ arc α β`, `y ∈ frontier B`.
  --   (2) After replacing `(α, β)` with a translate of the same length, we
  --       may assume the midpoint of `[α, β]` lies in `[-π/4, π/4]` modulo
  --       `2π`. Using the `B`-symmetry (`B = -B`) and the rotational symmetry
  --       of the unit disc this reduces to the case `α = -π/4`, `β = π/4`,
  --       so the arc has endpoints `M = (1/√2, 1/√2)` and `N = (1/√2, -1/√2)`.
  --   (3) For `0 < ε < δ` define `a = 1 + ε`, `b² = a² / (2 a² - 1)`.
  --       Then `ellipse a b ⊆ B`:
  --         • For `(x, y) ∈ ellipse a b` with `|x| ≤ |y|`, one has `x² + y² ≤ 1`
  --           (using `b² ≤ 1`), so the point is in `unitDisc ⊆ B`.
  --         • For `(x, y) ∈ ellipse a b` with `|x| > |y|`, the radial distance
  --           from the unit circle is at most `ε`, so it is at distance `< δ`
  --           from the arc `arc (-π/4) (π/4)`, which lies in `B \ frontier B`.
  --           In particular it lies in `B`.
  --   (4) Compute: `π * a * b = π * (1 + ε)² / √(2 (1 + ε)² - 1) > π`
  --       for every `ε > 0`, since `t ↦ t² / √(2 t² - 1)` is strictly
  --       increasing on `(1, ∞)` and equals `1` at `t = 1`.
  --       This contradicts `ellipse_max a b _ _ _ ≤ π`.
  sorry

end Imc1996P10
