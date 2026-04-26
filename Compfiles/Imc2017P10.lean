/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Competition 2017, Problem 10

Let `K` be an equilateral triangle in the plane. Prove that for every `p > 0`
there exists an `ε > 0` with the following property: if `n` is a positive
integer and `T₁, …, Tₙ` are non-overlapping triangles inside `K`, each
homothetic to `K` with a negative ratio, and
`∑ area(Tₗ) > area(K) - ε`, then `∑ perimeter(Tₗ) > p`.

## Outline of proof (from the official solution)

By an affine transformation, we may take `K` with vertices `(0,0), (0,1),
(1,0)`, projecting onto `[0,1]` on the `x`-axis. Replace perimeter by total
projection length on the `x`-axis (these are proportional).

For each triangle `Tᵢ`, let `fᵢ(a)` be the length of the slice
`{x = a} ∩ Tᵢ`. Since `Tᵢ` is homothetic to `K` with negative ratio, `fᵢ` is
increasing on its support, with a downward gap at its right endpoint (the
"projection" of the side of `Tᵢ`). Set `f = ∑ fᵢ`. Where smooth,
`fᵢ'(a) = fᵢ(a)/a`. So `f` is increasing piecewise with downward gaps
`d₁, …, d_N`; each `dⱼ` sums some side-lengths, and every `Tᵢ` contributes
to exactly one `dⱼ`. Also `f(a) ≤ 1 - a` and `∫₀¹ f(a) da ≥ 1/2 - ε`.

Pick `m = ⌊1/(8ε)⌋`. For each `0 ≤ k ≤ (m-1)/2`, the area in the strip
`k/m ≤ x ≤ (k+1)/m` is at least `1/(2m) - ε ≥ 1/(4m)`. Hence
`∫_{k/m}^{(k+1)/m} f'(x) dx ≥ ∫_{k/m}^{(k+1)/m} f(x)/x dx`
                          `≥ (m/(k+1)) · 1/(4m) = 1/(4(k+1))`.
Summing,
`∫₀^{1/2} f'(x) dx ≥ (1/4) ∑_{k=0}^{⌊(m-1)/2⌋} 1/(k+1) → ∞ as ε → 0`.
The left side equals `f(1/2) + ∑_{xⱼ < 1/2} dⱼ`, so the perimeter sum
diverges as `ε → 0`.
-/

namespace Imc2017P10

open scoped Real

open MeasureTheory Set

/-- The plane. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- A triangle, recorded by its three vertices. -/
structure Triangle where
  v0 : Plane
  v1 : Plane
  v2 : Plane

namespace Triangle

/-- The closed triangle (convex hull of the three vertices). -/
noncomputable def carrier (T : Triangle) : Set Plane :=
  convexHull ℝ {T.v0, T.v1, T.v2}

/-- A triangle is *equilateral* if its three sides have equal positive length. -/
def IsEquilateral (T : Triangle) : Prop :=
  ‖T.v0 - T.v1‖ = ‖T.v1 - T.v2‖ ∧
  ‖T.v1 - T.v2‖ = ‖T.v2 - T.v0‖ ∧
  0 < ‖T.v0 - T.v1‖

/-- The (common) side length of an equilateral triangle. -/
noncomputable def sideLength (T : Triangle) : ℝ := ‖T.v0 - T.v1‖

/-- The perimeter of a triangle (sum of its three side lengths). -/
noncomputable def perimeter (T : Triangle) : ℝ :=
  ‖T.v0 - T.v1‖ + ‖T.v1 - T.v2‖ + ‖T.v2 - T.v0‖

/-- The area of a triangle (the 2-dimensional Lebesgue measure of its
closed convex hull). -/
noncomputable def area (T : Triangle) : ℝ := (volume T.carrier).toReal

/-- `T'` is homothetic to `T` with ratio `r` (and some center `c`) if its
vertices are the images of those of `T` under the homothety
`x ↦ c + r • (x - c)`. -/
def IsHomotheticWithRatio (T T' : Triangle) (r : ℝ) : Prop :=
  ∃ c : Plane,
    T'.v0 = c + r • (T.v0 - c) ∧
    T'.v1 = c + r • (T.v1 - c) ∧
    T'.v2 = c + r • (T.v2 - c)

end Triangle

open Triangle

/-- IMC 2017 Problem 10. Let `K` be an equilateral triangle in the plane.
For every `p > 0` there exists `ε > 0` such that whenever `T₁, …, Tₙ` are
non-overlapping triangles inside `K`, each homothetic to `K` with a negative
ratio, and the sum of their areas exceeds `area K - ε`, then the sum of
their perimeters exceeds `p`. -/
problem imc2017_p10
    (K : Triangle) (hK : K.IsEquilateral) :
    ∀ p : ℝ, 0 < p → ∃ ε : ℝ, 0 < ε ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (T : Fin n → Triangle) (r : Fin n → ℝ),
        (∀ i, r i < 0) →
        (∀ i, IsHomotheticWithRatio K (T i) (r i)) →
        (∀ i, (T i).carrier ⊆ K.carrier) →
        (∀ i j, i ≠ j → volume ((T i).carrier ∩ (T j).carrier) = 0) →
        K.area - ε < ∑ i, (T i).area →
        p < ∑ i, (T i).perimeter := by
  -- TODO: The full proof follows the official outline above. Key steps:
  -- 1. Reduce to a fixed convenient `K` (e.g. vertices `(0,0), (1,0), (0,1)`)
  --    via an affine change of coordinates; perimeter / area / homothety
  --    behave equivariantly.
  -- 2. Define the slice lengths `fᵢ(a) = length({x = a} ∩ Tᵢ)` and their
  --    sum `f`. Establish: each `fᵢ` is piecewise affine increasing on its
  --    support with `fᵢ'(a) = fᵢ(a)/a` (when smooth) and a downward jump at
  --    its right endpoint of size `(side length of Tᵢ)`; further
  --    `∑ⱼ dⱼ = ∑ᵢ |rᵢ| · sideLength K` (proportional to total perimeter).
  -- 3. From `∑ area(Tᵢ) > area(K) - ε` deduce `∫₀¹ f ≥ 1/2 · area(K)·c - ε`
  --    (for an appropriate constant). Bound `f(a) ≤ (1-a) · sideLength K`.
  -- 4. Pick `m = ⌊1/(8ε)⌋` and split `[0,1/2]` into strips of width `1/m`.
  --    Use `∫_{k/m}^{(k+1)/m} f'(x) dx ≥ ∫_{k/m}^{(k+1)/m} f(x)/x dx
  --      ≥ (m/(k+1)) · (1/(4m)) = 1/(4(k+1))`.
  -- 5. Sum over `k = 0, …, ⌊(m-1)/2⌋` to get a logarithmic lower bound on
  --    `∫₀^{1/2} f'(x) dx = f(1/2) + ∑_{xⱼ < 1/2} dⱼ`, which therefore
  --    diverges as `ε → 0`. Pick `ε` so the resulting bound exceeds `p`.
  sorry

end Imc2017P10
