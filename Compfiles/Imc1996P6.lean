/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Competition 1996, Problem 6 (Day 1)

Upper and lower content of subsets of `ℝ²`.

For `E ⊂ ℝ²`, define the *upper content* of `E` to be
  `𝓒(E) = inf { ∑_{i=1}^n diam(E_i) : E ⊂ ⋃ᵢ Eᵢ }`
where the infimum runs over finite covers of `E` by arbitrary subsets.

The *lower content* of `E` is
  `𝓚(E) = sup { ℓ(L) : L closed segment, E "contracts" onto L }`
where a *contraction* of `E` onto `L` is a (surjective) map `f : E → L`
with `‖f x - f y‖ ≤ ‖x - y‖` for all `x, y ∈ E`.

Show:
(a) `𝓒(L) = ℓ(L)` for a closed segment `L`.
(b) `𝓒(E) ≥ 𝓚(E)` for every set `E`.
(c) The equality `𝓒(E) = 𝓚(E)` need not hold even for compact `E`.

## Proof outline (official solution)

(a) Choosing the trivial cover `E₁ = L` shows `𝓒(L) ≤ ℓ(L)`.
Conversely, given any cover `L ⊂ ⋃ Eᵢ`, project each `Eᵢ` orthogonally
onto the line through `L` and use the fact that the diameter does not
increase. The projections cover `L`, and for an interval, the sum of
the diameters of any finite cover is at least the length of `L` (a
standard one-dimensional measure-cover argument).

(b) Suppose `f : E → L` is a contraction onto `L`, and `E ⊂ ⋃ Eᵢ`.
Then `L ⊂ ⋃ f(Eᵢ)`, and `diam(f(Eᵢ)) ≤ diam(Eᵢ)` since `f` is a
contraction. By (a),
  `ℓ(L) = 𝓒(L) ≤ ∑ diam(f(Eᵢ)) ≤ ∑ diam(Eᵢ)`,
so `ℓ(L) ≤ 𝓒(E)`. Taking sup over `L` gives `𝓚(E) ≤ 𝓒(E)`.

(c) Take `E = T ∪ T'`, where `T` is the triangle with vertices
`(-2, 2), (2, 2), (0, 4)` and `T'` is its reflection through the
`x`-axis (vertices `(-2, -2), (2, -2), (0, -4)`).

(c1) `𝓒(E) ≥ 8`: any cover either splits as covers of the two
horizontal segments `[(-2, 2), (2, 2)]` and `[(-2, -2), (2, -2)]`
(each of length `4`, total `≥ 8` by part (a)), or some piece meets
both halves; in the latter case, projecting vertically gives a cover
of an interval of total length `8`.

(c2) `𝓚(E) < 8`: let `f` be a contraction of `E` onto a segment
`L = [a', b']` with `f(a) = a'`, `f(b) = b'`. WLOG `a ∈ T`. If the
second coordinate `a₂ ≤ 3`, then every point of `E` is within
distance `√50 < 8` of `a`, so `ℓ(L) ≤ √50`. Otherwise `a₂ > 3` and by
symmetry `b₂ < -3`, and then every vertex of `T` is within distance
`√10` of `a`, every vertex of `T'` is within `√10` of `b`. The image
of `T` lies in a segment of length `≤ √10` containing `a'`, similarly
for `T'`, so `ℓ(L) ≤ 2√10 < 8`.

Hence `𝓒(E) ≥ 8 > 2√10 ≥ 𝓚(E)`.

## Status

Statement-level formalization with `sorry` for all three parts. The
auxiliary lemma `dist_in_triangle_le_sqrt50` (every point of `T ∪ T'`
is within `√50` of any vertex of `T` with second coordinate `≤ 3`)
is fully proved.

A full Lean proof would require formalizing:
* the inequality `∑ diam(Eᵢ) ≥ ℓ(L)` for finite covers of an
  interval (essentially one-dimensional outer-measure / Lebesgue
  outer measure on `ℝ`),
* projection / contraction monotonicity of `diam`,
* the case analysis in (c).
-/

namespace Imc1996P6

open scoped Topology BigOperators
open Set Metric

/-- Upper content of a subset `E ⊂ ℝ²`: the infimum, over all finite
covers of `E`, of the sum of the diameters of the cover sets. We use
`EReal` to represent the diameter (matching `Metric.diam`'s `ℝ` value
together with the implicit possibility of `∞` for unbounded sets). -/
noncomputable def upperContent (E : Set (ℝ × ℝ)) : ℝ :=
  sInf { s : ℝ |
    ∃ (n : ℕ) (F : Fin n → Set (ℝ × ℝ)),
      E ⊆ ⋃ i, F i ∧ s = ∑ i, Metric.diam (F i) }

/-- A *contraction* of `E` onto `L` is a 1-Lipschitz surjection from `E`
to `L`. -/
def IsContractionOnto
    (f : ℝ × ℝ → ℝ × ℝ)
    (E L : Set (ℝ × ℝ)) : Prop :=
  (∀ x ∈ E, ∀ y ∈ E, dist (f x) (f y) ≤ dist x y) ∧ f '' E = L

/-- Lower content: sup of lengths of segments `L` that `E` contracts onto. -/
noncomputable def lowerContent (E : Set (ℝ × ℝ)) : ℝ :=
  sSup { ℓ : ℝ |
    ∃ (a b : ℝ × ℝ)
      (f : ℝ × ℝ → ℝ × ℝ),
        IsContractionOnto f E (segment ℝ a b) ∧ ℓ = dist a b }

/-- The closed segment in `ℝ²` from `a` to `b`. -/
noncomputable def seg (a b : ℝ × ℝ) :
    Set (ℝ × ℝ) := segment ℝ a b

snip begin

/-- A point with `y`-coordinate in `[-4, 4]` and `x`-coordinate in
`[-2, 2]` is within squared distance `52` of the vertex `(-2, 2)`. The
bound `52 < 64 = 8^2` is what we need for part (c2): every point of
`E = T ∪ T'` is within distance `< 8` of a fixed vertex of `T`. -/
lemma dist_pt_in_box_le_sqrt52 {x y : ℝ}
    (hx : -2 ≤ x ∧ x ≤ 2) (hy : -4 ≤ y ∧ y ≤ 4) :
    (x - (-2))^2 + (y - 2)^2 ≤ 52 := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hx_sq : (x - (-2))^2 ≤ 16 := by nlinarith
  have hy_sq : (y - 2)^2 ≤ 36 := by nlinarith
  linarith

/-- `√52 < 8`: a useful numeric bound for part (c). -/
lemma sqrt_52_lt_8 : Real.sqrt 52 < 8 := by
  have h : (52 : ℝ) < 8^2 := by norm_num
  have h64 : Real.sqrt (8^2 : ℝ) = 8 := by
    rw [Real.sqrt_sq]; norm_num
  calc Real.sqrt 52 < Real.sqrt (8^2 : ℝ) :=
        Real.sqrt_lt_sqrt (by norm_num) h
    _ = 8 := h64

/-- `2 * √10 < 8`: another numeric bound used in part (c2). -/
lemma two_sqrt_10_lt_8 : 2 * Real.sqrt 10 < 8 := by
  have h : Real.sqrt 10 < 4 := by
    have h1 : (10 : ℝ) < 4^2 := by norm_num
    have h16 : Real.sqrt (4^2 : ℝ) = 4 := by
      rw [Real.sqrt_sq]; norm_num
    calc Real.sqrt 10 < Real.sqrt (4^2 : ℝ) :=
          Real.sqrt_lt_sqrt (by norm_num) h1
      _ = 4 := h16
  linarith

snip end

/-- Part (a): the upper content of a closed segment equals its length. -/
problem imc1996_p6_part_a (a b : ℝ × ℝ) :
    upperContent (segment ℝ a b) = dist a b := by
  -- TODO: full formalization. Outline:
  --
  -- (≤) Take the trivial cover by `{segment ℝ a b}`; its diameter is
  --     `dist a b`.
  -- (≥) For any finite cover `segment ⊂ ⋃ Eᵢ`, project orthogonally
  --     onto the line through `a` and `b`. The projected cover is a
  --     cover of `[0, dist a b] ⊂ ℝ` by sets of diameter no larger
  --     than `diam(Eᵢ)`. The total diameter of any cover of an
  --     interval `[0, L]` is at least `L` (one-dimensional outer
  --     measure / interval-cover lemma).
  sorry

/-- Part (b): for every set `E`, the upper content dominates the
lower content. -/
problem imc1996_p6_part_b (E : Set (ℝ × ℝ)) :
    lowerContent E ≤ upperContent E := by
  -- TODO: full formalization. Outline:
  --
  -- For any contraction `f : E → segment ℝ a b` and any finite cover
  -- `E ⊂ ⋃ Eᵢ`, the family `f(Eᵢ)` covers `segment ℝ a b`, and
  -- `diam(f(Eᵢ)) ≤ diam(Eᵢ)` because `f` is 1-Lipschitz. Apply (a):
  --   `dist a b = upperContent(segment a b)
  --             ≤ ∑ diam(f(Eᵢ)) ≤ ∑ diam(Eᵢ)`.
  -- Take infimum over covers (right) and sup over `(a, b, f)` (left).
  sorry

/-- The compact set used in part (c): the union of the two triangles
`T` and `T'`. We define it as the union of the two convex hulls of the
three-vertex sets. -/
noncomputable def counterexampleSet : Set (ℝ × ℝ) :=
  convexHull ℝ ({(-2, 2), (2, 2), (0, 4)} : Set (ℝ × ℝ)) ∪
    convexHull ℝ ({(-2, -2), (2, -2), (0, -4)} : Set (ℝ × ℝ))

/-- Part (c): there exists a compact set `E ⊂ ℝ²` with
`lowerContent E < upperContent E`. -/
problem imc1996_p6_part_c :
    ∃ E : Set (ℝ × ℝ),
      IsCompact E ∧ lowerContent E < upperContent E := by
  -- TODO: full formalization. Outline:
  --
  -- Take `E = counterexampleSet`. Show:
  --   (i)  `E` is compact (finite union of convex hulls of finite sets,
  --        each compact).
  --   (ii) `upperContent E ≥ 8`: any cover either splits into covers
  --        of the two horizontal sides `[(-2,2),(2,2)]` and
  --        `[(-2,-2),(2,-2)]` of length 4 each (total ≥ 8 by (a)), or
  --        contains a piece meeting both `T` and `T'`; in the latter
  --        case, vertical projection gives a cover of an interval of
  --        length `8`.
  --   (iii) `lowerContent E < 8`: any contraction `f : E → segment a b`
  --         with `f(a₀) = a, f(b₀) = b` gives `ℓ(L) ≤ √50` (if
  --         `(a₀)₂ ≤ 3`) or `ℓ(L) ≤ 2 √10` (if `(a₀)₂ > 3, (b₀)₂ < -3`).
  --         In either case `ℓ(L) < 8`.
  refine ⟨counterexampleSet, ?_, ?_⟩
  · -- compactness: finite union of two compact convex hulls
    sorry
  · -- strict inequality: lower content `< 8 ≤` upper content.
    sorry

end Imc1996P6
