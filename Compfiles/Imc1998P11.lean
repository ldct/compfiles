/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Competition 1998, Problem 11 (Day 2, Problem 5)

Suppose that `𝒮` is a family of spheres (i.e. surfaces of balls of positive
radius) in `ℝⁿ` (`n ≥ 2`), such that the intersection of any two contains at
most one point. Prove that the set `M` of points that belong to at least two
different spheres of `𝒮` is countable.

## Solution sketch (official IMC solution)

For every `x ∈ M` choose two distinct spheres `S, T ∈ 𝒮` with `x ∈ S ∩ T`. The
complement `ℝⁿ ∖ (S ∪ T)` has exactly three connected components: write `U`,
`V`, `W` for them, with `∂U = S` (and `T ⊄ ∂U`), `∂V = T` (and `S ⊄ ∂V`), and
let `W` be the third (unbounded) component. The point `x` is then the unique
point of `U⁻ ∩ V⁻` (closure intersection).

Choose three points with rational coordinates `u ∈ U`, `v ∈ V`, `w ∈ W`. We
claim that the assignment `x ↦ (u, v, w)` is injective into the countable set
`ℚⁿ × ℚⁿ × ℚⁿ`, which is countable, so `M` is countable.

For injectivity, suppose another point `x' ∈ M` arrived at the same triple
`(u, v, w)` using spheres `S', T'` with components `U', V', W'`. Since
`|S ∩ S'| ≤ 1` and the two open sets `U, U'` share a point `u`, one must
contain the other; similarly for `V, V'` and `W, W'`. Up to swapping the
roles of `U/V` and of `x/x'`, only two cases remain:

* `U ⊃ U'` and `V ⊃ V'`: then `x' ∈ U'⁻ ∩ V'⁻ ⊂ U⁻ ∩ V⁻ = {x}`, so `x = x'`.
* `U ⊂ U'`, `V ⊃ V'`, `W ⊂ W'`: from `W ⊂ W'` we get `U' ⊂ U ∪ V ∪ {x}`.
  But `U'` is open and connected and `U ∩ V = ∅` with `{x}` a single point,
  so `U' ⊂ U` (else `U'` would split). Combined with `U ⊂ U'` we get `U = U'`,
  reducing to the previous case.

## Status

This is a sorry-skeleton. The statement is fully formalised. The proof
requires substantial work in topology of spheres in `ℝⁿ`:

* The Jordan-Brouwer-type fact that the complement of a sphere has exactly
  two connected components (one bounded, one unbounded), and consequently
  that `ℝⁿ ∖ (S ∪ T)` has three components when `S, T` meet in one point.
* A choice of rational points in each open component (each is open and
  non-empty, hence contains a rational point because `ℚⁿ` is dense in `ℝⁿ`).
* The geometric "component containment" argument, which uses the connectedness
  of each component and the hypothesis that each pair of spheres meets in at
  most one point.

Mathlib does not currently have a clean Jordan-Brouwer separation theorem for
spheres in `ℝⁿ`, so a full Lean formalisation would either build that
infrastructure or specialise to round spheres (where one can use the explicit
inside/outside decomposition by distance to the centre).
-/

namespace Imc1998P11

open Metric Set

/-- A sphere in `ℝⁿ` with positive radius, parametrised by its centre and
radius. -/
structure RoundSphere (n : ℕ) where
  /-- The centre of the sphere. -/
  centre : EuclideanSpace ℝ (Fin n)
  /-- The radius of the sphere; required to be strictly positive. -/
  radius : ℝ
  /-- Positivity of the radius. -/
  radius_pos : 0 < radius

/-- The underlying set of points of a `RoundSphere`. -/
def RoundSphere.toSet {n : ℕ} (S : RoundSphere n) : Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.sphere S.centre S.radius

/-- Coerce a `RoundSphere n` to a `Set (EuclideanSpace ℝ (Fin n))` automatically. -/
instance {n : ℕ} : CoeTC (RoundSphere n) (Set (EuclideanSpace ℝ (Fin n))) :=
  ⟨RoundSphere.toSet⟩

/-- The set of points lying on at least two distinct spheres of the family. -/
def doubleCoveredSet {n : ℕ} (𝒮 : Set (RoundSphere n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∃ S ∈ 𝒮, ∃ T ∈ 𝒮, S ≠ T ∧ x ∈ S.toSet ∧ x ∈ T.toSet}

/-- IMC 1998 P11. If every two distinct spheres of `𝒮` meet in at most one
point, then the set of points covered by at least two spheres is countable. -/
problem imc1998_p11 (n : ℕ) (_hn : 2 ≤ n) (𝒮 : Set (RoundSphere n))
    (_hpair : ∀ S ∈ 𝒮, ∀ T ∈ 𝒮, S ≠ T → (S.toSet ∩ T.toSet).Subsingleton) :
    (doubleCoveredSet 𝒮).Countable := by
  -- TODO: Formalise the official solution.
  --
  -- Step 1: For each `x ∈ doubleCoveredSet 𝒮`, choose two spheres `S, T ∈ 𝒮`
  -- with `S ≠ T` and `x ∈ S ∩ T` (using `Classical.choice` and the definition
  -- of `doubleCoveredSet`).
  --
  -- Step 2: Identify the three connected components of
  -- `(EuclideanSpace ℝ (Fin n)) ∖ (S.toSet ∪ T.toSet)`.
  -- For round spheres, one can use the inside/outside split via distance to
  -- the centre: write `B(c, r) = {y | dist y c < r}` and the open exterior
  -- `Ext(c, r) = {y | dist y c > r}`. Then
  --   `ℝⁿ ∖ S = B(c_S, r_S) ⊔ Ext(c_S, r_S)`
  -- and similarly for `T`. Intersecting the four pairs gives at most four
  -- non-empty pieces, but the interior-of-S ∩ interior-of-T pair is empty
  -- (it would force `S ∩ T` to contain a circle if `S, T` are both bounding
  -- the same region), so three components remain. (Care: this needs the
  -- `|S ∩ T| ≤ 1` hypothesis and the `n ≥ 2` hypothesis to rule out tangencies
  -- giving more than one common point.)
  --
  -- Step 3: Each of the three open sets `U, V, W` is non-empty and open, so
  -- contains a rational point (using density of `ℚⁿ` in `ℝⁿ`, e.g. via
  -- `Rat.denseRange_cast` componentwise, or `EuclideanSpace.exists_mem_denseRange`).
  --
  -- Step 4: Define `f : doubleCoveredSet 𝒮 → (Fin n → ℚ) × (Fin n → ℚ) × (Fin n → ℚ)`
  -- by `f x = (u_x, v_x, w_x)`. Show `f` is injective: this is the geometric
  -- core of the problem and uses the case analysis described in the docstring.
  --
  -- Step 5: Conclude using `Set.Countable.injective_image_of_countable_codomain`
  -- (the codomain is countable as a finite product of countable sets).
  sorry

end Imc1998P11
