/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2004, Problem 4

Let `M` be a finite set of `n ≥ 4` points in `ℝ³` no four of which are coplanar.
Suppose `M` is 2-coloured (with colours `+1` and `-1`, encoded by a function
`f : ℝ³ → {-1, +1}`) so that, for every sphere `S` whose intersection with `M`
contains at least four points, the colours on `S ∩ M` are balanced (i.e.
`∑ X ∈ S ∩ M, f X = 0`). Prove that all points of `M` lie on a single sphere.

## Outline of the standard solution

Define `Σ = ∑ X ∈ M, f X`.

For any three pairwise distinct points `A, B, C ∈ M`, let
`𝒮(A, B, C)` be the family of spheres through `A, B, C` whose intersection
with `M` contains at least one further point.  Summing the colour-balance
condition over `S ∈ 𝒮(A, B, C)` and over points of `S ∩ M` gives
`0 = (|𝒮(A, B, C)| - 1) (f A + f B + f C) + Σ`,
because each point of `M ∖ {A, B, C}` lies on exactly one sphere through
`A, B, C` (this uses the no-4-coplanar hypothesis).

If for some triple `(A, B, C)` we have `|𝒮(A, B, C)| = 1` then there is a
single sphere through `A, B, C` containing every other point of `M`, and the
conclusion follows.  Otherwise `|𝒮(A, B, C)| ≥ 2`, and summing the displayed
identity over all triples in `M` of size `3` together with simple sign
considerations forces `Σ = 0`, hence `f A + f B + f C = 0` for every triple.
Comparing two such identities (with shared variables) shows that `f` must
vanish on `M`, contradicting `f ∈ {-1, +1}`.

The geometric step "through any three non-collinear points, every other point
of `M` not coplanar with them lies on exactly one sphere through the three"
is genuine 3-D Euclidean geometry, which we leave as a `sorry` (the file is
otherwise structured for such a refinement).
-/

namespace Imc2004P4

open scoped BigOperators

/-- Points of three-dimensional Euclidean space. -/
abbrev Pt := EuclideanSpace ℝ (Fin 3)

/-- A subset `M : Finset Pt` is "in general position with respect to spheres"
in our sense if no four of its points are affinely dependent (equivalently,
no four are coplanar).

We express this as `AffineIndependent` over the corresponding `Finset.attach`
indexing whenever we pick four distinct points. -/
def NoFourCoplanar (M : Finset Pt) : Prop :=
  ∀ (p : Fin 4 → Pt), Function.Injective p → (∀ i, p i ∈ M) →
    AffineIndependent ℝ p

/-- `OnCommonSphere M` says that all points of `M` lie on a common sphere. -/
def OnCommonSphere (M : Finset Pt) : Prop :=
  ∃ c : Pt, ∃ r : ℝ, ∀ x ∈ M, x ∈ Metric.sphere c r

problem imc2004_p4
    (M : Finset Pt) (hMcard : 4 ≤ M.card)
    (hM : NoFourCoplanar M)
    (f : Pt → ℤ)
    (hf : ∀ x ∈ M, f x = 1 ∨ f x = -1)
    (hbal : ∀ c : Pt, ∀ r : ℝ,
        4 ≤ (M.filter (fun x => dist x c = r)).card →
        ∑ x ∈ M.filter (fun x => dist x c = r), f x = 0) :
    OnCommonSphere M := by
  -- The full geometric proof is sketched in the module docstring.
  -- It requires non-trivial 3D Euclidean geometry: through any three
  -- non-collinear points and any further non-coplanar point there is a
  -- unique sphere; counting incidences in two ways yields the conclusion.
  sorry

end Imc2004P4
