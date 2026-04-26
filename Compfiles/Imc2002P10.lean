/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2002, Problem 10
(IMC 2002, Day 2, Problem 4)

In tetrahedron `OABC`, let `α = ∠BOC`, `β = ∠COA`, `γ = ∠AOB`. Let `σ` be the
dihedral angle along the edge `OA` (between faces `OAB` and `OAC`) and let `τ`
be the dihedral angle along the edge `OB` (between faces `OBA` and `OBC`).
Prove that
  `γ > β · cos σ + α · cos τ`.

## Solution outline

(Spherical / Gauss–Bonnet style.) Normalize so that `‖OA‖ = ‖OB‖ = ‖OC‖ = 1`.
Slice the unit sphere centered at `O` with the three angular regions `BOC`,
`COA`, `AOB`. The slice areas are `α/2`, `β/2`, `γ/2` respectively.

Project the slices `AOC` and `COB` orthogonally onto the plane `OAB`. The
signed projected areas are `(β cos σ)/2` and `(α cos τ)/2`. A case analysis on
the signs of `cos σ`, `cos τ` shows that the projected slices fit strictly
inside the slice `BOA` (with area `γ/2`), giving the inequality.

This formalization records the statement; the full geometric proof requires a
substantial amount of differential / spherical geometry that is not yet
available in Mathlib, so the proof is left as a `sorry`.
-/

namespace Imc2002P10

open scoped RealInnerProductSpace
open InnerProductGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The orthogonal projection of `v` onto the hyperplane through the origin
perpendicular to `u`, given as a vector in `V`. When `u = 0` this is `v`. -/
noncomputable def projOrth (u v : V) : V :=
  v - (inner ℝ v u / inner ℝ u u) • u

/-- The dihedral angle along edge `Ou`, between the half-plane through `v` and
the half-plane through `w` (both half-planes meeting along the line through
`O` and `u`). It is the unoriented angle between the orthogonal projections of
`v` and `w` onto the plane perpendicular to `u`. -/
noncomputable def dihedralAngleAt (u v w : V) : ℝ :=
  angle (projOrth u v) (projOrth u w)

/-- IMC 2002 / Day 2 / Problem 4.

Let `OA`, `OB`, `OC` be three nonzero vectors in a real inner product space
(thought of as the edges of a tetrahedron `OABC` from the vertex `O`).
Set `α = ∠BOC`, `β = ∠COA`, `γ = ∠AOB`, and let `σ` (resp. `τ`) be the
dihedral angle along the edge `OA` (resp. `OB`) of the tetrahedron. Then

  `γ > β · cos σ + α · cos τ`.

The hypothesis that `OA`, `OB`, `OC` are linearly independent (i.e. `OABC` is
a non-degenerate tetrahedron) is essential and is encoded as the condition
that the three vectors are not coplanar. -/
problem imc2002_p10
    (A B C : EuclideanSpace ℝ (Fin 3))
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hindep : LinearIndependent ℝ ![A, B, C]) :
    let α := angle B C
    let β := angle C A
    let γ := angle A B
    let σ := dihedralAngleAt A B C
    let τ := dihedralAngleAt B A C
    γ > β * Real.cos σ + α * Real.cos τ := by
  -- The proof is the spherical-area / Gauss–Bonnet argument outlined in the
  -- module docstring. It requires substantial machinery (areas of spherical
  -- regions and their behaviour under orthogonal projection) that is not yet
  -- available in Mathlib.
  sorry

end Imc2002P10
