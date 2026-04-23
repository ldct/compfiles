/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.Analysis.Convex.Hull

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2020, Problem 3

Let `d ≥ 2` be an integer. Prove that there exists a constant `C(d)`
such that for any centrally symmetric convex polytope `K ⊂ ℝᵈ` and any
`ε ∈ (0, 1)`, there exists a convex polytope `L ⊂ ℝᵈ` with at most
`C(d) · ε^{1-d}` vertices such that `(1 - ε) · K ⊆ L ⊆ K`.
-/

namespace Imc2020P3

open Set

/-- A (closed) convex polytope in `ℝᵈ` is the convex hull of a nonempty
finite set of vertices. -/
structure Polytope (d : ℕ) where
  vertices : Finset (EuclideanSpace ℝ (Fin d))
  ne : vertices.Nonempty

/-- The underlying set of a polytope. -/
noncomputable def Polytope.toSet {d : ℕ} (P : Polytope d) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  convexHull ℝ (P.vertices : Set _)

/-- `P` is centrally symmetric (about the origin) if `-x ∈ P` for every
`x ∈ P`. -/
def CentrallySymmetric {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ x ∈ S, -x ∈ S

/-- The scaled set `c · S`. -/
def smulSet {d : ℕ} (c : ℝ) (S : Set (EuclideanSpace ℝ (Fin d))) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∃ y ∈ S, x = c • y}

problem imc2020_p3 (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, ∀ (K : Polytope d) (ε : ℝ),
      CentrallySymmetric K.toSet → 0 < ε → ε < 1 →
      ∃ L : Polytope d,
        (L.vertices.card : ℝ) ≤ C * ε ^ (1 - (d : ℤ)) ∧
        smulSet (1 - ε) K.toSet ⊆ L.toSet ∧ L.toSet ⊆ K.toSet := by
  -- TODO: Classical John-ellipsoid style result.
  -- Cover the boundary of K by O(ε^{(1-d)/2}) "caps" each of angular
  -- radius ~√ε; take a spanning polytope with vertices on these caps.
  -- Centrally symmetric version of Dudley-Bronshtein theorem.
  sorry

end Imc2020P3
