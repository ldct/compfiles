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
  -- TODO: Official solution (volume packing + separating hyperplane).
  -- Take an inclusion-maximal set {p₁, …, p_m} ⊆ ∂K such that the
  -- translated bodies Kᵢ = pᵢ + (ε/2) K have pairwise disjoint interiors,
  -- and let L = conv{p₁, …, p_m}.
  --
  -- Counting:  Each Kᵢ ⊆ (1+ε/2) K \ (1-ε/2) K (using central symmetry
  -- and pᵢ ∈ ∂K).  Volume comparison gives
  --   m · (ε/2)^d · vol K ≤ ((1+ε/2)^d - (1-ε/2)^d) · vol K
  --                      ≤ (3/2)^d · ε · vol K,
  -- whence m ≤ 3^d · ε^{1-d}.  So C(d) := 3^d works.
  --
  -- Inclusion (1-ε) K ⊆ L:  if p ∈ (1-ε) K \ L, separate by a linear
  -- functional ℓ with ℓ(p) > maxᵢ ℓ(pᵢ).  Pick x ∈ K maximising ℓ; by
  -- maximality of {pᵢ}, x + (ε/2) K meets some Kᵢ, giving
  -- ℓ(pᵢ) ≥ (1-ε) · max_K ℓ ≥ ℓ(p), contradiction.
  --
  -- Mathlib gaps:  volume scaling for centrally symmetric convex bodies
  -- in EuclideanSpace, Minkowski-sum volume bound, and a usable
  -- formulation of the geometric Hahn–Banach theorem on Finset.convexHull.
  sorry

end Imc2020P3
