/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Competition 2009, Problem 5
(Day 1, Problem 5)

Let `S = P_0 P_1 ⋯ P_n` be a non-degenerate `n`-simplex in Euclidean `n`-space and
let `P` be a point in its interior. For each `i`, let `S_i` be the simplex obtained
from `S` by replacing `P_i` with `P`. Writing `v(·)` for the (signed) volume and
`C(·)` for the circumcenter, prove

  `∑ᵢ v(S_i) · C(S_i) = v(S) · C(S)`,

interpreting the equality as an identity of points (with weighted-sum on the left).

## Sketch of solution

Set `q_j = C(S_j) - C(S)` and `p_j = P_j - P`. The geometric definition of `C(S_j)`
yields `⟨p_i, q_j - q_k⟩ = 0` and `⟨q_i, p_j - p_k⟩ = 0` for distinct `i, j, k`.
For `n ≥ 2` this forces `⟨p_i, q_j⟩ = ⟨p_j, q_i⟩` for all `i, j`. The volumes
`V_j = |det(p_0, …, p̂_j, …, p_n)|` and `W_j = |det(q_0, …, q̂_j, …, q_n)|` are
then proportional with the same constant, and the standard identity
`Σ (-1)^j q_j W_j = 0` (a vanishing alternating sum of cofactors) gives
`Σ (-1)^j q_j V_j = 0`, which is the claim. The base case `n = 1` is direct.
-/

namespace Imc2009P5

open scoped EuclideanGeometry
open Affine Matrix

/--
For a finite collection of points `pts : Fin (n+1) → EuclideanSpace ℝ (Fin n)`,
we define `vol pts` as the absolute value of the determinant of the matrix whose
`j`-th row is `pts (j+1) - pts 0` (i.e. the edge vectors from `pts 0`). This is
proportional (by `1/n!`) to the usual Euclidean volume of the simplex, and is
nonzero exactly when the points are affinely independent.
-/
noncomputable def vol {n : ℕ} (pts : Fin (n+1) → EuclideanSpace ℝ (Fin n)) : ℝ :=
  |(Matrix.of (fun (j : Fin n) (k : Fin n) => pts j.succ k - pts 0 k)).det|

/-- Replace the `i`-th vertex of a simplex with a point `P`. -/
def replaceVertex {n : ℕ} {V : Type*} (pts : Fin (n+1) → V) (i : Fin (n+1))
    (P : V) : Fin (n+1) → V := Function.update pts i P

/--
Statement of IMC 2009 Problem 5: for a non-degenerate `n`-simplex with vertices
`pts : Fin (n+1) → EuclideanSpace ℝ (Fin n)` and an interior point `P`, the
weighted sum of the circumcenters of the sub-simplices (each obtained by
replacing one vertex with `P`) equals `vol(S) · C(S)`.

We require `2 ≤ n` since the proof uses an inner-product argument that is only
non-degenerate above dimension 1; the case `n = 1` is handled separately by
direct computation in the source. The interior condition is encoded by
asking that the simplices `S_i = replaceVertex pts i P` are themselves
non-degenerate (their points are affinely independent).
-/
problem imc2009_p5 (n : ℕ) (hn : 2 ≤ n)
    (pts : Fin (n+1) → EuclideanSpace ℝ (Fin n))
    (hpts : AffineIndependent ℝ pts)
    (P : EuclideanSpace ℝ (Fin n))
    (hPi : ∀ i : Fin (n+1), AffineIndependent ℝ (replaceVertex pts i P))
    (S : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin n)) n)
    (hS : S.points = pts)
    (Si : Fin (n+1) → Affine.Simplex ℝ (EuclideanSpace ℝ (Fin n)) n)
    (hSi : ∀ i, (Si i).points = replaceVertex pts i P) :
    (∑ i : Fin (n+1),
        vol (replaceVertex pts i P) • ((Si i).circumcenter -ᵥ
          (0 : EuclideanSpace ℝ (Fin n))))
      = vol pts • (S.circumcenter -ᵥ (0 : EuclideanSpace ℝ (Fin n))) := by
  -- TODO: full proof.
  -- Outline:
  --   (1) Set q_j = C(S_j) - C(S) and p_j = P_j - P.
  --       The defining property of the circumcenter (equidistance from vertices)
  --       gives, for distinct i, j, k:
  --         ⟨p_i, q_j - q_k⟩ = 0  and  ⟨q_i, p_j - p_k⟩ = 0.
  --   (2) For n ≥ 2 the above forces ⟨p_i, q_j⟩ = ⟨p_j, q_i⟩ (symmetry of
  --       the bilinear pairing) and hence the matrices (⟨p_k, q_l⟩) and
  --       (⟨q_k, p_l⟩) coincide.
  --   (3) The Cramer-style cofactor identity Σ_j (-1)^j q_j W_j = 0 (where
  --       W_j = |det(q_0, …, q̂_j, …, q_n)|) holds because Σ_j (-1)^j q_j W_j
  --       is the expansion along a column of a determinant with a repeated row.
  --   (4) The proportionality V_j / W_j = constant (independent of j),
  --       deduced from the shared Gram matrix in (2), turns the identity in (3)
  --       into Σ_j (-1)^j q_j V_j = 0, i.e. Σ_j v(S_j) (C(S_j) - C(S)) = 0.
  --   (5) Since Σ_j v(S_j) = v(S) (the simplex is partitioned by P), this
  --       rearranges to the desired Σ_j v(S_j) C(S_j) = v(S) C(S).
  sorry

end Imc2009P5
