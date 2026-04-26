/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2011, Problem 5

Let `n` be a positive integer and let `V` be a `(2n-1)`-dimensional vector space
over the two-element field. Prove that for arbitrary vectors
`v₁, …, v_{4n-1} ∈ V`, there exists a sequence
`1 ≤ i₁ < … < i_{2n} ≤ 4n-1` of indices such that
`v_{i₁} + … + v_{i_{2n}} = 0`.

## Solution sketch

Translation invariance lets us assume `0 ∈ aff{v₁, …, v_{4n-1}}`. Let
`d = dim(aff{vᵢ})`. After permuting we can arrange that
`v₁+v₂, v₃+v₄, …, v_{2d-1}+v_{2d}` form a basis of the affine hull;
the proof is by induction on `d`. Then writing the vector
`w = (v₁ + v₃ + … + v_{2d-1}) + (v_{2d+1} + … + v_{2n+d})`
in this basis gives `w + Σᵢ εᵢ(v_{2i-1}+v_{2i}) = 0` for some choice of
`εᵢ ∈ {0,1}`, and the resulting equality involves exactly `2n` of the
original vectors.

This is the EGZ-style theorem of Davenport over `𝔽₂`; we model `V` as
`Fin (2*n - 1) → ZMod 2` and the family of vectors as
`Fin (4*n - 1) → V`.
-/

namespace Imc2011P5

open Finset BigOperators

problem imc2011_p5 (n : ℕ) (hn : 0 < n)
    (v : Fin (4 * n - 1) → Fin (2 * n - 1) → ZMod 2) :
    ∃ S : Finset (Fin (4 * n - 1)), S.card = 2 * n ∧
      ∑ i ∈ S, v i = 0 := by
  -- TODO: formalize the basis-of-pair-sums argument from the official
  -- solution. The proof uses: (1) translation invariance, (2) induction
  -- on the dimension of the affine hull to construct a basis of pair
  -- sums, (3) decoding any element of the affine hull in this basis to
  -- exhibit `2n` vectors summing to zero.
  sorry

end Imc2011P5
