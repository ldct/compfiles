/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics, .Algebra] }

/-!
# International Mathematical Competition 2015, Problem 8

Consider all `26^26` words of length `26` in the Latin alphabet.
Define the *weight* of a word as `1/(k+1)`, where `k` is the number of letters
not used in this word. Prove that the sum of the weights of all words is `3^75`.

The proof strategy:
1. Use the identity `1/(k+1) = ∑_{j=0}^{k} (-1)^j C(k,j) / (j+1)`.
2. Switch the order of summation by counting pairs `(w, S)` with
   `S ⊆ unused(w)` and `|S| = j`.
3. For fixed `S`, words `w` with `S ⊆ unused(w)` are exactly maps
   `Fin 26 → (Fin 26 \ S)`, of which there are `(26 - |S|)^26`.
4. So the sum equals `∑_{j=0}^{26} C(26,j) (-1)^j / (j+1) * (26-j)^26`.
5. This equals `27^25 = 3^75` by the finite-difference identity
   `Δ^{n+1} f ≡ 0` for `deg f ≤ n`, applied to `f(x) = (n-x)^n` at `x = -1`.
-/

namespace Imc2015P8

open Finset BigOperators

/-- The weight of a word `w : Fin 26 → Fin 26` is `1/(k+1)` where `k` is the number
of letters not in the image of `w`. -/
noncomputable def weight (w : Fin 26 → Fin 26) : ℚ :=
  1 / ((26 - (Finset.univ.image w).card : ℕ) + 1 : ℚ)

problem imc2015_p8 :
    ∑ w : Fin 26 → Fin 26, weight w = (3 : ℚ) ^ 75 := by
  -- The full proof requires:
  --   (a) Switching order of summation using
  --       `1/(k+1) = ∑_{j=0}^k (-1)^j C(k,j) / (j+1)`, yielding
  --       `∑_{j=0}^{26} C(26,j) (-1)^j (26-j)^26 / (j+1)`.
  --   (b) Evaluating this sum to `27^25 = 3^75` via the finite-difference identity.
  -- TODO: complete the formalization.
  sorry

end Imc2015P8
