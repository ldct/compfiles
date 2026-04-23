/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2022, Problem 5

We colour all the sides and diagonals of a regular polygon `P` with `43`
vertices either red or blue so that every vertex is an endpoint of `20` red
segments and `22` blue segments. A triangle formed by vertices of `P` is
called monochromatic if all of its sides have the same colour. Suppose there
are `2022` blue monochromatic triangles. How many red monochromatic triangles
are there?

Answer: `859`.
-/

namespace Imc2022P5

/-- The number of red monochromatic triangles. -/
determine answer : ℕ := 859

/-- `c (i, j) = true` means the edge `{i,j}` is red, `false` means blue.
`c` is symmetric and irreflexive. -/
problem imc2022_p5 (c : Fin 43 → Fin 43 → Bool)
    (hsym : ∀ i j, c i j = c j i)
    (hirrefl : ∀ i, c i i = false)
    (hred_deg : ∀ i, (Finset.univ.filter fun j => j ≠ i ∧ c i j = true).card = 20)
    (hblue_tri : (Finset.univ.filter fun t : Fin 43 × Fin 43 × Fin 43 =>
        t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧
        c t.1 t.2.1 = false ∧ c t.2.1 t.2.2 = false ∧ c t.1 t.2.2 = false).card = 2022) :
    (Finset.univ.filter fun t : Fin 43 × Fin 43 × Fin 43 =>
        t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧
        c t.1 t.2.1 = true ∧ c t.2.1 t.2.2 = true ∧ c t.1 t.2.2 = true).card = answer := by
  -- TODO: double counting "cherries" (paths of length 2 with colour switch).
  sorry

end Imc2022P5
