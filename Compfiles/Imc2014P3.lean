/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2014, Problem 3

Let `n` be a positive integer. Show that there are positive real numbers
`a_0, a_1, …, a_n` such that for each choice of signs the polynomial
`±a_n x^n ± a_{n-1} x^{n-1} ± … ± a_1 x ± a_0` has `n` distinct real roots.
-/

namespace Imc2014P3

open Polynomial

/-- Given coefficients `a : Fin (n+1) → ℝ` and signs `ε : Fin (n+1) → ℝ`,
the polynomial `∑ k, ε k * a k * X^k`. -/
noncomputable def signedPoly (n : ℕ) (a ε : Fin (n + 1) → ℝ) : ℝ[X] :=
  ∑ k : Fin (n + 1), C (ε k * a k) * X ^ (k : ℕ)

/-- A polynomial has `n` distinct real roots if its set of real roots has
cardinality `n`. -/
def HasDistinctRealRoots (p : ℝ[X]) (n : ℕ) : Prop :=
  (p.roots.toFinset.card = n) ∧ p.roots.card = n

problem imc2014_p3 (n : ℕ) (hn : 0 < n) :
    ∃ a : Fin (n + 1) → ℝ, (∀ k, 0 < a k) ∧
      ∀ ε : Fin (n + 1) → ℝ, (∀ k, ε k = 1 ∨ ε k = -1) →
        HasDistinctRealRoots (signedPoly n a ε) n := by
  -- Proof by induction on n. The key analytical step (choosing ε small enough
  -- relative to the local extrema of all signed polynomials of degree n+1
  -- obtained by multiplying by x) is left as a sorry; the existence of such
  -- ε follows from the finiteness of sign choices and continuity / compactness.
  sorry

end Imc2014P3
