/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2012, Problem 5 (Day 1, Problem 5)

Let `a` be a rational number and `n` a positive integer. Prove that the polynomial
`X^(2^n) (X + a)^(2^n) + 1` is irreducible in `ℚ[X]`.
-/

namespace Imc2012P5

open Polynomial

problem imc2012_p5
    (a : ℚ) (n : ℕ) (hn : 0 < n) :
    Irreducible (X ^ (2 ^ n) * (X + C a) ^ (2 ^ n) + 1 : ℚ[X]) := by
  -- The proof has two main parts:
  -- (1) When a = 0: the polynomial is X^(2^(n+1)) + 1, which is the cyclotomic
  --     polynomial Φ_(2^(n+2)), hence irreducible over ℚ.
  -- (2) When a ≠ 0: substitute X = Y - a/2; the polynomial becomes
  --     (Y^2 - a^2/4)^(2^n) + 1. As a polynomial in Z = Y^2 - a^2/4 this is
  --     Φ_(2^(n+1))(Z), so it is irreducible as a polynomial in Y^2.
  --     If it factored in ℚ[Y], comparing constant terms gives a rational
  --     b with (a/2)^(2^(n+1)) + 1 = b^2. Setting c = (a/2)^(2^(n-1)) yields
  --     c^4 + 1 = b^2 with c ≠ 0, contradicting Mathlib's `Fermat42.not_fermat_42`
  --     (Fermat's theorem for n = 4: u^4 + v^4 ≠ w^2 for nonzero u, v).
  sorry

end Imc2012P5
