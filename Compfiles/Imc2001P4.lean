/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .NumberTheory] }

/-!
# International Mathematical Competition 2001, Problem 4
(IMC 2001, Day 1, Problem 4)

Let `p` be a polynomial of degree `n` with integer coefficients, all of absolute
value at most `1`, divisible by `(X - 1)^k`. Let `q` be a prime number such that
`q / log q < k / log (n + 1)`. Prove that every non-trivial `q`-th root of unity
`ε` (i.e. every primitive `q`-th root of unity) is a root of `p`.

## Solution sketch

Write `p = (X - 1)^k · r` over `ℤ`. The minimal polynomial of any primitive
`q`-th root of unity `ε_j = exp(2πij/q)` (`1 ≤ j ≤ q - 1`) over `ℚ` is the
cyclotomic polynomial `Φ_q`, which is irreducible over `ℚ`. Hence either *all*
of the `ε_j` are roots of `r`, or *none* of them are.

Suppose, for contradiction, that none of them is a root. Then
`N = ∏_{j=1}^{q-1} r(ε_j)` is a nonzero algebraic integer fixed by every Galois
automorphism, so `N` is a nonzero integer; in particular `|N| ≥ 1`. Using
`|p(ε_j)| ≤ n + 1` (since `p` has `n + 1` coefficients each of absolute value
≤ 1) and the identity `∏_{j=1}^{q-1}(1 - ε_j) = Φ_q(1) = q`, we obtain

  `(n + 1)^(q - 1) ≥ ∏ |p(ε_j)| = q^k · |N| ≥ q^k`.

Taking logarithms gives `(q - 1) · log (n + 1) ≥ k · log q`, hence
`q / log q ≥ k / log (n + 1)`, contradicting the hypothesis.
-/

namespace Imc2001P4

open Polynomial Complex

/-- A primitive `q`-th root of unity (where `q` is prime) is given by
`exp (2 π i j / q)` for `1 ≤ j ≤ q - 1`. -/
noncomputable def primRoot (q j : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * j / q)

problem imc2001_p4
    (n k : ℕ) (q : ℕ) (hq : q.Prime)
    (p : Polynomial ℤ)
    (hpdeg : p.natDegree = n)
    (hpcoeff : ∀ i, |p.coeff i| ≤ 1)
    (hpdvd : (X - C (1 : ℤ)) ^ k ∣ p)
    (hbound : (q : ℝ) / Real.log q < (k : ℝ) / Real.log (n + 1)) :
    ∀ j : ℕ, 1 ≤ j → j ≤ q - 1 →
      (p.map (Int.castRingHom ℂ)).eval (primRoot q j) = 0 := by
  -- TODO: Full proof. The argument requires:
  --   (1) Cyclotomic polynomial `Φ_q` is irreducible over `ℚ` and is the
  --       minimal polynomial of every primitive `q`-th root of unity. Hence
  --       if `r ∈ ℤ[X]` and `Φ_q ∤ r`, then `r(ε_j) ≠ 0` for every `j`.
  --   (2) Writing `p = (X - 1)^k · r` and assuming for contradiction that
  --       `r(ε_j) ≠ 0` for some (equivalently all) `j`, the product
  --       `N = ∏_{j=1}^{q-1} r(ε_j)` is a nonzero rational integer.
  --   (3) The factorization `∏_{j=1}^{q-1} (X - ε_j) = Φ_q(X)` evaluated at
  --       `X = 1` gives `∏_{j=1}^{q-1} (1 - ε_j) = q`.
  --   (4) The crude bound `|p(ε_j)| ≤ n + 1` follows from
  --       `|p(z)| ≤ ∑ |p.coeff i| · |z|^i ≤ ∑_{i=0}^{n} 1 = n + 1` when `|z| = 1`.
  --   (5) Combining (2), (3), (4) yields `(n + 1)^(q - 1) ≥ q^k`, which after
  --       taking logarithms contradicts the hypothesis on `q`.
  sorry

end Imc2001P4
