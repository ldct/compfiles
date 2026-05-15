/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra, .NumberTheory] }

/-!
# International Mathematical Competition 2011, Problem 9

Let `f(x)` be a polynomial with real coefficients of degree `n`. Suppose
`(f(k) - f(m)) / (k - m)` is an integer for all integers `0 ≤ k < m ≤ n`.
Prove that `a - b` divides `f(a) - f(b)` for all distinct integers `a` and `b`.

## Solution sketch

WLOG `f(0) = 0` (replace `f` by `f - f(0)`; the hypothesis is invariant and the
conclusion is invariant). Then for `1 ≤ m ≤ n`, `m ∣ f(m)`, so `f(m) ∈ ℤ` and in
fact `m ∣ f(m)`.

Let `L(k) = lcm(1, …, k)` and `h_k(x) = L(k) · C(x, k)`. The Vandermonde
identity gives `(a - b) ∣ h_k(a) - h_k(b)` for all integers `a, b`.

Expand `f(x) = ∑ A_k C(x, k)`. By induction on `m`, one shows `L(m) ∣ A_m`.
The conclusion then follows.
-/

namespace Imc2011P9

open Polynomial

snip begin

-- TODO: establish the lemmas described in the docstring.

snip end

problem imc2011_p9 (f : ℝ[X])
    (hint : ∀ k m : ℤ, 0 ≤ k → k < m → m ≤ f.natDegree →
      ∃ z : ℤ, f.eval (k : ℝ) - f.eval (m : ℝ) = (k - m : ℝ) * (z : ℝ)) :
    ∀ a b : ℤ, a ≠ b →
      ∃ z : ℤ, f.eval (a : ℝ) - f.eval (b : ℝ) = (a - b : ℝ) * (z : ℝ) := by
  -- This is a substantial formalization; left as TODO.
  sorry

end Imc2011P9
