/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2006, Problem 5

(Day 1, Problem 5.)

Let `a, b, c, d, e` be positive real numbers with
`a² + b² + c² = d² + e²` and `a⁴ + b⁴ + c⁴ = d⁴ + e⁴`.
Compare `a³ + b³ + c³` with `d³ + e³`.

Answer: `a³ + b³ + c³ < d³ + e³`.
-/

namespace Imc2006P5

/-- The comparison result: under the given hypotheses, the three-term cube sum is
strictly less than the two-term cube sum. -/
problem imc2006_p5
    (a b c d e : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (h2 : a^2 + b^2 + c^2 = d^2 + e^2)
    (h4 : a^4 + b^4 + c^4 = d^4 + e^4) :
    a^3 + b^3 + c^3 < d^3 + e^3 := by
  -- This is a nontrivial inequality; the standard proof uses the function
  -- `f(x) = a^x + b^x + c^x - d^x - e^x`, observes `f(2) = f(4) = 0`, and
  -- argues by Rolle's theorem that `f` cannot change sign more than twice,
  -- together with `f(0) = 1 > 0`, to conclude `f < 0` on `(2, 4)`, hence
  -- `f(3) < 0`.
  sorry

end Imc2006P5
