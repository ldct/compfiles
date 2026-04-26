/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .NumberTheory] }

/-!
# International Mathematical Competition 2015, Problem 10

Let `n` be a positive integer, and let `p(x)` be a polynomial of degree `n`
with integer coefficients. Prove that
\[ \max_{0 \le x \le 1} |p(x)| > \frac{1}{e^n}. \]
-/

namespace Imc2015P10

open Polynomial

problem imc2015_p10 (n : ℕ) (hn : 1 ≤ n) (p : ℤ[X]) (hp : p.natDegree = n) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1,
      1 / Real.exp n < |(p.map (Int.castRingHom ℝ)).eval x| := by
  -- The standard proof integrates `p(x)^(2k)` over `[0,1]` and uses:
  --   (1) The integral is a positive rational whose denominator divides
  --       `lcm(1, 2, …, 2kn+1)`; hence `∫₀¹ p(x)^{2k} dx ≥ 1 / lcm(1,…,2kn+1)`.
  --   (2) By the prime number theorem, `log(lcm(1,…,N)) ∼ N`.
  -- Letting `M = max |p|` on `[0,1]`, we get `M^{2k} > e^{-(1+ε)(2kn+1)}` for
  -- any `ε > 0` and large `k`, giving `M ≥ e^{-n}`. Since `e` is transcendental,
  -- equality is impossible, so `M > e^{-n}`.
  --
  -- Both ingredients (quantitative PNT for lcm, transcendence of e) are
  -- substantial and not readily available in Mathlib, so this proof is
  -- left as a sorry.
  -- TODO: formalize the PNT-based bound on `lcm(1,…,N)` and use transcendence of `e`.
  sorry


end Imc2015P10
