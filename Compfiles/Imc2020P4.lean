/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2020, Problem 4

A polynomial `p` with real coefficients satisfies `p(x+1) − p(x) = x^100` for
all `x ∈ ℝ`. Prove that `p(1−t) ≥ p(t)` for `0 ≤ t ≤ 1/2`.
-/

namespace Imc2020P4

open Polynomial

snip begin

/--
Helper: `0^100 = 0` evaluated over `ℝ`. Used for the boundary condition `D(0) = 0`.
-/
lemma zero_pow_hundred : (0 : ℝ) ^ 100 = 0 := by norm_num

/--
Boundary value: `D(0) = p(1) - p(0) = 0`.
-/
lemma boundary_zero (p : ℝ[X]) (hp : ∀ x : ℝ, p.eval (x + 1) - p.eval x = x ^ 100) :
    p.eval 1 - p.eval 0 = 0 := by
  have h := hp 0
  simpa [zero_pow_hundred] using h

/--
Boundary value at `t = 1/2`: trivially `D(1/2) = p(1/2) - p(1/2) = 0`.
-/
lemma boundary_half (p : ℝ[X]) : p.eval (1 - (1/2 : ℝ)) - p.eval (1/2) = 0 := by
  norm_num

/--
Reformulation: substituting `x = -t` into the difference equation gives
`p(1 - t) = p(-t) + t^100`. Hence `p(1 - t) ≥ p(t)` is equivalent to
`p(t) - p(-t) ≤ t^100`.
-/
lemma reflect_identity (p : ℝ[X]) (hp : ∀ x : ℝ, p.eval (x + 1) - p.eval x = x ^ 100)
    (t : ℝ) :
    p.eval (1 - t) = p.eval (-t) + t ^ 100 := by
  have h := hp (-t)
  have hpow : (-t : ℝ) ^ 100 = t ^ 100 := by ring
  have h1 : p.eval (-t + 1) = p.eval (-t) + t ^ 100 := by
    rw [← hpow]; linarith
  rw [show (1 : ℝ) - t = -t + 1 from by ring]
  exact h1

/--
Equivalent formulation: `p(1-t) - p(t) = (p(-t) - p(t)) + t^{100}`.
-/
lemma diff_eq_reflect (p : ℝ[X]) (hp : ∀ x : ℝ, p.eval (x + 1) - p.eval x = x ^ 100)
    (t : ℝ) :
    p.eval (1 - t) - p.eval t = (p.eval (-t) - p.eval t) + t ^ 100 := by
  rw [reflect_identity p hp t]; ring

snip end

problem imc2020_p4 (p : ℝ[X])
    (hp : ∀ x : ℝ, p.eval (x + 1) - p.eval x = x ^ 100)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    p.eval t ≤ p.eval (1 - t) := by
  -- The standard proof uses complex analysis: extend p to ℂ, consider
  -- `h(z) = p(1 - z̄) - p(z)`, show Re h ≥ 0 on the strip `0 ≤ Re z ≤ 1/2`
  -- via the maximum principle on a rectangle `[0, 1/2] × [-N, N]`.
  -- On the vertical line `Re z = 1/2`, `h(1/2 + it) + conj h(1/2 + it) = 0`
  -- so Re h = 0 there. On `Re z = 0`, `h(it) = t^100 ≥ 0` is real.
  -- For large |t|, Re h is dominated by the leading term with positive sign.
  -- Hence Re h ≥ 0 on the strip, and on [0, 1/2] ⊆ ℝ we get p(1-t) - p(t) ≥ 0.
  --
  -- Formalizing the maximum-principle-on-a-rectangle argument in Mathlib
  -- requires substantial complex-analysis scaffolding; this remains open.
  sorry

end Imc2020P4
