/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2004, Problem 8
(IMC 2004, Day 2, Problem 2)

Let `f, g : [a, b] → [0, ∞)` be continuous and nondecreasing, and assume that
`∫_a^x √(f t) dt ≤ ∫_a^x √(g t) dt` for all `x ∈ [a, b]` and
`∫_a^b √(f t) dt = ∫_a^b √(g t) dt`.
Prove that `∫_a^b √(1 + f t) dt ≥ ∫_a^b √(1 + g t) dt`.

Proof sketch (official solution):

Let `F(x) = ∫_a^x √(f t) dt` and `G(x) = ∫_a^x √(g t) dt`. Both `F` and `G` are
convex (since `√f, √g` are nondecreasing), `F(a) = G(a) = 0`, `F(b) = G(b)`,
and `F ≤ G`. Since `F'(x) = √(f x)` and `G'(x) = √(g x)`, we have
`√(1 + f x) = √(1 + F'(x)²)` and similarly for `g`. Thus the integrals
`∫_a^b √(1 + f)` and `∫_a^b √(1 + g)` are exactly the arc lengths of the
graphs of `F` and `G` over `[a, b]`.

Both graphs connect `(a, 0)` to `(b, F(b))`. `F` is convex, sits below `G`
(also convex) with the same endpoints. The graph of `F` bounds a larger
convex region (together with the segment from `(a, 0)` to `(b, F(b))`), whose
perimeter is longer. Analytically: by convexity of `h(u) = √(1 + u²)`,
`h(F') - h(G') ≥ h'(G') · (F' - G')`; integrating and using integration by
parts together with monotonicity of `h'(G')` and the sign of `F - G` yields
the conclusion.

The full formalization below leaves the analytic conclusion as a `sorry`, as a
rigorous formalization would require Lebesgue-Stieltjes integration by parts
or a careful arc-length argument, both of which exceed the scope of the
current Mathlib API in a self-contained way.
-/

namespace Imc2004P8

open MeasureTheory intervalIntegral Set

problem imc2004_p8 (a b : ℝ) (_hab : a ≤ b) (f g : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Icc a b))
    (hg_cont : ContinuousOn g (Icc a b))
    (hf_nonneg : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hg_nonneg : ∀ x ∈ Icc a b, 0 ≤ g x)
    (_hf_mono : MonotoneOn f (Icc a b))
    (_hg_mono : MonotoneOn g (Icc a b))
    (_hineq : ∀ x ∈ Icc a b,
      ∫ t in a..x, Real.sqrt (f t) ≤ ∫ t in a..x, Real.sqrt (g t))
    (_heq : ∫ t in a..b, Real.sqrt (f t) = ∫ t in a..b, Real.sqrt (g t)) :
    ∫ t in a..b, Real.sqrt (1 + g t) ≤ ∫ t in a..b, Real.sqrt (1 + f t) := by
  -- Proof outline (see module docstring).
  -- Let F(x) = ∫_a^x √f, G(x) = ∫_a^x √g. Then F, G are convex (since
  -- √f, √g nondecreasing), F(a) = G(a) = 0, F(b) = G(b), F ≤ G.
  --
  -- Since F'(x) = √(f x), G'(x) = √(g x) on [a,b], we have
  -- √(1 + f) = √(1 + F'²) and √(1 + g) = √(1 + G'²), so the goal becomes
  --   ∫_a^b √(1 + G'²) ≤ ∫_a^b √(1 + F'²).
  --
  -- By convexity of h(u) = √(1 + u²),
  --   h(F') - h(G') ≥ h'(G')·(F' - G'),
  -- where h'(u) = u/√(1+u²).
  --
  -- Integrating over [a,b]:
  --   ∫(√(1+F'²) - √(1+G'²)) ≥ ∫ h'(G')·(F' - G') dx.
  --
  -- Let φ(x) = G'(x)/√(1+G'(x)²). Since G' = √g is nondecreasing (g ≥ 0 and
  -- nondecreasing), and u/√(1+u²) is increasing, φ is nondecreasing.
  --
  -- Integration by parts (Lebesgue-Stieltjes):
  --   ∫(F'-G')·φ dx = [(F - G)·φ]_a^b - ∫(F - G) dφ.
  --
  -- Boundary term: F(a) - G(a) = 0 and F(b) - G(b) = 0, so this vanishes.
  -- Remaining: - ∫(F - G) dφ. Since F ≤ G, F - G ≤ 0; since φ is nondecreasing,
  -- dφ ≥ 0 as a measure. Hence -(F - G) dφ ≥ 0, so the integral is ≥ 0.
  --
  -- Thus ∫(√(1+f) - √(1+g)) dx ≥ 0.
  sorry

end Imc2004P8
