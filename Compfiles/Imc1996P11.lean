/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1996, Problem 11
(Day 2, Problem 5)

(i) Prove
  `lim_{x → +∞} ∑_{n=1}^∞ n·x / (n² + x)² = 1/2`.

(ii) Prove there exists `c > 0` such that, for all `x ≥ 1`,
  `|∑_{n=1}^∞ n·x / (n² + x)² - 1/2| ≤ c / x`.

## Proof outline (official solution)

Set `f(t) = t / (1 + t²)²` and `h = 1/√x`. Then
  `∑_{n ≥ 1} n·x/(n² + x)² = ∑_{n ≥ 1} h · f(n h)`,
since
  `n·x/(n² + x)² = h · (n h) / (1 + (n h)²)²`
when `h² = 1/x`.

(i) As `x → ∞`, `h → 0⁺`, and the right-hand side is a Riemann sum for
`∫_0^∞ f(t) dt`. The integral equals
  `∫_0^∞ t/(1+t²)² dt = [-(1/2) · 1/(1+t²)]_0^∞ = 1/2`.
Convergence of the Riemann sum to the integral holds because `f` is
integrable on `[0, ∞)` and is monotone decreasing on `[1, ∞)` (so the
Riemann sums sandwich the integral up to one term, of size `O(h)`).

(ii) Quantitative version. We bound
  `| h ∑_n f(nh) - ∫_0^∞ f | ≤ ∑_n | h f(nh) - ∫_{(n-1/2)h}^{(n+1/2)h} f |
                              + ∫_0^{h/2} f`.
For each midpoint-rule error,
  `2b · g(a) - ∫_{a-b}^{a+b} g = -(1/2) ∫_0^b (b-t)² (g''(a+t)+g''(a-t)) dt`
(integrate by parts twice). Applied with `g = f`, `a = nh`, `b = h/2`:
  `| h f(nh) - ∫_{(n-1/2)h}^{(n+1/2)h} f | ≤ (h³/24) · sup_{[(n-1/2)h, (n+1/2)h]} |f''|`.
Summing gives `≤ (h²/24) · ∫_{h/2}^∞ |f''(t)| dt = O(h²)` because `f''`
is integrable at infinity (`|f''(t)| = O(1/t⁴)`). The boundary term
`∫_0^{h/2} f(t) dt = ∫_0^{h/2} t/(1+t²)² dt ≤ (h/2)² / 2 = O(h²)`.
Altogether, the error is `O(h²) = O(1/x)`.

## Status

`sorry` skeleton: statements of (i) and (ii) with the auxiliary
function `f(t) = t/(1+t²)²` and the algebraic identity
`n·x/(n² + x)² = (1/√x) · (n/√x) / (1 + (n/√x)²)²`
proved.

A full formalization would require nontrivial Mathlib infrastructure
on (a) the integral `∫_0^∞ t/(1+t²)² dt = 1/2`, (b) Riemann-sum to
improper-integral convergence for monotone integrands, and (c) the
integration-by-parts twice midpoint-rule remainder. These are not
currently available in a directly usable form.
-/

namespace Imc1996P11

open scoped Topology BigOperators
open Filter Real

/-- The summand `n x / (n² + x)²`. -/
noncomputable def term (n : ℕ) (x : ℝ) : ℝ :=
  (n : ℝ) * x / ((n : ℝ) ^ 2 + x) ^ 2

/-- The auxiliary function `f(t) = t / (1 + t²)²`. -/
noncomputable def f (t : ℝ) : ℝ := t / (1 + t ^ 2) ^ 2

/-- The series, for `x > 0`, converges (we just give the sum as a real
number; the corresponding `Summable` fact is also a side condition in
the problem). -/
noncomputable def S (x : ℝ) : ℝ := ∑' n : ℕ, term (n + 1) x

snip begin

/-- The summand vanishes at `n = 0`, so it does not matter whether we
sum from `n = 0` or from `n = 1`. -/
@[simp] lemma term_zero (x : ℝ) : term 0 x = 0 := by
  simp [term]

/-- Algebraic identity relating the summand to `f`:
for `x > 0`, with `s = √x`,
  `n x / (n² + x)² = (1/s) · f(n / s)`. -/
lemma term_eq_h_f {x : ℝ} (hx : 0 < x) (n : ℕ) :
    term n x = (1 / Real.sqrt x) * f ((n : ℝ) * (1 / Real.sqrt x)) := by
  have hxsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hxsqrt_ne : Real.sqrt x ≠ 0 := ne_of_gt hxsqrt_pos
  have hsqsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hxne : x ≠ 0 := ne_of_gt hx
  have hsum_pos : 0 < (n : ℝ) ^ 2 + x := by positivity
  have hsum_ne : ((n : ℝ) ^ 2 + x) ≠ 0 := ne_of_gt hsum_pos
  -- Set s := sqrt x, rewrite x = s^2 everywhere, then close by `field_simp; ring`.
  set s : ℝ := Real.sqrt x with hs_def
  have hs_pos : 0 < s := hxsqrt_pos
  have hs_ne : s ≠ 0 := hxsqrt_ne
  have hxs : x = s ^ 2 := hsqsq.symm
  unfold term f
  rw [hxs]
  have hsum_ne' : (n : ℝ) ^ 2 + s ^ 2 ≠ 0 := by rw [← hxs]; exact hsum_ne
  field_simp
  ring

snip end

/-- Part (i): `lim_{x → +∞} ∑_{n=1}^∞ n·x / (n² + x)² = 1/2`. -/
problem imc1996_p11_part_i :
    Tendsto (fun x : ℝ => ∑' n : ℕ, term (n + 1) x) atTop (𝓝 (1 / 2)) := by
  -- TODO: full formalization. Outline:
  --
  -- Substitute `h = 1/√x`, so `h → 0⁺` as `x → ∞`. By `term_eq_h_f`,
  --   ∑_{n ≥ 1} term n x = h · ∑_{n ≥ 1} f (n h).
  -- The right-hand side is a (left-endpoint) Riemann sum of `f` on
  -- `[0, ∞)`. Show it converges to `∫_0^∞ f = 1/2`.
  --
  -- Two ingredients:
  -- (a) `∫_0^∞ t/(1+t²)² dt = 1/2`. Antiderivative is `-1/(2(1+t²))`,
  --     evaluated from `0` to `∞`: `0 - (-1/2) = 1/2`.
  -- (b) For `f` decreasing on `[1, ∞)` and integrable, the Riemann
  --     sums `h ∑_{n ≥ 1} f(n h)` converge to `∫_0^∞ f` as `h → 0⁺`.
  sorry

/-- Part (ii): there is `c > 0` such that for all `x ≥ 1`,
`|∑_{n=1}^∞ n·x / (n² + x)² - 1/2| ≤ c / x`. -/
problem imc1996_p11_part_ii :
    ∃ c : ℝ, 0 < c ∧
      ∀ x : ℝ, 1 ≤ x →
        |(∑' n : ℕ, term (n + 1) x) - 1 / 2| ≤ c / x := by
  -- TODO: full formalization. Outline:
  --
  -- With `h = 1/√x`, write
  --   ∑_{n ≥ 1} h f(n h) - ∫_0^∞ f
  --     = -∫_0^{h/2} f
  --       + ∑_{n ≥ 1} ( h f(n h) - ∫_{(n-1/2)h}^{(n+1/2)h} f ).
  --
  -- (a) Boundary term: `∫_0^{h/2} t/(1+t²)² dt ≤ ∫_0^{h/2} t dt = h²/8`,
  --     so `|·| = O(h²) = O(1/x)`.
  --
  -- (b) Each midpoint-rule remainder satisfies, by integrating by parts
  --     twice (Taylor's formula with integral remainder):
  --       2b g(a) - ∫_{a-b}^{a+b} g(t) dt
  --         = -(1/2) ∫_0^b (b-t)² (g''(a+t) + g''(a-t)) dt.
  --     Hence
  --       | h f(nh) - ∫_{(n-1/2)h}^{(n+1/2)h} f | ≤ (h³/24) · M_n,
  --     with `M_n = sup_{|t-nh| ≤ h/2} |f''(t)|`.
  --
  -- (c) Summation: Σ_n (h³/24) M_n ≤ (h²/24) · ∫_{h/2}^∞ |f''| = O(h²),
  --     since `|f''(t)| ≤ K/t⁴` for `t ≥ 1` and `f''` is bounded near 0.
  --
  -- All in all, the total error is `O(h²) = O(1/x)`, giving some `c > 0`.
  sorry

end Imc1996P11
