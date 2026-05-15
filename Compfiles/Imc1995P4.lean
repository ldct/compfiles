/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1995, Problem 4 (Day 1)

Define `F : (1, ∞) → ℝ` by `F(x) = ∫_x^{x²} 1/log t dt`. Show that `F` is
injective on `(1, ∞)` and find its range.

## Answer

The range is `(log 2, ∞)`.

## Proof outline (official solution)

* Differentiating under the integral sign,
  `F'(x) = 2x / log(x²) − 1 / log x = x / log x − 1 / log x = (x − 1) / log x`.
  For `x > 1`, both `x − 1 > 0` and `log x > 0`, so `F'(x) > 0`, hence `F` is
  strictly increasing on `(1, ∞)` and therefore injective.
* As `x → ∞`, `F(x) ≥ (x² − x) · min_{x ≤ t ≤ x²} (1/log t) = (x² − x)/(2 log x)`,
  which tends to `∞`.
* Substituting `t = e^v` gives `F(x) = ∫_{log x}^{2 log x} e^v / v dv`. As
  `x → 1⁺`, `log x → 0⁺`, and using `e^v / v = 1/v + (e^v − 1)/v` together with
  `(e^v − 1)/v → 1` as `v → 0`, the integral tends to
  `∫_{log x}^{2 log x} 1/v dv = log 2`.
* Combining strict monotonicity with continuity of `F` and the two limit
  computations, the range of `F` is the open interval `(log 2, ∞)`.
-/

namespace Imc1995P4

open Set Filter Topology MeasureTheory intervalIntegral Real

noncomputable def F (x : ℝ) : ℝ := ∫ t in x..x^2, 1 / Real.log t

problem imc1995_p4 :
    Set.InjOn F (Ioi 1) ∧ F '' (Ioi 1) = Ioi (Real.log 2) := by
  -- TODO: full proof.
  --
  -- Plan:
  --
  -- (1) [Continuity] `1 / log t` is continuous on `(1, ∞)` since `log t > 0`
  --     for `t > 1`. Hence `1/log` is interval-integrable on any subinterval
  --     of `(1, ∞)`.
  --
  -- (2) [Differentiability of F] Pick base point `2 > 1` and define
  --     `G(y) := ∫ t in 2..y, 1/log t`. By the FTC
  --     (`integral_hasDerivAt_right`) applied at any `y > 1`,
  --     `HasDerivAt G (1 / log y) y`. Since
  --     `F(x) = G(x²) − G(x)` for `x > 1` (by `integral_add_adjacent_intervals`),
  --     the chain rule gives, for `x > 1`:
  --       `HasDerivAt F (2*x*(1/log(x²)) − 1/log x) x`.
  --     Algebraic simplification using `log(x²) = 2 log x`:
  --       `2x/(2 log x) − 1/log x = (x − 1)/log x`.
  --     Hence `F'(x) = (x − 1)/log x > 0` for `x > 1`.
  --
  -- (3) [Strict monotonicity / injectivity] By
  --     `strictMonoOn_of_hasDerivWithinAt_pos` on `Ioi 1`, `F` is strictly
  --     increasing on `Ioi 1`. So `Set.InjOn F (Ioi 1)`.
  --
  -- (4) [Continuity of F] `F` has a derivative everywhere on `Ioi 1`, hence
  --     it is continuous on `Ioi 1`.
  --
  -- (5) [Limit at +∞] For `t ∈ [x, x²]` with `x > 1`, `1/log t ≥ 1/log(x²)
  --     = 1/(2 log x)`, so `F(x) ≥ (x² − x)/(2 log x)`. The right side tends
  --     to `+∞` as `x → ∞`. Hence `Tendsto F atTop atTop`.
  --
  -- (6) [Limit at 1⁺] Substitute `t = e^u`, `dt = e^u du`. Using
  --     `intervalIntegral.integral_comp_smul_deriv` (or
  --     `MeasureTheory.integral_comp_mul_right`-style): for `x > 1`,
  --       `F(x) = ∫ u in (log x)..(2*log x), e^u / u du`.
  --     Split: `e^u / u = 1/u + (e^u − 1)/u`. Then
  --       `∫ u in (log x)..(2*log x), 1/u = log(2*log x) − log(log x) = log 2`,
  --     and the second integrand `(e^u − 1)/u` extends continuously to `1` at
  --     `u = 0` (since `e^u − 1 = u + O(u²)`), so it is bounded near `0`. Its
  --     integral over an interval of length `log x` tends to `0` as
  --     `log x → 0⁺` (`x → 1⁺`). Conclusion: `Tendsto F (𝓝[>] 1) (𝓝 (log 2))`.
  --
  -- (7) [Range identification] `F` is continuous on the open interval
  --     `Ioi 1` (an `OrdConnected` set). Restricting to `Ioi 1`, the
  --     filter `atBot` on `Ioi 1` corresponds to `𝓝[>] 1`, and `atTop`
  --     corresponds to `atTop` on `ℝ`. Apply `ContinuousOn.surjOn_of_tendsto`
  --     to deduce that `F '' Ioi 1` is the open interval bounded by
  --     `log 2` (below) and `+∞` (above). Combined with strict monotonicity,
  --     `F '' Ioi 1 = Ioi (log 2)`.
  sorry

end Imc1995P4
