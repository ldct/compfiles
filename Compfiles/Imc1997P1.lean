/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1997, Problem 1 (Day 1)

Let `εₙ > 0` with `εₙ → 0`. Compute

  `lim_{n → ∞} (1/n) · ∑_{k=1}^{n} log(k/n + εₙ) = -1`.

## Proof outline (official solution)

* `∫₀¹ log x dx = -1`.
* The standard Riemann sum gives `(1/n) · ∑_{k=1}^n log(k/n) → -1` as
  `n → ∞` (this is a Riemann sum for the improper integral of `log` on
  `(0, 1]`).
* For each fixed `ε > 0`,
    `(1/n) · ∑_{k=1}^n log(k/n + ε) → ∫₀¹ log(x + ε) dx`
  as `n → ∞` (this is a standard Riemann sum, since `x ↦ log(x + ε)` is
  continuous on `[0, 1]`); the antiderivative of `log(x + ε)` is
  `(x + ε) log(x + ε) - (x + ε)`, giving
    `∫₀¹ log(x + ε) dx = (1+ε) log(1+ε) - ε log ε - 1 → -1`
  as `ε → 0⁺` (using `ε log ε → 0`).
* Sandwich. For `n` large, `εₙ ≤ ε`, so
    `log(k/n) ≤ log(k/n + εₙ) ≤ log(k/n + ε)`,
  giving `(1/n) ∑ log(k/n) ≤ (1/n) ∑ log(k/n + εₙ) ≤ (1/n) ∑ log(k/n + ε)`.
  Take `n → ∞` first, then `ε → 0⁺`.

## Status

`sorry` skeleton. The full formalization requires:

1. `(1/n) ∑_{k=1}^n log(k/n) → -1` (improper Riemann sum for `log`),
   which is not directly in Mathlib.
2. For `ε > 0`, `(1/n) ∑_{k=1}^n log(k/n + ε) → ∫₀¹ log(x+ε) dx`
   (Riemann sum for a continuous function), which is also not directly
   available in Mathlib in a usable form.
3. `∫₀¹ log(x + ε) dx = (1+ε) log(1+ε) - ε log ε - 1`.
4. `ε log ε → 0` as `ε → 0⁺` (this is in Mathlib as `Real.tendsto_log_mul_self_nhds_zero_right`
   or similar; can be derived from `Real.tendsto_log_div_pow_nhds_zero` etc.).

We prove the auxiliary derivative formula `hasDerivAt_xlog_shift` and the
limit formula `∫₀¹ log(x+ε) dx = (1+ε) log(1+ε) - ε log ε - 1`
(`integral_log_shift`), leaving the Riemann-sum ingredients as `sorry`.
-/

namespace Imc1997P1

open scoped Topology BigOperators
open Filter Real MeasureTheory intervalIntegral

/-- The Riemann-sum `S n` for `log` (without the `εₙ` shift):
`(1/n) ∑_{k=1}^n log(k/n)`. We sum over `k = 1, …, n` (skipping `k = 0`
where `log` would diverge). -/
noncomputable def riemannLog (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * ∑ k ∈ Finset.range n, Real.log ((k + 1 : ℝ) / n)

/-- The shifted Riemann sum
`(1/n) ∑_{k=1}^n log(k/n + ε)`. -/
noncomputable def riemannLogShift (n : ℕ) (ε : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ k ∈ Finset.range n, Real.log ((k + 1 : ℝ) / n + ε)

snip begin

/-- Antiderivative of `log(x + ε)` on `(-ε, ∞)`. -/
lemma hasDerivAt_xlog_shift (ε : ℝ) (x : ℝ) (hx : 0 < x + ε) :
    HasDerivAt (fun y => (y + ε) * Real.log (y + ε) - (y + ε)) (Real.log (x + ε)) x := by
  -- d/dx[(x+ε) log(x+ε) - (x+ε)] = log(x+ε) + (x+ε)·(1/(x+ε)) - 1 = log(x+ε).
  have h1 : HasDerivAt (fun y : ℝ => y + ε) 1 x :=
    (hasDerivAt_id x).add_const ε
  have hlog : HasDerivAt (fun y : ℝ => Real.log (y + ε)) ((x + ε)⁻¹) x := by
    have := (Real.hasDerivAt_log (ne_of_gt hx)).comp x h1
    simpa using this
  have hprod : HasDerivAt (fun y : ℝ => (y + ε) * Real.log (y + ε))
      (1 * Real.log (x + ε) + (x + ε) * (x + ε)⁻¹) x := h1.mul hlog
  have hsub : HasDerivAt
      (fun y : ℝ => (y + ε) * Real.log (y + ε) - (y + ε))
      (1 * Real.log (x + ε) + (x + ε) * (x + ε)⁻¹ - 1) x := hprod.sub h1
  convert hsub using 1
  rw [mul_inv_cancel₀ (ne_of_gt hx)]
  ring

/-- For `ε > 0`,
`∫₀¹ log(x + ε) dx = (1 + ε) log(1 + ε) - ε log ε - 1`. -/
lemma integral_log_shift (ε : ℝ) (hε : 0 < ε) :
    ∫ x in (0:ℝ)..1, Real.log (x + ε) =
      (1 + ε) * Real.log (1 + ε) - ε * Real.log ε - 1 := by
  have hpos : ∀ x ∈ Set.uIcc (0:ℝ) 1, 0 < x + ε := by
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    linarith [hx.1]
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun y => (y + ε) * Real.log (y + ε) - (y + ε))
        (Real.log (x + ε)) x := fun x hx => hasDerivAt_xlog_shift ε x (hpos x hx)
  have hcont : ContinuousOn (fun x : ℝ => Real.log (x + ε)) (Set.uIcc 0 1) := by
    intro x hx
    have hx_pos : 0 < x + ε := hpos x hx
    have hd := hasDerivAt_xlog_shift ε x hx_pos
    -- log(x+ε) is continuous at x because it's the second factor. Use the chain via deriv.
    have hcont_log : ContinuousAt (fun y : ℝ => Real.log (y + ε)) x := by
      have h1 : ContinuousAt (fun y : ℝ => y + ε) x :=
        ((continuous_id.add continuous_const).continuousAt)
      have h2 : ContinuousAt Real.log (x + ε) :=
        Real.continuousAt_log hx_pos.ne'
      exact ContinuousAt.comp (g := Real.log) (f := fun y : ℝ => y + ε) h2 h1
    exact hcont_log.continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont.intervalIntegrable)]
  simp
  ring

snip end

/-- The main problem: `(1/n) ∑_{k=1}^n log(k/n + εₙ) → -1` whenever `εₙ > 0`
and `εₙ → 0`. -/
problem imc1997_p1
    (ε : ℕ → ℝ) (hpos : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => riemannLogShift n (ε n)) atTop (𝓝 (-1)) := by
  -- Sandwich argument. The full proof requires:
  -- (A) `riemannLog n → -1` (Riemann sum for ∫₀¹ log = -1).
  -- (B) For each fixed `δ > 0`, `riemannLogShift n δ → ∫₀¹ log(x + δ) dx
  --     = (1+δ) log(1+δ) - δ log δ - 1`.
  -- (C) The right-hand side `(1+δ) log(1+δ) - δ log δ - 1 → -1` as `δ → 0⁺`,
  --     using continuity of `(1+·) log(1+·)` and `tendsto_mul_log_nhds_zero_right`.
  -- (D) Sandwich: for `n` large enough that `ε n ≤ δ`,
  --       riemannLog n ≤ riemannLogShift n (ε n) ≤ riemannLogShift n δ,
  --     because `log` is monotone and `0 ≤ ε n ≤ δ`.
  --     (Note: in `riemannLog n`, the term at `k = 0` (i.e. `k+1 = 1`) is fine,
  --     but k/n = 1/n > 0, while in the shift version the ε n shift is positive,
  --     so log(k/n) is defined here for k ≥ 1.)
  -- We omit the full Mathlib-level Riemann-sum infrastructure and leave this as `sorry`.
  --
  -- TODO (concrete steps once Riemann-sum convergence is available):
  --   • Show `riemannLog n → -1`. The summand `log(k/n) = log k - log n` for k ≥ 1.
  --     Use Stirling-like asymptotics for `∑_{k=1}^n log k = log(n!)` ≈ `n log n - n`,
  --     so `(1/n) ∑ (log k - log n) ≈ (n log n - n)/n - log n = -1`.
  --     This is actually a *clean* approach in Mathlib, since `Stirling.log_factorial`
  --     or the summation `Finset.sum_range_id_mul_two` style identities give us
  --     `log(n!) - n log n + n → -1/2 log(2πn)` (Stirling), and dividing by n yields the limit.
  --   • Show `riemannLogShift n δ → ∫₀¹ log(x + δ) dx` for δ > 0 fixed: continuous
  --     Riemann sums, by `Continuous.tendsto_riemannSum` (TODO: confirm Mathlib name),
  --     or by uniform continuity of `log(· + δ)` on `[0,1]`.
  --   • Combine via the standard ε–δ sandwich.
  sorry

end Imc1997P1
