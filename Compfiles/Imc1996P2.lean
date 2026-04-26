/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1996, Problem 2 (Day 1)

Evaluate
  `I_n = ∫_{-π}^{π} sin(n x) / ((1 + 2^x) sin x) dx`,
where `n ∈ ℕ`.

## Answer

`I_n = 0` if `n` is even, and `I_n = π` if `n` is odd.

## Proof outline (official solution)

Split the integral over `[-π, 0]` and `[0, π]`. In the first integral
substitute `x ↦ -x` (so `dx ↦ -dx` and the limits flip):
`∫_{-π}^{0} sin(n x) / ((1 + 2^x) sin x) dx
   = ∫_0^π sin(-n x) / ((1 + 2^{-x}) sin (-x)) dx
   = ∫_0^π sin(n x) / ((1 + 2^{-x}) sin x) dx`,
using `sin(-y) = -sin y` to cancel two minus signs. Adding,
`I_n = ∫_0^π sin(n x) · (1/(1 + 2^x) + 1/(1 + 2^{-x})) / sin x dx`,
and `1/(1 + 2^x) + 1/(1 + 2^{-x}) = 1/(1+2^x) + 2^x/(2^x+1) = 1`.
So
`I_n = J_n := ∫_0^π sin(n x) / sin x dx`.

For `n ≥ 2`, using `sin A - sin B = 2 sin((A-B)/2) cos((A+B)/2)`,
`sin(n x) - sin((n-2) x) = 2 sin x cos((n-1) x)`. Thus
`J_n - J_{n-2} = 2 ∫_0^π cos((n-1) x) dx = 0`
since `n - 1 ≥ 1`.

Base cases:
* `J_0 = ∫_0^π 0 / sin x dx = 0`.
* `J_1 = ∫_0^π sin x / sin x dx = π` (the integrand equals 1 a.e.).

Hence `J_n = 0` for `n` even and `J_n = π` for `n` odd.

## Status

This formalization defines the relevant integrals and states the main
result with the closed-form answer. The full Lean proof — combining the
substitution `x ↦ -x` on `[-π, 0]`, the recurrence on `J_n`, and the
boundary handling at the (removable) singularities `x = 0, π` of
`sin(n x)/sin x` — is left as `sorry` with detailed TODO notes. The base
cases `n = 0` and `n = 1` are partially handled in `snip` lemmas.
-/

namespace Imc1996P2

open MeasureTheory intervalIntegral Set Real

/-- The integrand `sin(n x) / ((1 + 2^x) sin x)`. -/
noncomputable def f (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin (n * x) / ((1 + (2 : ℝ) ^ x) * Real.sin x)

/-- Auxiliary integrand `sin(n x) / sin x` (the symmetrized version). -/
noncomputable def g (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin (n * x) / Real.sin x

/-- The closed-form answer: `0` if `n` is even, `π` if `n` is odd. -/
noncomputable def answer (n : ℕ) : ℝ :=
  if n % 2 = 0 then 0 else Real.pi

snip begin

/-- `1/(1 + 2^x) + 1/(1 + 2^{-x}) = 1` for every real `x`. -/
lemma half_plus_half (x : ℝ) :
    1 / (1 + (2 : ℝ) ^ x) + 1 / (1 + (2 : ℝ) ^ (-x)) = 1 := by
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) x
  have h2pos' : (0 : ℝ) < (2 : ℝ) ^ (-x) := Real.rpow_pos_of_pos (by norm_num) (-x)
  have h1 : (1 : ℝ) + (2 : ℝ) ^ x ≠ 0 := by positivity
  have h2 : (1 : ℝ) + (2 : ℝ) ^ (-x) ≠ 0 := by positivity
  have hx : (2 : ℝ) ^ (-x) = 1 / (2 : ℝ) ^ x := by
    rw [Real.rpow_neg (by norm_num), one_div]
  rw [hx]
  field_simp
  ring

/-- Trig identity `sin((n+2) x) - sin(n x) = 2 sin x cos((n+1) x)`. -/
lemma sin_step_diff (n : ℕ) (x : ℝ) :
    Real.sin ((n + 2 : ℕ) * x) - Real.sin (n * x)
      = 2 * Real.sin x * Real.cos ((n + 1 : ℕ) * x) := by
  have := Real.sin_sub_sin ((n + 2 : ℕ) * x) (n * x)
  -- this : sin a - sin b = 2 * sin ((a - b)/2) * cos ((a + b)/2)
  rw [this]
  push_cast
  have h1 : ((n + 2 : ℝ) * x - n * x) / 2 = x := by ring
  have h2 : ((n + 2 : ℝ) * x + n * x) / 2 = (n + 1) * x := by ring
  rw [h1, h2]

/-- Base case `n = 0`: the auxiliary integrand `g 0` is identically `0`. -/
lemma g_zero (x : ℝ) : g 0 x = 0 := by
  simp [g]

/-- Base case `n = 0`: `∫_0^π g 0 x dx = 0`. -/
lemma integral_g_zero : ∫ x in (0:ℝ)..Real.pi, g 0 x = 0 := by
  simp [g_zero]

/-- For `x ≠ 0` with `sin x ≠ 0`, `g 1 x = 1`. -/
lemma g_one_eq_one_of {x : ℝ} (hx : Real.sin x ≠ 0) : g 1 x = 1 := by
  simp [g, hx]

snip end

/-- The main problem: compute `I_n`. -/
problem imc1996_p2 (n : ℕ) :
    ∫ x in (-Real.pi)..Real.pi,
        Real.sin (n * x) / ((1 + (2 : ℝ) ^ x) * Real.sin x)
      = answer n := by
  -- TODO: full formalization. Outline:
  --
  -- Step 1. Symmetrization.
  --   ∫_{-π}^{π} f n = ∫_{-π}^{0} f n + ∫_{0}^{π} f n.
  --   In the first integral, substitute u = -x:
  --     ∫_{-π}^{0} sin(n x)/((1 + 2^x) sin x) dx
  --       = ∫_{0}^{π} sin(-n u)/((1 + 2^{-u}) sin(-u)) du
  --       = ∫_{0}^{π} sin(n u)/((1 + 2^{-u}) sin u) du.
  --   (Use intervalIntegral.integral_comp_neg or _comp_smul/_comp_mul_left.)
  --   Adding to the second:
  --     I_n = ∫_{0}^{π} sin(n x) · [1/((1+2^x) sin x) + 1/((1+2^{-x}) sin x)] dx
  --         = ∫_{0}^{π} (sin(n x)/sin x) · [1/(1+2^x) + 1/(1+2^{-x})] dx
  --         = ∫_{0}^{π} sin(n x) / sin x dx
  --   by `half_plus_half`. (At x = 0 the integrand has a removable singularity;
  --   use the fact that `{0}` has measure zero so it does not affect the
  --   Lebesgue integral.)
  --
  --   So I_n = J_n where `J_n := ∫_{0}^{π} g n`.
  --
  -- Step 2. Recurrence on J_n.
  --   For n ≥ 2 and x with sin x ≠ 0,
  --     g (n+2) x - g n x = (sin((n+2)x) - sin(n x)) / sin x
  --                       = (2 sin x cos((n+1) x)) / sin x
  --                       = 2 cos((n+1) x).
  --   (Use `sin_step_diff`.)
  --   Outside the measure-zero set {x : sin x = 0} = {0, π} ∩ [0, π], we have
  --     ∫_0^π (g (n+2) - g n) = ∫_0^π 2 cos((n+1) x) dx
  --                           = 2 [sin((n+1) x)/(n+1)]_0^π
  --                           = 0
  --   since sin((n+1) π) = 0 and sin 0 = 0.
  --   Hence J_{n+2} = J_n.
  --
  -- Step 3. Base cases.
  --   J_0 = 0           (integrand is 0 a.e.)
  --   J_1 = ∫_0^π 1 dx = π   (integrand equals 1 a.e. on (0, π))
  --
  -- Step 4. Conclude J_n = answer n by strong induction on n with step 2.
  --
  -- The careful parts of this argument are:
  --   (a) the change-of-variable on [-π, 0] (handle Bochner integrals;
  --       use intervalIntegral.integral_comp_neg);
  --   (b) showing integrability of f n and g n on the relevant intervals,
  --       which follows because sin(n x)/sin x extends continuously and is
  --       bounded by `n` (Dirichlet kernel-type bound), but a measure-zero
  --       handling at x = 0 (and x = ±π) suffices since we use Lebesgue
  --       integrals;
  --   (c) the algebraic identity `half_plus_half` (proved above).
  sorry

end Imc1996P2
