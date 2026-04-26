/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1996, Problem 5 (Day 1)

(i) Let `a, b ∈ ℝ` with `b ≤ 0`, and assume `1 + a·x + b·x² ≥ 0` for all
    `x ∈ [0, 1]`. Prove
    `lim_{n → ∞} n · ∫_0^1 (1 + a x + b x²)^n dx
       = -1/a` if `a < 0`, and `= +∞` if `a ≥ 0`.

(ii) Let `f : [0, 1] → [0, ∞)` be a (continuous) function with `f''(x) ≤ 0`
     on `[0, 1]`. Suppose
     `L = lim_{n → ∞} n · ∫_0^1 f(x)^n dx`
     exists with `0 < L < ∞`. Prove that `f'` has constant sign on `[0, 1]`
     and `min_{[0,1]} |f'| = 1/L`.

## Proof outline (official solution)

### Part (i)

By a linear change of variable, reduce to showing: if `b ≤ 0`, `A > 0`,
`1 + a x + b x² > 0` on `[0, A]`, and `I_n = n · ∫_0^A (1+ax+bx²)^n dx`,
then `I_n → -1/a` (if `a < 0`) or `I_n → +∞` (if `a ≥ 0`).

For `a < 0`: define `f(x) = e^{ax} - (1 + ax + bx²)`. Then `f(0)=f'(0)=0`,
and `f''(x) = a² e^{ax} - 2b ≥ 0` (since `b ≤ 0`). So
`0 ≤ e^{ax} - (1+ax+bx²) ≤ c x²`, with `c = a²/2 - b ≥ 0`. By the mean
value theorem applied to `t ↦ t^n`,
`0 ≤ e^{a n x} - (1 + a x + b x²)^n ≤ c x² · n · e^{a (n-1) x}`.

Then
* `n · ∫_0^A e^{a n x} dx = (e^{a n A} - 1) / a → -1/a` since
  `e^{a n A} → 0` (as `a < 0`).
* `n² · ∫_0^A x² e^{a (n-1) x} dx → 0` (Laplace-type estimate).

So `I_n → -1/a`.

For `a ≥ 0`: pick `n` large so that `1/√(n+1) ≤ A` and `1 + b/(n+1) > 0`.
Then on `[0, 1/√(n+1)]`, `1 + ax + bx² ≥ 1 + bx² ≥ 1 + b/(n+1)`. Hence
`I_n ≥ n · (1/√(n+1)) · (1 + b/(n+1))^n → +∞`.

### Part (ii)

Let `M = max f`. Show `M = 1`.
* If `M < 1`, then `n · ∫_0^1 f^n ≤ n · M^n → 0`, contradicting `L > 0`.
* If `M > 1`, then `f > 1` on some interval `I` of positive length, so
  `n · ∫_I f^n → ∞`, contradicting `L < ∞`.

Show that the maximum is attained at an endpoint `x_0 ∈ {0, 1}`. If
instead `M` is attained at some `x_0 ∈ (0, 1)`, then `f'(x_0) = 0` and
`f(x_0) = 1`. Then `f(x_0 + h) ≥ 1 + (m/2) h²` near `x_0`, with
`m = min f''`. Choose `δ` small so `1 + δ²·m/2 > 0` and apply part (i) to
`a = 0, b = m/2`: `n · ∫_0^δ (1 + (m/2) h²)^n dh → +∞`, again a
contradiction.

So `M ∈ {f(0), f(1)}`. Case `M = f(0) = 1`: argue `f'(0) ≠ 0`
(otherwise the same interior-quadratic argument gives a contradiction).
Then `f` is decreasing, `f'(0) < 0`. For `h ∈ [0, 1]`,
`1 + h f'(0) ≥ f(h) ≥ 1 + h f'(0) + (m/2) h²`.

Choose `A < 1` with `1 + A f'(0) + (A²·m)/2 > 0`. By part (i) applied to
the lower and upper bounds,
`n · ∫_0^A (1 + h f'(0))^n dh → -1/f'(0)`,
`n · ∫_0^A (1 + h f'(0) + (m/2) h²)^n dh → -1/f'(0)`,
so by squeezing, `n · ∫_0^A f^n → -1/f'(0)`. Outside `[0, A]`,
`f(h) ≤ f(A) < 1`, so `n · ∫_A^1 f^n → 0`. Hence `L = -1/f'(0)`.

The case `M = f(1) = 1` is symmetric and gives `L = 1/f'(1)`.

Either way, `f'` has constant sign on `[0, 1]` (because `f` is monotone
under each branch — concavity rules out a sign change once we know `f` is
monotone on the interval `[0, x_0]` and `[x_0, 1]` with `x_0` an
endpoint), and `min |f'| = 1/L`. (`min |f'|` is attained at the endpoint
where `f` attains its maximum because `f''≤0` makes `|f'|` non-decreasing
away from the maximum.)

## Status

Statement-only formalization with `sorry` for both parts plus a few
auxiliary lemmas (positivity / non-emptiness facts and the
linear-bound inequality `1 + a x + b x² ≥ 1 + b x²` when `a ≥ 0` and
`x ≥ 0`).

This problem is genuinely hard to formalize: the standard solution
mixes Laplace-type asymptotic estimates with squeeze arguments via the
mean value theorem. A full Lean proof would require nontrivial lemmas
on `n · ∫_0^A e^{anx} dx` and `n² · ∫_0^A x² e^{a(n-1)x} dx`, plus the
concavity-driven monotonicity classification of part (ii).
-/

namespace Imc1996P5

open scoped Topology BigOperators
open MeasureTheory Filter

/-- The polynomial inside the integrand for part (i). -/
noncomputable def p (a b x : ℝ) : ℝ := 1 + a * x + b * x ^ 2

/-- Closed-form answer for part (i). When `a < 0` the limit is `-1/a`;
when `a ≥ 0` the limit is `+∞`, which we cannot return in `ℝ`. We use
the predicate-style statement below instead. -/
noncomputable def ansI (a : ℝ) : ℝ := -1 / a

snip begin

/-- For `a ≥ 0`, `b ≤ 0`, and `x ≥ 0`,
  `1 + a·x + b·x² ≥ 1 + b·x²`. -/
lemma poly_ge_quadratic {a b x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) :
    1 + b * x ^ 2 ≤ p a b x := by
  unfold p
  have : 0 ≤ a * x := mul_nonneg ha hx
  linarith

/-- `p a b 0 = 1`. -/
@[simp] lemma p_zero (a b : ℝ) : p a b 0 = 1 := by
  unfold p; ring

/-- For `b ≤ 0` and `x ≥ 0`, `b · x² ≤ 0`. -/
lemma b_xsq_nonpos {b x : ℝ} (hb : b ≤ 0) : b * x ^ 2 ≤ 0 := by
  have : 0 ≤ x ^ 2 := sq_nonneg x
  nlinarith

/-- For `a < 0`, `b ≤ 0`, the function `p a b` is `≤ 1 + a·x` on `x ≥ 0`,
i.e. dominated by its linear part. -/
lemma p_le_linear {a b x : ℝ} (hb : b ≤ 0) (_hx : 0 ≤ x) :
    p a b x ≤ 1 + a * x := by
  unfold p
  have := b_xsq_nonpos (b := b) (x := x) hb
  linarith

/-- For `a ≥ 0`, the linear part `1 + a x` is `≥ 1` on `x ≥ 0`. -/
lemma one_le_linear {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) :
    (1 : ℝ) ≤ 1 + a * x := by
  have : 0 ≤ a * x := mul_nonneg ha hx
  linarith

/-- The constant `c = a²/2 - b` from the proof outline is non-negative
when `b ≤ 0`. -/
lemma c_nonneg (a b : ℝ) (hb : b ≤ 0) : 0 ≤ a ^ 2 / 2 - b := by
  have h1 : 0 ≤ a ^ 2 := sq_nonneg a
  linarith

snip end

/-- Part (i), case `a < 0`. -/
problem imc1996_p5_part_i_neg
    (a b : ℝ) (ha : a < 0) (hb : b ≤ 0)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ p a b x) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) * ∫ x in (0 : ℝ)..1, (p a b x) ^ n)
      Filter.atTop (𝓝 (-1 / a)) := by
  -- TODO: full formalization. Outline:
  --
  -- Step 1. Reduce to bounding `(1 + ax + bx²)^n` between
  --   `e^{anx}` (sandwiched from above by `e^{a n x}` since
  --   `1 + ax + bx² ≤ e^{ax}` for `x ≥ 0` when `b ≤ 0`) and
  --   `e^{a n x} - c x² · n · e^{a (n-1) x}` (from below via the MVT
  --   applied to `t ↦ t^n` and the bound `e^{ax} - p a b x ≤ c x²`,
  --   `c = a²/2 - b`).
  --
  -- Step 2. Compute `n · ∫_0^1 e^{anx} dx = (e^{an} - 1)/a → -1/a`
  --   as `n → ∞` (using `Real.exp_neg_atTop` style limit since `a < 0`).
  --
  -- Step 3. Show `n² · ∫_0^1 x² e^{a(n-1)x} dx → 0`
  --   (the leading term is `2 n² / |a (n-1)|³ → 0`).
  --
  -- Step 4. Squeeze theorem.
  sorry

/-- Part (i), case `a ≥ 0`: the integrals diverge. -/
problem imc1996_p5_part_i_nonneg
    (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 0)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ p a b x) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) * ∫ x in (0 : ℝ)..1, (p a b x) ^ n)
      Filter.atTop Filter.atTop := by
  -- TODO: full formalization. Outline:
  --
  -- For `n` large enough that `1/√(n+1) ≤ 1` and `1 + b/(n+1) > 0`:
  --   on `[0, 1/√(n+1)]`, by `poly_ge_quadratic`, `p a b x ≥ 1 + bx²`,
  --   and since `x² ≤ 1/(n+1)`, we get `p a b x ≥ 1 + b/(n+1) > 0`.
  --   Hence
  --     ∫_0^{1/√(n+1)} (p a b x)^n dx ≥ (1/√(n+1)) · (1 + b/(n+1))^n.
  --   So
  --     n · ∫_0^1 (p a b x)^n dx ≥ (n/√(n+1)) · (1 + b/(n+1))^n.
  --
  -- The factor `(1 + b/(n+1))^n → e^b > 0` (since `b ≤ 0`),
  --   and `n/√(n+1) → ∞`, so the product `→ +∞`.
  sorry

/-- Part (ii): for nonneg concave continuous `f`, if `L = lim n ∫_0^1 f^n`
exists with `0 < L < ∞`, then `f'` has constant sign and `min |f'| = 1/L`.

We formalize the "constant sign" conclusion as: either `f' ≥ 0` everywhere
on `(0, 1)` or `f' ≤ 0` everywhere on `(0, 1)`. -/
problem imc1996_p5_part_ii
    (f : ℝ → ℝ)
    (f_cont : ContinuousOn f (Set.Icc 0 1))
    (f_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x)
    (f_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ f x)
    (f_second_nonpos : ∀ x ∈ Set.Ioo (0 : ℝ) 1, deriv (deriv f) x ≤ 0)
    (L : ℝ) (hL : 0 < L)
    (hLim : Filter.Tendsto
      (fun n : ℕ => (n : ℝ) * ∫ x in (0 : ℝ)..1, (f x) ^ n)
      Filter.atTop (𝓝 L)) :
    (∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ deriv f x) ∨
      (∀ x ∈ Set.Ioo (0 : ℝ) 1, deriv f x ≤ 0) := by
  -- TODO: full formalization. Outline:
  --
  -- Step 1 (M = max f equals 1).
  --   If max f < 1, then n · ∫_0^1 f^n ≤ n · (max f)^n → 0, contradicting L > 0.
  --   If max f > 1, then by continuity f > 1 on a sub-interval of positive
  --   length, giving n · ∫ f^n → ∞, contradicting L < ∞.
  --   So max f = 1.
  --
  -- Step 2 (the maximum is attained at an endpoint).
  --   Suppose f(x₀) = 1 with x₀ ∈ (0, 1). Then f'(x₀) = 0 and f(x₀ + h) ≥
  --   1 + (m/2) h² near x₀ with m = min f''. Apply part (i) at
  --   `a = 0, b = m/2`:
  --     n · ∫_0^δ (1 + (m/2) h²)^n dh → +∞,
  --   contradicting L < ∞.
  --
  -- Step 3 (monotonicity).
  --   So either f(0) = 1 (and f decreasing on [0, 1] by concavity + max
  --   at left endpoint) or f(1) = 1 (and f increasing). In each case,
  --   f' has constant sign.
  --
  -- For the simplified conclusion (constant-sign of f'), only Steps 1-3
  -- are needed.
  sorry

end Imc1996P5
