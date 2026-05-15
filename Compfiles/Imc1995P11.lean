/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1995, Problem 11 (Day 2 Problem 5)

(a) Prove that every function of the form
    `f(x) = a₀ / 2 + cos x + Σ_{n=2}^N a_n · cos (n x)`
with `|a₀| < 1` takes both positive and negative values on `[0, 2π)`.

(b) Prove that `F(x) = Σ_{n=1}^{100} cos (n^{3/2} · x)` has at least
    `40` zeros on the open interval `(0, 1000)`.

## Proof outline (official solution)

(a) Compute
  `∫₀^{2π} f(x) (1 ± cos x) dx = π (a₀ ± 1)`.
If `f ≥ 0` everywhere, the integral with `1 + cos x` (which is `≥ 0`) is
nonnegative, giving `a₀ + 1 ≥ 0` — and the integral with `1 - cos x` is
nonneg, giving `π (a₀ - 1) ≥ 0`, i.e. `a₀ ≥ 1`, contradicting `|a₀| < 1`.
Symmetrically, `f ≤ 0` everywhere forces `a₀ ≤ -1`. Hence `f` must take both
signs.

(b) We prove the stronger statement: for every integer `N`, every real
`h ≥ 24`, and every real `y`, the partial sum
  `F_N(x) = Σ_{n=1}^N cos (n^{3/2} x)`
changes sign on the interval `(y, y + h)`. Applying this with `h = 25` to
each of the disjoint intervals `(25k, 25(k+1))` for `k = 0, …, 39` (all
contained in `(0, 1000)`) yields at least 40 sign changes, hence at least
40 zeros.

To show `F_N` changes sign on `(y, y + h)`, suppose otherwise — so `F_N` has
constant sign on the interval. Consider
  `I₁ = ∫_y^{y+h} F_N(x) dx`, `I₂ = ∫_y^{y+h} F_N(x) cos x dx`.
If `F_N` keeps a single sign, `|I₂| ≤ |I₁|` (since `|cos x| ≤ 1`). We derive
the contradiction `|I₂| > |I₁|`.

Bound for `I₁`. Using `|∫_y^{y+h} cos(α x) dx| ≤ 2/|α|` for `α ≠ 0`,
  `|I₁| ≤ Σ_{n=1}^N 2 · n^{-3/2} ≤ 2 · (1 + ∫_1^∞ t^{-3/2} dt) = 6`.

Bound for `I₂`. Using the product-to-sum formula
  `cos(x · n^{3/2}) · cos x = (cos(x(n^{3/2} - 1)) + cos(x(n^{3/2} + 1))) / 2`,
the `n = 1` term contributes
  `∫_y^{y+h} cos²x dx = h/2 + (1/2) · ∫_y^{y+h} cos(2x) dx`,
whose error is bounded by `1/2`. For `n ≥ 2`:
  `|∫_y^{y+h} cos(x(n^{3/2} ± 1)) dx| ≤ 2/(n^{3/2} - 1)`,
and `n^{3/2} - 1 ≥ (2/3) n^{3/2}` for `n ≥ 3`. Hence
  `|I₂ - h/2| ≤ 1/2 + 2/(2√2 - 1) + 3 · ∫_2^∞ t^{-3/2} dt < 6`,
so `|I₂| > h/2 - 6`.

For `h ≥ 24`, `|I₂| > 6 ≥ |I₁|`, contradiction.

## Implementation notes

A complete formalization requires:

* Interval-integral manipulations involving `cos`, `sin`, and finite sums
  (sum/integral exchange, `integral_cos`, `integral_sin`).
* The product-to-sum identity for cosines.
* A version of the integral comparison test giving
  `Σ_{n=1}^N n^{-3/2} ≤ 1 + ∫_1^∞ t^{-3/2} dt`, then evaluating the
  improper integral to `2`.
* A continuous function `F_N` on a closed interval with a sign change has a
  zero (intermediate value theorem); 40 disjoint sub-intervals each with a
  sign change yield 40 distinct zeros, all in `(0, 1000)`.

These ingredients are all present in Mathlib but the bookkeeping is
extensive. The skeleton below records the statements with `sorry`.
-/

namespace Imc1995P11

open Real intervalIntegral MeasureTheory

/-- Part (a): A trigonometric polynomial with leading constant of magnitude
less than `1` and a `cos x` coefficient equal to `1` cannot keep a single
sign on `[0, 2π)`. -/
def PartA : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℝ), |a 0| < 1 →
    let f : ℝ → ℝ := fun x => a 0 / 2 + Real.cos x +
      ∑ n ∈ Finset.Icc 2 N, a n * Real.cos (n * x)
    (∃ x ∈ Set.Ico (0 : ℝ) (2 * π), 0 < f x) ∧
    (∃ x ∈ Set.Ico (0 : ℝ) (2 * π), f x < 0)

/-- Part (b): The function `F(x) = Σ_{n=1}^{100} cos(n^{3/2} · x)` has at least
`40` zeros on the open interval `(0, 1000)`. -/
noncomputable def F100 (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc (1 : ℕ) 100, Real.cos ((n : ℝ) ^ ((3 : ℝ) / 2) * x)

def PartB : Prop :=
  ∃ S : Finset ℝ, S.card ≥ 40 ∧ (∀ x ∈ S, x ∈ Set.Ioo (0 : ℝ) 1000 ∧ F100 x = 0)

/-- Combined statement of Problem 11. -/
problem imc1995_p11 : PartA ∧ PartB := by
  -- TODO: full proof.
  --
  -- Plan for part (a):
  --
  -- (1) Set `g(x) := 1 + cos x` and `h(x) := 1 - cos x`. Note `g, h ≥ 0` on ℝ.
  --
  -- (2) Compute
  --       `∫₀^{2π} f(x) · g(x) dx = π · (a₀ + 1)`,
  --       `∫₀^{2π} f(x) · h(x) dx = π · (a₀ - 1)`.
  --     Each summand `a_n cos(n x)` integrates to zero against `1`, against
  --     `cos x` (for `n ≠ 1`), and `∫₀^{2π} cos²x dx = π` handles the `n = 1`
  --     term. Use `intervalIntegral.integral_cos`,
  --     `intervalIntegral.integral_cos_sq` and orthogonality of distinct
  --     cosines on `[0, 2π]`.
  --
  -- (3) If `f x ≥ 0` for all `x ∈ [0, 2π)`, by continuity also on `[0, 2π]`.
  --     Then `∫ f · h ≥ 0` (product of nonneg integrable functions over an
  --     interval is nonneg), giving `a₀ ≥ 1` — contradicting `|a₀| < 1`.
  --     Hence `∃ x ∈ Ico 0 (2π), f x < 0`.
  --
  -- (4) Symmetrically, considering `∫ f · g ≥ 0` if `f ≤ 0` everywhere yields
  --     `a₀ ≤ -1`, contradiction; hence `∃ x ∈ Ico 0 (2π), 0 < f x`.
  --
  -- Plan for part (b):
  --
  -- (5) Auxiliary lemma: for every `N : ℕ` and every `y : ℝ` and every
  --     `h ≥ 24`, the function
  --       `F_N(x) := Σ_{n=1}^N cos(x · n^{3/2})`
  --     changes sign on `(y, y + h)`. Argued by contradiction as in the
  --     official solution sketched above:
  --       * if `F_N` has constant sign on `(y, y + h)` (equivalently on
  --         `[y, y + h]`, by continuity), then
  --         `|∫_y^{y+h} F_N(x) cos x dx| ≤ ∫_y^{y+h} |F_N(x)| dx
  --                                       = |∫_y^{y+h} F_N(x) dx|`.
  --       * Bound `|∫_y^{y+h} F_N(x) dx| ≤ 6` using
  --         `|∫_y^{y+h} cos(α x) dx| = |sin(α(y+h)) - sin(α y)|/|α| ≤ 2/|α|`
  --         and `Σ_{n=1}^N n^{-3/2} ≤ 1 + ∫_1^∞ t^{-3/2} dt = 1 + 2 = 3`.
  --       * Bound `|∫_y^{y+h} F_N(x) cos x dx - h/2| < 6` using the
  --         product-to-sum identity and the same `2/|α|` bounds for the
  --         oscillatory terms, plus the explicit `n = 1` term `cos²x`.
  --       * For `h ≥ 24`, the second integral has magnitude `> h/2 - 6 ≥ 6`,
  --         contradicting the first bound.
  --
  -- (6) By IVT, sign change on `(y, y + h)` with `F_N` continuous implies a
  --     zero of `F_N` in `(y, y + h)`.
  --
  -- (7) Apply (5) and (6) with `N = 100`, `h = 25`, and `y = 25 k` for
  --     `k = 0, 1, …, 39`. The intervals `(25 k, 25 (k + 1))` are pairwise
  --     disjoint and all contained in `(0, 1000)`. Pick a zero `x_k` from
  --     each, obtaining `40` distinct zeros of `F100` in `(0, 1000)`.
  sorry

end Imc1995P11
