/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1997, Problem 7 (Day 2, Problem 1)

Let `f : ℝ → ℝ` be a `C^3` non-negative function with `f(0) = 0`,
`f'(0) = 0`, and `f''(0) > 0`. Define
    `g(x) = (√f(x) / f'(x))'`  for `x ≠ 0`,  `g(0) = 0`.
Prove that `g` is bounded in some neighbourhood of `0`.

(The original problem also asks: does this still hold if we only assume
`f ∈ C^2`? The answer is **no**: the function `f(x) = (x + |x|^{3/2})^2`
is a `C^2` counterexample with `g(x) → -∞` as `x → 0^+`. We do not formalize
this counterexample here.)

## Proof outline (official solution)

Let `c = f''(0)/2 > 0`. A direct computation gives
    `g(x) = ((f'(x))^2 - 2 f(x) f''(x)) / (2 (f'(x))^2 √(f(x)))`
for `x ≠ 0` (whenever `f'(x) ≠ 0` and `f(x) > 0`, which holds near `0`,
`x ≠ 0`, by Taylor expansion).

By the third-order Taylor expansion at `0`:
* `f(x) = c x^2 + O(x^3)`,
* `f'(x) = 2 c x + O(x^2)`,
* `f''(x) = 2 c + O(x)`,
hence
* `(f'(x))^2 = 4 c^2 x^2 + O(x^3)`,
* `2 f(x) f''(x) = 4 c^2 x^2 + O(x^3)`,
so the numerator `(f')^2 - 2 f f'' = O(x^3)`.

The denominator satisfies `2 (f'(x))^2 √(f(x)) ~ 8 c^{5/2} |x|^3`, so the
ratio is `O(1)`, i.e. `g` is bounded near `0`.

## Formalization notes

The formal statement uses:
* `ContDiff ℝ 3 f` for "`f` is `C^3`",
* `deriv f`, `deriv (deriv f)`, etc. for the derivatives,
* `Real.sqrt (f x) / deriv f x` for `√f / f'`,
* `deriv (fun y => Real.sqrt (f y) / deriv f y) x` for `g(x)`.

The full proof would proceed by:
1. Establishing third-order Taylor remainder bounds for `f`, `f'`, `f''`
   near `0` via `ContDiff.taylorWithinEval` / Peano's form of Taylor's
   theorem.
2. Using these to bound `(f')^2 - 2 f f'' = O(x^3)` and
   `2 (f')^2 √f ≥ 4 c^{5/2} |x|^3` (for `|x|` small enough).
3. Differentiating the quotient `√f / f'` to express `g` explicitly.

The proof is left as a `sorry` with the detailed roadmap above.
-/

namespace Imc1997P7

open scoped Topology
open Filter Real

/-- The function `g(x) = (√f(x) / f'(x))'` for `x ≠ 0`, `g(0) = 0`. -/
noncomputable def g (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else deriv (fun y => Real.sqrt (f y) / deriv f y) x

snip begin

/-- The pointwise identity for `g`: when `f` is differentiable at `x`,
`f x > 0`, `deriv f x ≠ 0`, then `g(x) = ((f'x)^2 - 2 f x f'' x) /
(2 (f' x)^2 sqrt (f x))` (assuming `f` has a second derivative at `x`).

This is the classical algebraic simplification of the quotient
`√f / f'`. We do not prove it here; it is a standard derivative
computation given the existence of `f''(x)` and the non-vanishing of
`f'(x)` and `f(x)`. -/
lemma g_eq_formula
    (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (x : ℝ) (hx : x ≠ 0)
    (hfx : 0 < f x) (hf'x : deriv f x ≠ 0) :
    g f x = ((deriv f x) ^ 2 - 2 * f x * deriv (deriv f) x) /
            (2 * (deriv f x) ^ 2 * Real.sqrt (f x)) := by
  -- TODO. The proof is a routine derivative computation:
  --   d/dx (√f / f') = (f'/(2√f) · f' - √f · f'') / (f')^2
  --                  = ((f')^2 - 2 f f'') / (2 (f')^2 √f).
  sorry

snip end

/-- The IMC 1997 Problem 7. Under the hypotheses:
* `f` is `C^3`,
* `f(x) ≥ 0` for all `x`,
* `f(0) = 0`,
* `f'(0) = 0`,
* `f''(0) > 0`,
the function `g` (as defined above) is bounded in a neighbourhood of `0`:
there is a `δ > 0` and an `M` such that `|g(x)| ≤ M` for all `x` with
`|x| < δ`. -/
problem imc1997_p7
    (f : ℝ → ℝ)
    (hf : ContDiff ℝ 3 f)
    (hnn : ∀ x, 0 ≤ f x)
    (hf0 : f 0 = 0)
    (hf'0 : deriv f 0 = 0)
    (hf''0 : 0 < deriv (deriv f) 0) :
    ∃ M : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x| < δ → |g f x| ≤ M := by
  -- HIGH-LEVEL ROADMAP (TODO).
  --
  -- Let `c = (deriv (deriv f) 0) / 2 > 0`.
  --
  -- Step 1.  Use the second-order Taylor expansion of `f` at `0`:
  --   `f(x) = c · x^2 + r(x)`  with `r(x) = o(x^2)`,
  -- and (since `f ∈ C^3`) the more precise statement
  --   `f(x) = c · x^2 + O(x^3)`.
  -- Likewise:
  --   `f'(x) = 2c · x + O(x^2)`,
  --   `f''(x) = 2c + O(x)`.
  -- Concretely: pick `δ₀ > 0` and constants `K_f, K_{f'}, K_{f''}` such that
  -- for `|x| < δ₀`,
  --   `|f(x) - c x^2|     ≤ K_f · |x|^3`,
  --   `|f'(x) - 2c x|     ≤ K_{f'} · x^2`,
  --   `|f''(x) - 2c|      ≤ K_{f''} · |x|`.
  -- The cleanest Mathlib hook is `ContDiff.taylorWithinEval` /
  -- `taylor_mean_remainder_lagrange`, applied at order 2 (for `f`) and at
  -- order 1 (for `f'` and `f''`).
  --
  -- Step 2.  Deduce, after possibly shrinking `δ₀`:
  --   `f(x) ≥ c x^2 / 2 > 0`  for `0 < |x| < δ₀`,
  --   `|f'(x)| ≥ c |x|`        for `0 < |x| < δ₀`,
  -- so in particular `f(x) > 0` and `f'(x) ≠ 0` away from `0`. This
  -- legitimizes the formula in `g_eq_formula`.
  --
  -- Step 3.  Estimate the numerator of the quotient form of `g`:
  --   `(f')^2 - 2 f · f''`
  --     = `(2c x + O(x^2))^2 - 2(c x^2 + O(x^3))(2c + O(x))`
  --     = `(4 c^2 x^2 + O(x^3)) - (4 c^2 x^2 + O(x^3))`
  --     = `O(x^3)`,
  -- i.e. there is a constant `C₁` and `δ₁ ∈ (0, δ₀]` such that
  --   `|(f'(x))^2 - 2 f(x) f''(x)| ≤ C₁ |x|^3`  for `|x| < δ₁`.
  --
  -- Step 4.  Estimate the denominator:
  --   `2 (f')^2 · √f ≥ 2 (c |x|)^2 · √(c x^2 / 2)`
  --                 `= 2 c^2 x^2 · |x| · √(c/2) = √2 · c^{5/2} · |x|^3`,
  -- so there is `C₂ > 0` with `|2 (f'(x))^2 √(f(x))| ≥ C₂ |x|^3`
  -- for `0 < |x| < δ₁` (after possibly shrinking `δ₁`).
  --
  -- Step 5.  Combining steps 3 and 4 with `g_eq_formula`:
  --   `|g(x)| ≤ C₁ / C₂`  for `0 < |x| < δ₁`,
  -- and `g(0) = 0` by definition. Hence `M := max (C₁ / C₂) 0` and
  -- `δ := δ₁` work.
  --
  -- All four steps are routine but Mathlib-heavy; the entire argument is
  -- left as a single `sorry` here.
  sorry

end Imc1997P7
