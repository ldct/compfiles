/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Inequality] }

/-!
# International Mathematical Competition 1999, Problem 6 (Day 1)

(a) For each real `p` with `1 < p < ∞`, find a finite constant `c_p` with the
    following property: for every `f ∈ C¹[-1, 1]` with `f(1) > f(-1)` and
    `|f'(x)| ≤ 1` for all `x ∈ [-1, 1]`, there exists `x ∈ [-1, 1]` with
    `f'(x) > 0` and `|f(y) - f(x)| ≤ c_p · (f'(x))^{1/p} · |y - x|` for all
    `y ∈ [-1, 1]`.

(b) Does such a constant `c_1` exist for `p = 1`?

## Answer

(a) `c_p = 6 p / (p - 1)` works.

(b) No: there is no finite constant that works for `p = 1`.

## Proof outline (official solution)

**Part (a).** Let `g(x) := max(0, f'(x))` (the positive part of `f'`). Then
`f(1) - f(-1) = ∫_{-1}^{1} f' = ∫ g - ∫ (-f' on the negative part) ≤ 2 ∫ g`
(more precisely, `2 ∫ g ≥ ∫ |f'|`).

Suppose for contradiction the conclusion fails for the constant `c = c_p`.
Then for every `x ∈ [-1,1]` with `g(x) = f'(x) > 0`, there exists
`y ∈ [-1, 1]` with `|f(y) - f(x)| > c · g(x)^{1/p} · |y - x|`.

Fix `t > 0` and consider the level set `E_t := { x ∈ [-1,1] | g(x) > t }`.
For each `x ∈ E_t`, pick an interval `I_x` (with one endpoint at `x`) on
which the failure occurs. By the Vitali covering lemma applied to the
collection `{I_x}_{x ∈ E_t}`, there is a disjoint subcollection
`{I_{x_i}}` covering at least `1/3` of `|E_t|`. Each chosen interval
satisfies `|f(I_{x_i})| ≥ c · t^{1/p} · |I_{x_i}|`. Summing,
  `c · t^{1/p} · ∑|I_{x_i}| ≤ ∑|f(I_{x_i})| ≤ 2 ∫ g`,
so `|E_t| ≤ 3 · ∑|I_{x_i}| ≤ (6/c) · t^{-1/p} · ∫ g`.

Integrating in `t` from `0` to `1` (using `|f'| ≤ 1` so `g ≤ 1`):
  `∫ g = ∫_0^1 |E_t| dt ≤ (6/c) · (∫ g) · ∫_0^1 t^{-1/p} dt`
       `= (6/c) · (p/(p-1)) · ∫ g`.

Since `∫ g > 0` (because `f(1) > f(-1)`), we get `1 ≤ (6/c) · p/(p-1)`,
contradicting `c = 6p/(p-1) + 1` (or any `c > 6p/(p-1)`). Thus
`c_p = 6p/(p-1)` works (with strict inequality, or any `c > 6p/(p-1)`).

**Part (b).** No constant works for `p = 1`. Given `c > 1`, set `α := 1/c`.
Choose `0 < ε < 1` so small that `((1+ε)/(2ε))^{-α} < 1/4`. Choose an even
continuous `g : [-1,1] → ℝ` with `g(x) = -1` for `|x| ≤ ε`,
`0 ≤ g(x) < α · ((|x| + ε)/(2ε))^{-α-1}` for `ε < |x| ≤ 1`, with
`∫_ε^1 g > ε`. Let `f(x) := ∫_{-1}^x g`. Then `f(1) - f(-1) > 0` and
`|f'| ≤ 1`. For `x ∈ (ε, 1]` and `y = -ε`,
  `|f(x) - f(y)| ≥ 2 ε · ((x + ε)/(2ε))^{-α} > g(x) · (x - y) / α
   = f'(x) · |x - y| / α = c · f'(x)^{1/1} · |x - y|`,
so the required inequality fails.

## Status of this formalization

Both `determine` answers (the constant `c_p` and the Boolean answer to
part (b)) are filled in. Both proof bodies are `sorry` placeholders with
TODO outlines. The proofs require the Vitali covering lemma applied to
the level sets of `f'`, Cavalieri's principle (`∫ g = ∫ |{g > t}| dt`),
and a delicate counterexample construction for part (b).
-/

namespace Imc1999P6

open scoped BigOperators
open MeasureTheory Set

/-- Answer to part (a): the smallest (in fact, sharp up to a constant)
admissible value is `c_p = 6 p / (p - 1)`. We pose any value strictly
greater than this; the canonical choice is `6p/(p-1) + 1`. -/
noncomputable determine c_p (p : ℝ) : ℝ := 6 * p / (p - 1) + 1

/-- Answer to part (b): a constant `c_1` does NOT exist. -/
determine c_one_exists : Prop := False

/-- **IMC 1999 Problem 6 (a).**
For each real `p > 1`, the constant `c_p` (defined above) satisfies the
required property: for every `f ∈ C¹[-1, 1]` with `f(1) > f(-1)` and
`|f'| ≤ 1`, there is `x ∈ [-1, 1]` with `f'(x) > 0` and
`|f(y) - f(x)| ≤ c_p · (f'(x))^{1/p} · |y - x|` for all `y ∈ [-1, 1]`. -/
problem imc1999_p6_part_a (p : ℝ) (hp : 1 < p) (f : ℝ → ℝ)
    (hf_diff : ContDiffOn ℝ 1 f (Set.Icc (-1 : ℝ) 1))
    (hf_endpts : f (-1) < f 1)
    (hf_deriv_bd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ f' : ℝ,
      HasDerivWithinAt f f' (Set.Icc (-1 : ℝ) 1) x → |f'| ≤ 1) :
    ∃ x ∈ Set.Icc (-1 : ℝ) 1, ∃ fx' : ℝ,
      HasDerivWithinAt f fx' (Set.Icc (-1 : ℝ) 1) x ∧
      0 < fx' ∧
      ∀ y ∈ Set.Icc (-1 : ℝ) 1,
        |f y - f x| ≤ c_p p * fx' ^ (1 / p) * |y - x| := by
  -- TODO: full proof.
  --
  -- Sketch of the official solution:
  --   1. Define `g(x) := max(0, f'(x))`. Then `g` is continuous on `[-1,1]`
  --      and `f(1) - f(-1) = ∫_{-1}^{1} f' ≤ 2 ∫ g` (since
  --      `|f'| ≤ |f'|⁺ + |f'|⁻ = g + (g - f') = 2g - f'`, so
  --      `∫ |f'| ≤ 2 ∫ g - (f(1) - f(-1)) ≤ 2 ∫ g`).
  --   2. Argue by contradiction: suppose for `c := c_p` no valid `x` exists.
  --   3. For each `t > 0` and each `x ∈ E_t := {x ∈ [-1,1] | g(x) > t}`,
  --      pick `y_x ∈ [-1, 1]` with
  --      `|f(y_x) - f(x)| > c · t^{1/p} · |y_x - x|`. Let
  --      `I_x := [min(x, y_x), max(x, y_x)]`.
  --   4. Vitali covering: extract a countable disjoint subcollection
  --      `{I_{x_i}}` whose total measure is at least `(1/3) μ(E_t)`. (Use
  --      `Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall`
  --      or `Vitali.exists_disjoint_covering_ae` from Mathlib.)
  --   5. On each `I_{x_i}`, `|f(y_{x_i}) - f(x_i)| = |∫_{I_{x_i}} f'|
  --      ≤ ∫_{I_{x_i}} 2 g`, so summing,
  --      `c · t^{1/p} · ∑ |I_{x_i}| ≤ 2 ∫ g`.
  --      Hence `μ(E_t) ≤ 3 ∑ |I_{x_i}| ≤ (6/c) · t^{-1/p} · ∫ g`.
  --   6. Cavalieri: `∫ g = ∫_0^∞ μ({g > t}) dt = ∫_0^1 μ(E_t) dt` (using
  --      `g ≤ 1`). Plug in the bound:
  --      `∫ g ≤ (6/c) · (∫ g) · ∫_0^1 t^{-1/p} dt
  --           = (6/c) · (p/(p-1)) · ∫ g`.
  --   7. Since `∫ g > 0` (from step 1 + `f(-1) < f(1)`), divide by `∫ g`:
  --      `1 ≤ (6/c) · p/(p-1)`, i.e. `c ≤ 6p/(p-1)`. With `c := c_p :=
  --      6p/(p-1) + 1` this is a contradiction.
  --
  -- Mathlib references:
  --   * `MeasureTheory.lintegral_eq_lintegral_meas_lt` for Cavalieri.
  --   * `Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall`
  --     or the 1D specialisation for the covering step.
  --   * `intervalIntegral.integral_eq_sub_of_hasDerivAt` for FTC.
  --   * `Real.rpow_natCast`/`Real.rpow_one_div_le_iff` for the
  --     `t^{1/p}` rearrangements.
  sorry

/-- **IMC 1999 Problem 6 (b).**
For `p = 1` no finite constant works: for every `c < ∞` there is a
counterexample `f`. -/
problem imc1999_p6_part_b :
    c_one_exists ↔
      ∃ c : ℝ, ∀ f : ℝ → ℝ,
        ContDiffOn ℝ 1 f (Set.Icc (-1 : ℝ) 1) →
        f (-1) < f 1 →
        (∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ f' : ℝ,
          HasDerivWithinAt f f' (Set.Icc (-1 : ℝ) 1) x → |f'| ≤ 1) →
        ∃ x ∈ Set.Icc (-1 : ℝ) 1, ∃ fx' : ℝ,
          HasDerivWithinAt f fx' (Set.Icc (-1 : ℝ) 1) x ∧
          0 < fx' ∧
          ∀ y ∈ Set.Icc (-1 : ℝ) 1,
            |f y - f x| ≤ c * fx' * |y - x| := by
  -- TODO: full proof. The answer is `False`, so we must show the right
  -- side is also `False`, i.e., for every `c` we exhibit a
  -- counterexample.
  --
  -- Sketch (official solution): given any `c > 0`, set `α := 1/c` (WLOG
  -- `c > 1` so `α < 1`). Pick `0 < ε < 1` with
  -- `((1 + ε)/(2 ε))^{-α} < 1/4`.
  --
  -- Construct a continuous even `g : [-1,1] → ℝ` with
  --   * `g(x) = -1` for `|x| ≤ ε`,
  --   * `0 ≤ g(x) < α · ((|x| + ε)/(2ε))^{-α-1}` for `ε < |x| ≤ 1`,
  --   * `∫_ε^1 g > ε`.
  -- (Such `g` is built by smoothing a piecewise affine bump; the precise
  -- choice involves an explicit interpolation between the two regimes.)
  --
  -- Set `f(x) := ∫_{-1}^x g`. Then `f ∈ C¹`, `|f'| = |g| ≤ 1`,
  -- `f(1) - f(-1) > 0` (positive over (ε,1] outweighs the `-1` slab over
  -- `[-ε, ε]`).
  --
  -- For any candidate `x ∈ (-1,1)` with `f'(x) > 0`, necessarily
  -- `|x| > ε`. Pick `y` of opposite sign with `|y| = ε`. By construction
  -- `|f(x) - f(y)| ≥ 2ε · ((|x| + ε)/(2ε))^{-α} > (g(x)/α) · |x - y|
  -- = (1/α) · f'(x) · |x - y| = c · f'(x) · |x - y|`,
  -- so the inequality fails.
  --
  -- Steps:
  --   1. `c_one_exists = False` so the LHS is `False`. The iff becomes
  --      `False ↔ ¬(∃ c, …)`, i.e., we must show
  --      `∀ c, ∃ f, …(counterexample)`.
  --   2. Use the construction above. Producing a `C¹` `g` with the
  --      stated properties is the bulk of the work; the algebraic
  --      contradiction is straightforward arithmetic.
  show False ↔ _
  constructor
  · intro h
    exact False.elim h
  · intro ⟨c, hc⟩
    -- Construct counterexample for this c. (TODO)
    sorry

end Imc1999P6
