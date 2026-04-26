/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1997, Problem 5 (Day 1)

Let `ℝ₀ⁿ = { x ∈ ℝⁿ : ∑ xᵢ = 0 }`, and let `ℤ₀ⁿ` be its integer sublattice.
For `p ∈ [1, ∞)`, `‖x‖ₚ = (∑ |xᵢ|ᵖ)^{1/p}` is the usual `p`-norm.

(a) Prove: if `x ∈ ℝ₀ⁿ` satisfies `max xᵢ − min xᵢ ≤ 1`, then for every
    `y ∈ ℤ₀ⁿ` and every `p ∈ [1, ∞)`,
        `‖x‖ₚ ≤ ‖x + y‖ₚ`.

(b) Show that the inequality in (a) can fail when `0 < p < 1`.

## Proof outline (official solution)

**(a)** WLOG `x ≠ 0`, so by the constraint `‖x‖_∞ < 1`. The crucial geometric
fact is: for every coordinate `j`, `xⱼ ≤ 0` implies `max_i xᵢ ≤ xⱼ + 1`, and
`xⱼ ≥ 0` implies `min_i xᵢ ≥ xⱼ − 1`.

Partition the indices `{1, …, n}` according to the signs of `xᵢ` and `yᵢ`:
let `I(s, t)` for `s, t ∈ {+, −, 0}` be the set of `i` with `sign yᵢ = s` and
`sign xᵢ = t`. Note `I(0, ·)` contributes `|xᵢ + yᵢ|ᵖ = |xᵢ|ᵖ` so can be
ignored.

If either `I(+, +)` or `I(−, −)` is nonempty, then `‖x + y‖_∞ ≥ 1 > ‖x‖_∞`,
which (combined with the support / dimension argument) implies
`‖x + y‖ₚ ≥ ‖x‖ₚ`.

Otherwise, only the "opposite-sign" sets `I(+, −)` and `I(−, +)` contribute.
Using the geometric inequalities above and convexity (`|x+y|ᵖ ≥ |y| − 1 + |x|ᵖ`
on these sets), one obtains
        `‖x + y‖ₚᵖ − ‖x‖ₚᵖ ≥ ∑ |yᵢ| − 2 · min(|I(+,−)|, |I(−,+)|) ≥ 0`,
where the last inequality uses the lattice condition `∑ yᵢ = 0` to rewrite
`∑|yᵢ| = 2 · ∑_{I(+,−)} yⱼ + 2 · ∑_{I(+,+)} yⱼ`.

**(b)** For `p ∈ (0, 1)`, choose a rational `t ∈ (1/2, 1)` of the form
`t = l/(m+l)` with `m, l` positive integers (so `m·t = l·(1−t)`), and set
`n = m + l`. Define
    `xᵢ = t` for `i ≤ m`, `xᵢ = t − 1` for `i > m`,
    `yᵢ = −1` for `i ≤ m`, `y_{m+1} = m`, `yᵢ = 0` otherwise.
Then `∑ xᵢ = m·t + l·(t−1) = m·t − l·(1−t) = 0`, and `∑ yᵢ = −m + m = 0`.
A computation gives
    `‖x‖ₚᵖ − ‖x + y‖ₚᵖ = m·(tᵖ − (1−t)ᵖ) + (1−t)ᵖ − (m − 1 + t)ᵖ`,
which is positive for sufficiently large `m` (the `m·(tᵖ − (1−t)ᵖ)` term
dominates the sublinearly growing `(m − 1 + t)ᵖ`).

## Formalization notes

This file states (a) for `p ∈ [1, ∞)` (the case `p = ∞` is handled by a
limiting argument and is omitted here for technical brevity). The proof
requires a substantial case split with sign partitions, plus a discrete
convexity inequality `|a + b|ᵖ ≥ |b| − 1 + |a|ᵖ` valid when `|a| ≤ 1` and
`|b| ≥ 1` of the appropriate sign — see the official solution above.
The full Lean proof is left as a `sorry` with a detailed roadmap.
-/

namespace Imc1997P5

open scoped BigOperators
open Finset Real

/-- The `p`-th power of the `p`-norm of a tuple `x : Fin n → ℝ`, expressed
without taking the `1/p`-th root. This is convenient because monotonicity of
`t ↦ t^(1/p)` on `[0, ∞)` shows `‖x‖ₚ ≤ ‖y‖ₚ` is equivalent (for `p ≥ 1`) to
`∑ |xᵢ|ᵖ ≤ ∑ |yᵢ|ᵖ`. -/
noncomputable def pNormPow {n : ℕ} (p : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, |x i| ^ p

/-- Real-valued `p`-norm of a tuple, `(∑ |xᵢ|ᵖ)^{1/p}`. -/
noncomputable def pNorm {n : ℕ} (p : ℝ) (x : Fin n → ℝ) : ℝ :=
  (pNormPow p x) ^ (1 / p)

/-- The main problem (part (a)): if `x : Fin n → ℝ` has zero sum and the
constraint `max - min ≤ 1`, and `y : Fin n → ℤ` has zero sum, then the
`p`-norm increases under the perturbation. Stated as `pNormPow ≤ pNormPow`
for `p ∈ [1, ∞)`. -/
problem imc1997_p5 (n : ℕ) (p : ℝ) (hp : 1 ≤ p)
    (x : Fin n → ℝ) (hxsum : ∑ i, x i = 0)
    (hxbound : ∀ i j, x i - x j ≤ 1)
    (y : Fin n → ℤ) (hysum : ∑ i, y i = 0) :
    pNormPow p x ≤ pNormPow p (fun i => x i + (y i : ℝ)) := by
  -- HIGH-LEVEL GLUE (TODO).
  --
  -- The proof follows the official solution outline above. Concretely:
  --
  -- Step 1. Reduce to `x ≠ 0`. If `x = 0`, both sides reduce to `∑ |yᵢ|ᵖ ≥ 0`.
  --
  -- Step 2. Show `‖x‖_∞ < 1` (as long as `x ≠ 0`): from `∑ xᵢ = 0` and
  --   `max xᵢ - min xᵢ ≤ 1`, if `max xᵢ ≥ 1` then `min xᵢ ≥ 0`, so all `xᵢ ≥ 0`
  --   forcing all `xᵢ = 0` (by zero sum), contradiction.
  --
  -- Step 3. Geometric inequalities: for any `j`,
  --     `xⱼ ≤ 0 → max_i xᵢ ≤ xⱼ + 1`,
  --     `xⱼ ≥ 0 → min_i xᵢ ≥ xⱼ - 1`.
  --   These follow directly from `max - min ≤ 1` and `min ≤ xⱼ ≤ max`.
  --
  -- Step 4. Sign partition: define
  --     `I_pp = {i : yᵢ > 0 ∧ xᵢ > 0}`, `I_pm = {i : yᵢ > 0 ∧ xᵢ ≤ 0}`,
  --     `I_mp = {i : yᵢ < 0 ∧ xᵢ ≥ 0}`, `I_mm = {i : yᵢ < 0 ∧ xᵢ < 0}`,
  --     `I_0 = {i : yᵢ = 0}` (whose contribution cancels).
  --
  -- Step 5. Case A: `I_pp ≠ ∅` or `I_mm ≠ ∅`. Then there is `i` with
  --   `yᵢ ≥ 1` and `xᵢ > 0` (or symmetric), so `|xᵢ + yᵢ| ≥ 1 + xᵢ > 1`.
  --   Combined with `‖x‖_∞ < 1`, conclude
  --     `pNormPow p (x+y) ≥ |xᵢ + yᵢ|ᵖ ≥ 1 ≥ ‖x‖_∞ᵖ · n ≥ ∑ |xᵢ|ᵖ · ?`.
  --   (The argument requires more care to get the inequality from the
  --   single dominant index; the cleanest route is the convexity inequality
  --   `|xᵢ + yᵢ|ᵖ ≥ |yᵢ| - 1 + |xᵢ|ᵖ` valid on the populated sets.)
  --
  -- Step 6. Case B: `I_pp = ∅` and `I_mm = ∅`. Then yᵢ and xᵢ have
  --   opposite signs whenever yᵢ ≠ 0. The convexity inequality
  --     `|a + b|ᵖ ≥ |b| - 1 + |a|ᵖ`   (when `|a| ≤ 1`, `|b| ≥ 1`, opp. signs)
  --   applied on `I_pm ∪ I_mp` plus the geometric inequalities (Step 3)
  --   yield, after WLOG-ing |I_pm| ≥ |I_mp|,
  --     `pNormPow p (x+y) - pNormPow p x ≥ ∑_{I_pm ∪ I_mp} |yᵢ| - 2|I_pm|`.
  --   Using `∑ yᵢ = 0`, this rewrites as
  --     `2 ∑_{I_pm}(yⱼ - 1) + 2 ∑_{I_pp} yⱼ ≥ 0`,
  --   each summand nonnegative.
  --
  -- The convexity lemma `|a + b|ᵖ ≥ |b| - 1 + |a|ᵖ` is the technical heart;
  -- it follows from the (forward) Bernoulli inequality
  --     `(1 + t)ᵖ ≥ 1 + p·t`   for `t ≥ -1`, `p ≥ 1`,
  -- specialized to `t = -|a|/|b|` (when `|b| ≥ 1`), giving
  --     `||b| - |a||ᵖ = |b|ᵖ · (1 - |a|/|b|)ᵖ ≥ |b|ᵖ - p·|b|^{p-1}·|a|`,
  -- and then comparing with `|b| - 1 + |a|ᵖ` using `|a| ≤ 1`.
  -- (Alternatively: `f(t) = |b - t|ᵖ - (|b| - t + tᵖ)` is `≥ 0` on `[0, 1]`
  -- by checking endpoints and the convexity of `|b - t|ᵖ`.)
  sorry

/-- Part (b): for `p ∈ (0, 1)`, the inequality from (a) can fail. Concretely,
there exist `n`, a zero-sum `x : Fin n → ℝ` with `max - min ≤ 1`, and a
zero-sum `y : Fin n → ℤ` with `pNormPow p (x + y) < pNormPow p x`. -/
problem imc1997_p5_part_b (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ (n : ℕ) (x : Fin n → ℝ) (y : Fin n → ℤ),
      (∑ i, x i = 0) ∧ (∀ i j, x i - x j ≤ 1) ∧ (∑ i, y i = 0) ∧
      pNormPow p (fun i => x i + (y i : ℝ)) < pNormPow p x := by
  -- TODO. Use the explicit construction from the official solution:
  --   pick rational t ∈ (1/2, 1) with m·t = l·(1−t), m, l positive integers,
  --   n = m + l, x, y as in the solution sketch above. Then compute
  --     pNormPow p x − pNormPow p (x+y)
  --       = m·(tᵖ − (1−t)ᵖ) + (1−t)ᵖ − (m − 1 + t)ᵖ.
  --   For 0 < p < 1, (m − 1 + t)ᵖ grows like m^p, while m·(tᵖ − (1−t)ᵖ)
  --   grows linearly in m (and t > 1/2 makes the coefficient positive),
  --   so the expression is positive for m large enough.
  sorry

end Imc1997P5
