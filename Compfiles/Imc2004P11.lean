/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2004, Problem 11
(IMC 2004, Day 2, Problem 5)

Prove that
  `∫₀¹ ∫₀¹ dx dy / (1/x + |log y| - 1) ≤ 1`.
-/

namespace Imc2004P11

open Real MeasureTheory

snip begin

/-
Solution outline.

Claim: `1/x - 1 ≥ |log x|` on `(0, 1]`.  Equivalently, `1/x ≥ 1 - log x`.
Setting `u = -log x ≥ 0`, this is `e^u ≥ 1 + u`, which holds for all real `u`.

On `(0, 1) × (0, 1)`, we therefore have
  `1/x + |log y| - 1 ≥ |log x| + |log y| = -log x - log y = -log(xy) > 0`,
so the integrand is bounded above pointwise by `1 / (-log(xy))`.

Integrating, substitute `x = e^{-s}`, `y = e^{-t}` for `s, t > 0`, giving
`dx dy = e^{-s-t} ds dt` and `-log(xy) = s + t`.  The bound integral becomes
`∫₀^∞ ∫₀^∞ e^{-s-t}/(s+t) ds dt`.  A clean way to evaluate this is the identity
`1/(s+t) = ∫₀^∞ e^{-r(s+t)} dr`, turning the double integral into

  `∫₀^∞ (∫₀^∞ e^{-(1+r)s} ds) (∫₀^∞ e^{-(1+r)t} dt) dr`
    `= ∫₀^∞ 1/(1+r)^2 dr = 1`.

We formalize the statement; the detailed integral computation via Fubini and
change of variables is lengthy, and we record only the key pointwise inequality
`1/x - 1 ≥ -log x` below.
-/

/-- Pointwise lemma: `1/x - 1 ≥ -log x` for `x ∈ (0, 1]`. -/
lemma one_div_sub_one_ge_neg_log {x : ℝ} (hx : 0 < x) : -Real.log x ≤ 1 / x - 1 := by
  -- Let `u = -log x`, so `x = e^{-u}` and the claim becomes `u ≤ e^u - 1`.
  set u : ℝ := -Real.log x with hu_def
  have hx_eq : x = Real.exp (-u) := by
    rw [hu_def]; simp [Real.exp_log hx]
  have h_expu : 1 / x = Real.exp u := by
    rw [hx_eq]; rw [one_div, ← Real.exp_neg]; ring_nf
  rw [h_expu]
  -- Need: `u ≤ exp u - 1`, i.e. `1 + u ≤ exp u`.
  linarith [Real.add_one_le_exp u]

/-- Pointwise lemma: `1/x + |log y| - 1 ≥ -log x - log y > 0` for `x, y ∈ (0, 1)`. -/
lemma denom_lower_bound {x y : ℝ} (hx : 0 < x) (_hx1 : x < 1) (hy : 0 < y) (hy1 : y < 1) :
    -Real.log x + -Real.log y ≤ 1 / x + |Real.log y| - 1 := by
  have h1 : -Real.log x ≤ 1 / x - 1 := one_div_sub_one_ge_neg_log hx
  have h2 : Real.log y < 0 := Real.log_neg hy hy1
  have h3 : |Real.log y| = -Real.log y := abs_of_neg h2
  linarith [h3]

/-- Positivity of the denominator on `(0, 1) × (0, 1)`. -/
lemma denom_pos {x y : ℝ} (hx : 0 < x) (hx1 : x < 1) (hy : 0 < y) (hy1 : y < 1) :
    0 < 1 / x + |Real.log y| - 1 := by
  have h_neglog_x : 0 < -Real.log x := by
    have : Real.log x < 0 := Real.log_neg hx hx1
    linarith
  have h_neglog_y : 0 < -Real.log y := by
    have : Real.log y < 0 := Real.log_neg hy hy1
    linarith
  have := denom_lower_bound hx hx1 hy hy1
  linarith

snip end

problem imc2004_p11 :
    ∫ x in Set.Ioo (0:ℝ) 1, ∫ y in Set.Ioo (0:ℝ) 1,
      1 / (1/x + |Real.log y| - 1) ≤ 1 := by
  -- TODO: complete the proof.  The statement reduces via `x = e^{-s}, y = e^{-t}`
  -- and the pointwise bound `1/x + |log y| - 1 ≥ -log(xy)` to
  -- `∫₀^∞ ∫₀^∞ e^{-s-t}/(s+t) ds dt ≤ 1`, which equals `1` via the identity
  -- `1/(s+t) = ∫₀^∞ e^{-r(s+t)} dr` followed by Fubini.
  sorry

end Imc2004P11
