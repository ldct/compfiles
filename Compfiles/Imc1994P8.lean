/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Exp

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1994, Problem 8 (Day 2 Problem 2)

Let `f(x,y) = (x² - y²) e^{-x² - y²}`.

(a) `f` attains its global maximum and minimum on `ℝ²`.
(b) The maximum value is `e⁻¹`, attained at `(±1, 0)`, and the minimum value
    is `-e⁻¹`, attained at `(0, ±1)`.

## Proof outline

Set `s = x² + y²` and `a = x² - y²`. Since `x², y² ≥ 0`, we have `|a| ≤ s`.
The single–variable function `g(u) = u · e^{-u}` on `u ≥ 0` is bounded above
by `e⁻¹`, since `g'(u) = (1-u)e^{-u}` and `g(1) = e⁻¹`. Hence

  `|f(x,y)| = |a| · e^{-s} ≤ s · e^{-s} ≤ e⁻¹`,

so `-e⁻¹ ≤ f(x,y) ≤ e⁻¹` for all `(x,y) ∈ ℝ²`. The values `e⁻¹` and `-e⁻¹`
are attained at `(1,0)` and `(0,1)` respectively, giving (b) and hence (a).
-/

namespace Imc1994P8

open Real

/-- For `u ≥ 0`, we have `u * exp (-u) ≤ exp (-1)`.
(In fact this holds for all real `u`, but we only need it for `u ≥ 0`.) -/
lemma key_ineq {u : ℝ} (_hu : 0 ≤ u) : u * exp (-u) ≤ exp (-1) := by
  -- The standard bound `1 + t ≤ exp t` at `t = u - 1` gives `u ≤ exp (u - 1)`.
  have hbound : u ≤ exp (u - 1) := by
    have h := Real.add_one_le_exp (u - 1)
    linarith
  -- Multiply both sides by `exp (-u) ≥ 0`:
  have hexp_nn : 0 ≤ exp (-u) := (exp_pos _).le
  have step : u * exp (-u) ≤ exp (u - 1) * exp (-u) :=
    mul_le_mul_of_nonneg_right hbound hexp_nn
  -- Simplify `exp (u - 1) * exp (-u) = exp (-1)`.
  have hsimp : exp (u - 1) * exp (-u) = exp (-1) := by
    rw [← exp_add]
    congr 1
    ring
  linarith [step, hsimp.le, hsimp.ge]

/-- The squared difference is bounded in absolute value by the squared sum. -/
lemma abs_sq_diff_le_sq_sum (x y : ℝ) : |x^2 - y^2| ≤ x^2 + y^2 := by
  have hx : 0 ≤ x^2 := sq_nonneg x
  have hy : 0 ≤ y^2 := sq_nonneg y
  rcases le_or_gt (x^2) (y^2) with h | h
  · rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_nonneg (by linarith)]
    linarith

/-- Pointwise bound: `|f(x,y)| ≤ e⁻¹`. -/
lemma f_abs_le (x y : ℝ) : |(x^2 - y^2) * exp (-x^2 - y^2)| ≤ exp (-1) := by
  set s := x^2 + y^2 with hs_def
  have hs_nn : 0 ≤ s := by positivity
  have hexp_nn : 0 ≤ exp (-s) := (exp_pos _).le
  have hrewrite : exp (-x^2 - y^2) = exp (-s) := by
    congr 1
    simp [s]
    ring
  rw [hrewrite, abs_mul, abs_of_nonneg hexp_nn]
  calc |x^2 - y^2| * exp (-s)
      ≤ s * exp (-s) :=
        mul_le_mul_of_nonneg_right (abs_sq_diff_le_sq_sum x y) hexp_nn
    _ ≤ exp (-1) := key_ineq hs_nn

/-- Upper bound: `f(x,y) ≤ e⁻¹`. -/
lemma f_le (x y : ℝ) : (x^2 - y^2) * exp (-x^2 - y^2) ≤ exp (-1) :=
  (le_abs_self _).trans (f_abs_le x y)

/-- Lower bound: `-e⁻¹ ≤ f(x,y)`. -/
lemma neg_le_f (x y : ℝ) : -exp (-1) ≤ (x^2 - y^2) * exp (-x^2 - y^2) := by
  have h := f_abs_le x y
  have h2 := neg_abs_le ((x^2 - y^2) * exp (-x^2 - y^2))
  linarith

/-- The maximum value `e⁻¹` is attained at `(1, 0)`. -/
lemma f_at_one_zero : ((1:ℝ)^2 - 0^2) * exp (-(1:ℝ)^2 - 0^2) = exp (-1) := by
  have h : -(1:ℝ)^2 - 0^2 = -1 := by ring
  rw [h]
  ring

/-- The minimum value `-e⁻¹` is attained at `(0, 1)`. -/
lemma f_at_zero_one : ((0:ℝ)^2 - 1^2) * exp (-(0:ℝ)^2 - 1^2) = -exp (-1) := by
  have h : -(0:ℝ)^2 - 1^2 = -1 := by ring
  rw [h]
  ring

/-- The function `f(x,y) = (x² - y²) e^{-x² - y²}` is bounded above by `e⁻¹`
and below by `-e⁻¹`, and both bounds are attained — proving simultaneously
that `f` attains its global maximum and minimum (statement (a)) and giving
the extremal values (statement (b)). -/
problem imc1994_p8 :
    (∀ x y : ℝ, (x^2 - y^2) * exp (-x^2 - y^2) ≤ exp (-1)) ∧
    (∀ x y : ℝ, -exp (-1) ≤ (x^2 - y^2) * exp (-x^2 - y^2)) ∧
    (∃ x y : ℝ, (x^2 - y^2) * exp (-x^2 - y^2) = exp (-1)) ∧
    (∃ x y : ℝ, (x^2 - y^2) * exp (-x^2 - y^2) = -exp (-1)) := by
  refine ⟨f_le, neg_le_f, ?_, ?_⟩
  · exact ⟨1, 0, f_at_one_zero⟩
  · exact ⟨0, 1, f_at_zero_one⟩

end Imc1994P8
