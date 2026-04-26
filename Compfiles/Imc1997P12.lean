/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1997, Problem 12 (Day 2, Problem 6)

A continuous function `f : [0, 1] → ℝ` is said to "cross the axis" at a point
`x ∈ [0, 1]` if `f x = 0` but every neighborhood of `x` (intersected with
`[0, 1]`) contains both points where `f` is positive and points where `f` is
negative.

(a) Give an example of a continuous function `f : [0, 1] → ℝ` that crosses the
    axis at infinitely many points.

(b) Can a continuous function `f : [0, 1] → ℝ` cross the axis at uncountably
    many points?

## Answers

(a) **Yes.**  The function `f(x) = x · sin(π / x)` (extended continuously by
    `f(0) = 0`) crosses the axis at every point `1 / k` for `k ≥ 2`.  Indeed,
    `f(1/k) = (1/k) · sin(kπ) = 0`.  On the open interval `(1/(k+1), 1/k)` the
    quantity `π/x` ranges over `(kπ, (k+1)π)`, so `sin(π/x)` has constant sign
    `(-1)^k` and `f` has constant sign `(-1)^k`.  Similarly on
    `(1/k, 1/(k-1))` the function `f` has constant sign `(-1)^{k-1}`.  Hence
    just to the left and just to the right of `1/k`, the values of `f` have
    opposite signs, so `f` crosses the axis at `1/k`.

(b) **Yes.**  Let `C ⊆ [0, 1]` be the standard Cantor set, which is
    uncountable.  Its complement in `[0, 1)` is a countable union of disjoint
    open intervals `(a_{k,i}, b_{k,i})`, where `k ≥ 1` indexes the depth (so
    that `2^{k-1}` intervals appear at depth `k`).  On each such interval,
    place a "tent" function `g_k`: piecewise linear, vanishing at the
    endpoints and the rest of `[0, 1]`, with peak `2^{-k}` at the midpoint.
    Set
    ```
        f(x) := ∑_{k=1}^∞ (-1)^k · g_k(x).
    ```
    The series converges uniformly because `|(-1)^k g_k(x)| ≤ 2^{-k}`, so `f`
    is continuous.  On the depth-`k` intervals `f` has the constant sign
    `(-1)^k`.  Each point of the Cantor set is a limit of depth-`k` intervals
    of *both* signs (any neighborhood of a Cantor point contains depth-`k`
    intervals for arbitrarily large `k`), so `f` vanishes on `C` and crosses
    the axis at every point of `C`.

## Formalization status

We formalize the *statement* of the two parts.  Part (a) is stated using the
explicit function `f₀(x) = x · sin(π / x)` (with `f₀ 0 = 0`); the proof
requires fine sign analysis of `sin` on intervals of the form
`(kπ, (k+1)π)`, which we leave as `sorry` with the roadmap above.

Part (b) requires the full Cantor construction outlined above; this is left
entirely as `sorry`.
-/

namespace Imc1997P12

open Real Set

/-- The function `f : ℝ → ℝ` is said to **cross the axis at `x`** (within
the interval `[0, 1]`) if `f x = 0` and every neighborhood of `x` contains
both a point of `[0, 1]` where `f` is strictly positive and a point of
`[0, 1]` where `f` is strictly negative. -/
def CrossesAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  f x = 0 ∧
  ∀ ε > (0 : ℝ),
    (∃ y ∈ Icc (0 : ℝ) 1, |y - x| < ε ∧ 0 < f y) ∧
    (∃ z ∈ Icc (0 : ℝ) 1, |z - x| < ε ∧ f z < 0)

/-! ### Part (a): the explicit example. -/

/-- The example function for part (a): `x ↦ x · sin(π / x)`, extended by
`0` at `x = 0`.  Outside the open interval `(0, 1)` we still use the formula
`x · sin(π / x)` (which evaluates to `0` at `x = 0` only via the convention
`sin(π / 0) = sin 0 = 0` in Mathlib's `Real.sin`); but this convention is
irrelevant since the problem is only about behavior on `[0, 1]`. -/
noncomputable def f₀ (x : ℝ) : ℝ :=
  if x = 0 then 0 else x * Real.sin (Real.pi / x)

/-- The example function `f₀` is continuous on all of `ℝ`. -/
lemma f₀_continuous : Continuous f₀ := by
  -- Away from `0`, `f₀ x = x * sin(π / x)`, continuous. At `0`, we use the
  -- bound `|x * sin(π / x)| ≤ |x|` (squeeze).
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · -- Continuity at `0`: by squeeze using `|f₀ y| ≤ |y|`.
    subst hx
    rw [ContinuousAt, show f₀ 0 = 0 from by unfold f₀; simp]
    have hbound : ∀ y, |f₀ y| ≤ |y| := by
      intro y
      unfold f₀
      by_cases hy : y = 0
      · simp [hy]
      · rw [if_neg hy, abs_mul]
        have hsin : |Real.sin (Real.pi / y)| ≤ 1 := Real.abs_sin_le_one _
        nlinarith [abs_nonneg y, abs_nonneg (Real.sin (Real.pi / y))]
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with y hy
    rw [Real.dist_eq, sub_zero]
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy
    exact lt_of_le_of_lt (hbound y) hy
  · -- Continuity at `x ≠ 0`: standard.
    have hcont : ContinuousAt (fun y => y * Real.sin (Real.pi / y)) x := by
      apply ContinuousAt.mul continuousAt_id
      exact (Real.continuous_sin).continuousAt.comp
        (continuousAt_const.div continuousAt_id hx)
    -- f₀ agrees with the formula in a neighborhood of x.
    have hag : ∀ᶠ y in nhds x, f₀ y = y * Real.sin (Real.pi / y) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
      have hy' : y ≠ 0 := hy
      unfold f₀
      rw [if_neg hy']
    exact (hcont.congr (Filter.EventuallyEq.symm hag) :)

/-- The example function vanishes at `1 / k` for any positive integer `k`. -/
lemma f₀_inv_natCast_eq_zero (k : ℕ) (hk : 1 ≤ k) : f₀ ((k : ℝ)⁻¹) = 0 := by
  -- f₀(1/k) = (1/k) * sin(π * k) = (1/k) * 0 = 0 because sin(πk) = 0.
  unfold f₀
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkne : ((k : ℝ))⁻¹ ≠ 0 := inv_ne_zero hkpos.ne'
  rw [if_neg hkne]
  have hxinv : Real.pi / ((k : ℝ))⁻¹ = Real.pi * k := by
    field_simp
  rw [hxinv]
  have : Real.sin (Real.pi * k) = 0 := by
    rw [mul_comm]
    exact_mod_cast Real.sin_int_mul_pi k
  rw [this, mul_zero]

/-- Helper: `sin (π / x)` is positive on `(1/(2n+1), 1/(2n))` for `n ≥ 1`,
since on this interval `π / x ∈ (2nπ, (2n+1)π)`, where `sin` is positive
(by `2π`-periodicity, this reduces to `sin > 0` on `(0, π)`). -/
lemma sin_pi_div_pos {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx₁ : (1 : ℝ) / (2 * n + 1) < x) (hx₂ : x < 1 / (2 * n)) :
    0 < Real.sin (Real.pi / x) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2nR : (0 : ℝ) < 2 * (n : ℝ) := by linarith
  have h2n1R : (0 : ℝ) < 2 * (n : ℝ) + 1 := by linarith
  have hxpos : 0 < x := by
    have h0 : (0 : ℝ) < 1 / (2 * n + 1) := by positivity
    linarith
  have hpipos : (0 : ℝ) < Real.pi := Real.pi_pos
  -- π/x > 2nπ : i.e. 1/x > 2n, i.e. x < 1/(2n).
  have h1 : 2 * (n : ℝ) * Real.pi < Real.pi / x := by
    rw [show Real.pi / x = (1/x) * Real.pi from by field_simp]
    have h1x : 2 * (n : ℝ) < 1 / x := by
      rw [lt_div_iff₀ hxpos]
      have : x * (2 * (n : ℝ)) < (1 / (2 * n)) * (2 * (n : ℝ)) := by
        have h2nposR : (0 : ℝ) < 2 * (n : ℝ) := h2nR
        nlinarith
      have heq : (1 / (2 * (n : ℝ))) * (2 * (n : ℝ)) = 1 := by field_simp
      linarith
    nlinarith
  -- π/x < (2n+1)π : i.e. 1/x < 2n+1, i.e. x > 1/(2n+1).
  have h2 : Real.pi / x < (2 * (n : ℝ) + 1) * Real.pi := by
    rw [show Real.pi / x = (1/x) * Real.pi from by field_simp]
    have h1x : 1 / x < 2 * (n : ℝ) + 1 := by
      rw [div_lt_iff₀ hxpos]
      have : (1 / (2 * (n : ℝ) + 1)) * (2 * (n : ℝ) + 1) < x * (2 * (n : ℝ) + 1) := by
        nlinarith
      have heq : (1 / (2 * (n : ℝ) + 1)) * (2 * (n : ℝ) + 1) = 1 := by field_simp
      linarith
    nlinarith
  -- Now y = π/x - 2nπ ∈ (0, π).
  set y : ℝ := Real.pi / x - 2 * (n : ℝ) * Real.pi with hy_def
  have hy1 : 0 < y := by rw [hy_def]; linarith
  have hy2 : y < Real.pi := by rw [hy_def]; linarith
  -- sin(π/x) = sin(y + 2nπ) = sin(y).
  have hsin_eq : Real.sin (Real.pi / x) = Real.sin y := by
    have heq : Real.pi / x = y + ((n : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [hy_def]; push_cast; ring
    rw [heq]
    exact_mod_cast Real.sin_add_int_mul_two_pi y n
  rw [hsin_eq]
  exact Real.sin_pos_of_pos_of_lt_pi hy1 hy2

/-- Helper: `sin (π / x)` is negative on `(1/(2n+2), 1/(2n+1))` for `n ≥ 0`,
since on this interval `π / x ∈ ((2n+1)π, (2n+2)π)`, where `sin` is negative
(by `2π`-periodicity, reduces to `sin < 0` on `(π, 2π)`, equivalently
`sin > 0` on `(0, π)` after shifting by `π`). -/
lemma sin_pi_div_neg {n : ℕ} {x : ℝ}
    (hx₁ : (1 : ℝ) / (2 * n + 2) < x) (hx₂ : x < 1 / (2 * n + 1)) :
    Real.sin (Real.pi / x) < 0 := by
  have h2n1R : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have h2n2R : (0 : ℝ) < 2 * (n : ℝ) + 2 := by positivity
  have hxpos : 0 < x := by
    have h0 : (0 : ℝ) < 1 / (2 * (n : ℝ) + 2) := by positivity
    have h0' : (0 : ℝ) < 1 / (2 * (↑n : ℝ) + 2) := h0
    linarith [hx₁, h0]
  have hpipos : (0 : ℝ) < Real.pi := Real.pi_pos
  -- π/x > (2n+1)π : i.e. x < 1/(2n+1).
  have h1 : (2 * (n : ℝ) + 1) * Real.pi < Real.pi / x := by
    rw [show Real.pi / x = (1/x) * Real.pi from by field_simp]
    have h1x : 2 * (n : ℝ) + 1 < 1 / x := by
      rw [lt_div_iff₀ hxpos]
      have hh : x * (2 * (n : ℝ) + 1) < (1 / (2 * (n : ℝ) + 1)) * (2 * (n : ℝ) + 1) := by
        nlinarith
      have heq : (1 / (2 * (n : ℝ) + 1)) * (2 * (n : ℝ) + 1) = 1 := by field_simp
      linarith
    nlinarith
  -- π/x < (2n+2)π : i.e. x > 1/(2n+2).
  have h2 : Real.pi / x < (2 * (n : ℝ) + 2) * Real.pi := by
    rw [show Real.pi / x = (1/x) * Real.pi from by field_simp]
    have h1x : 1 / x < 2 * (n : ℝ) + 2 := by
      rw [div_lt_iff₀ hxpos]
      have hh : (1 / (2 * (n : ℝ) + 2)) * (2 * (n : ℝ) + 2) < x * (2 * (n : ℝ) + 2) := by
        nlinarith
      have heq : (1 / (2 * (n : ℝ) + 2)) * (2 * (n : ℝ) + 2) = 1 := by field_simp
      linarith
    nlinarith
  -- Now y = π/x - (2n+1)π ∈ (0, π).
  set y : ℝ := Real.pi / x - (2 * (n : ℝ) + 1) * Real.pi with hy_def
  have hy1 : 0 < y := by rw [hy_def]; linarith
  have hy2 : y < Real.pi := by rw [hy_def]; linarith
  -- sin(π/x) = sin(y + (2n+1)π) = sin((y + π) + 2nπ) = sin(y + π) = -sin(y).
  have hsin_eq : Real.sin (Real.pi / x) = - Real.sin y := by
    have heq : Real.pi / x = (y + Real.pi) + ((n : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [hy_def]; push_cast; ring
    rw [heq]
    have hp : Real.sin ((y + Real.pi) + ((n : ℤ) : ℝ) * (2 * Real.pi)) =
        Real.sin (y + Real.pi) := by
      exact_mod_cast Real.sin_add_int_mul_two_pi (y + Real.pi) n
    rw [hp, Real.sin_add_pi]
  rw [hsin_eq]
  have hpos : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi hy1 hy2
  linarith

/-- The point `1 / (2k+1)` is a crossing point of `f₀`, for any `k ≥ 1`. -/
lemma crossesAt_inv_two_k_plus_one {k : ℕ} (hk : 1 ≤ k) :
    CrossesAt f₀ (1 / (2 * (k : ℝ) + 1)) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h2k1pos : (0 : ℝ) < 2 * (k : ℝ) + 1 := by linarith
  have h2k2pos : (0 : ℝ) < 2 * (k : ℝ) + 2 := by linarith
  have h2kpos : (0 : ℝ) < 2 * (k : ℝ) := by linarith
  -- The crossing point itself.
  set x₀ : ℝ := 1 / (2 * (k : ℝ) + 1) with hx₀_def
  have hx₀_pos : 0 < x₀ := by rw [hx₀_def]; positivity
  -- Key gap sizes between adjacent reciprocals.
  have hgap_R : 1 / (2 * (k : ℝ)) - x₀ = 1 / (2 * (k : ℝ) * (2 * (k : ℝ) + 1)) := by
    rw [hx₀_def]; field_simp; ring
  have hgap_L : x₀ - 1 / (2 * (k : ℝ) + 2) =
      1 / ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2)) := by
    rw [hx₀_def]; field_simp; ring
  have hgap_R_pos : 0 < 1 / (2 * (k : ℝ) * (2 * (k : ℝ) + 1)) := by positivity
  have hgap_L_pos : 0 < 1 / ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2)) := by positivity
  -- f₀(x₀) = 0.
  have h_f_zero : f₀ x₀ = 0 := by
    -- Use f₀_inv_natCast_eq_zero with k → 2k+1.
    have h2k1nat : (1 : ℕ) ≤ 2 * k + 1 := by omega
    have hcast : ((2 * k + 1 : ℕ) : ℝ)⁻¹ = x₀ := by
      rw [hx₀_def]; push_cast; rw [one_div]
    rw [← hcast]
    exact f₀_inv_natCast_eq_zero (2 * k + 1) h2k1nat
  refine ⟨h_f_zero, ?_⟩
  intro ε hε
  -- Choose δ small enough.
  have hε2 : 0 < ε / 2 := by linarith
  -- For positive value: use y in (x₀, 1/(2k)).
  -- For negative value: use z in (1/(2k+2), x₀).
  -- Note δ_pos is bounded by 1/(4k(2k+1)) ≤ 1/12 (since k ≥ 1), so x₀ + δ_pos ≤ 1.
  set δ_pos : ℝ := min (ε / 2) (1 / (4 * (k : ℝ) * (2 * (k : ℝ) + 1))) with hδ_pos_def
  have hδ_pos_pos : 0 < δ_pos := by
    rw [hδ_pos_def]; refine lt_min hε2 ?_; positivity
  have hδ_pos_small : δ_pos ≤ 1 / (4 * (k : ℝ) * (2 * (k : ℝ) + 1)) := min_le_right _ _
  set δ_neg : ℝ := min (ε / 2) (1 / (2 * ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2)))) with hδ_neg_def
  have hδ_neg_pos : 0 < δ_neg := by
    rw [hδ_neg_def]; refine lt_min hε2 ?_; positivity
  refine ⟨⟨x₀ + δ_pos, ?_, ?_, ?_⟩, ⟨x₀ - δ_neg, ?_, ?_, ?_⟩⟩
  · -- y ∈ [0, 1]: x₀ + δ_pos > 0, and x₀ + δ_pos < 1/(2k) ≤ 1/2 ≤ 1.
    refine ⟨by linarith [hδ_pos_pos, hx₀_pos], ?_⟩
    -- x₀ ≤ 1/3 (since 2k+1 ≥ 3), δ_pos ≤ 1/(4k(2k+1)) ≤ 1/12.
    have hx0_le : x₀ ≤ 1/3 := by
      rw [hx₀_def]
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    have hδ_le : δ_pos ≤ 1 / 12 := by
      have h1 : (12 : ℝ) ≤ 4 * (k : ℝ) * (2 * (k : ℝ) + 1) := by nlinarith
      have h2 : (1 : ℝ) / (4 * (k : ℝ) * (2 * (k : ℝ) + 1)) ≤ 1 / 12 := by
        apply one_div_le_one_div_of_le (by norm_num) h1
      linarith
    linarith
  · -- |y - x₀| < ε.
    show |x₀ + δ_pos - x₀| < ε
    rw [show x₀ + δ_pos - x₀ = δ_pos from by ring, abs_of_pos hδ_pos_pos]
    have : δ_pos ≤ ε / 2 := min_le_left _ _
    linarith
  · -- 0 < f₀ (x₀ + δ_pos).
    -- y = x₀ + δ_pos lies in (x₀, 1/(2k)).
    have hy_lt : x₀ + δ_pos < 1 / (2 * (k : ℝ)) := by
      have hδ_le : δ_pos ≤ 1 / (4 * (k : ℝ) * (2 * (k : ℝ) + 1)) := min_le_right _ _
      have h_target : 1 / (4 * (k : ℝ) * (2 * (k : ℝ) + 1)) <
          1 / (2 * (k : ℝ) * (2 * (k : ℝ) + 1)) := by
        apply one_div_lt_one_div_of_lt
        · positivity
        · nlinarith
      linarith [hgap_R]
    have hy_pos_lt : x₀ < x₀ + δ_pos := by linarith
    -- f₀ (x₀ + δ_pos) = (x₀ + δ_pos) * sin(π/(x₀ + δ_pos)).
    have hxδ_pos : 0 < x₀ + δ_pos := by linarith
    have hxδ_ne : x₀ + δ_pos ≠ 0 := hxδ_pos.ne'
    have hf_eq : f₀ (x₀ + δ_pos) = (x₀ + δ_pos) * Real.sin (Real.pi / (x₀ + δ_pos)) := by
      unfold f₀; rw [if_neg hxδ_ne]
    rw [hf_eq]
    have hsin_pos : 0 < Real.sin (Real.pi / (x₀ + δ_pos)) := by
      apply sin_pi_div_pos hk
      · -- 1 / (2k+1) < x₀ + δ_pos.
        show (1 : ℝ) / (2 * (k : ℝ) + 1) < x₀ + δ_pos
        rw [show ((1 : ℝ) / (2 * (k : ℝ) + 1)) = x₀ from hx₀_def.symm]
        linarith
      · exact hy_lt
    positivity
  · -- z ∈ [0, 1].
    refine ⟨?_, ?_⟩
    · -- 0 ≤ x₀ - δ_neg.
      have hδ_neg_le : δ_neg ≤ 1 / (2 * ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2))) := min_le_right _ _
      -- δ_neg ≤ 1/(2*((2k+1)(2k+2))) < 1/((2k+1)(2k+2)) = x₀ - 1/(2k+2)
      have : δ_neg < x₀ - 1 / (2 * (k : ℝ) + 2) := by
        rw [hgap_L]
        have h_target : 1 / (2 * ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2))) <
            1 / ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2)) := by
          apply one_div_lt_one_div_of_lt
          · positivity
          · nlinarith
        linarith
      have h1pos : 0 < 1 / (2 * (k : ℝ) + 2) := by positivity
      linarith
    · -- x₀ - δ_neg ≤ x₀ ≤ 1.
      have hx0_le : x₀ ≤ 1 := by
        rw [hx₀_def, div_le_one h2k1pos]; linarith
      linarith [hδ_neg_pos]
  · -- |z - x₀| < ε.
    show |x₀ - δ_neg - x₀| < ε
    rw [show x₀ - δ_neg - x₀ = -δ_neg from by ring, abs_neg, abs_of_pos hδ_neg_pos]
    have : δ_neg ≤ ε / 2 := min_le_left _ _
    linarith
  · -- f₀ (x₀ - δ_neg) < 0.
    have hz_gt : 1 / (2 * (k : ℝ) + 2) < x₀ - δ_neg := by
      have hδ_le : δ_neg ≤ 1 / (2 * ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2))) := min_le_right _ _
      have h_target : 1 / (2 * ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2))) <
          1 / ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2)) := by
        apply one_div_lt_one_div_of_lt
        · positivity
        · nlinarith
      linarith [hgap_L]
    have hz_pos : 0 < x₀ - δ_neg := by
      have : 0 < 1 / (2 * (k : ℝ) + 2) := by positivity
      linarith
    have hz_ne : x₀ - δ_neg ≠ 0 := hz_pos.ne'
    have hf_eq : f₀ (x₀ - δ_neg) = (x₀ - δ_neg) * Real.sin (Real.pi / (x₀ - δ_neg)) := by
      unfold f₀; rw [if_neg hz_ne]
    rw [hf_eq]
    have hsin_neg : Real.sin (Real.pi / (x₀ - δ_neg)) < 0 := by
      apply sin_pi_div_neg
      · exact hz_gt
      · -- x₀ - δ_neg < 1/(2k+1) = x₀.
        show x₀ - δ_neg < (1 : ℝ) / (2 * (k : ℝ) + 1)
        rw [show ((1 : ℝ) / (2 * (k : ℝ) + 1)) = x₀ from hx₀_def.symm]
        linarith
    have := mul_neg_of_pos_of_neg hz_pos hsin_neg
    exact this

/-- **Part (a).** There exists a continuous function `f : ℝ → ℝ` that crosses
the axis at infinitely many points of `[0, 1]`. -/
problem imc1997_p12_part_a :
    ∃ f : ℝ → ℝ, Continuous f ∧
      Set.Infinite { x ∈ Icc (0 : ℝ) 1 | CrossesAt f x } := by
  refine ⟨f₀, f₀_continuous, ?_⟩
  -- The set `S = { 1/(2k+1) : k ≥ 1 }` is an infinite subset of crossing points.
  let S : Set ℝ := (fun k : ℕ => 1 / (2 * (k : ℝ) + 1)) '' { k | 1 ≤ k }
  have hS_sub : S ⊆ { x ∈ Icc (0 : ℝ) 1 | CrossesAt f₀ x } := by
    rintro x ⟨k, hk, rfl⟩
    refine ⟨⟨?_, ?_⟩, crossesAt_inv_two_k_plus_one hk⟩
    · positivity
    · have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have : (1 : ℝ) ≤ 2 * (k : ℝ) + 1 := by linarith
      rw [div_le_one (by linarith)]
      exact this
  apply Set.Infinite.mono hS_sub
  -- S is infinite because the map is injective and { k | 1 ≤ k } is infinite.
  apply Set.Infinite.image
  · -- Injectivity of k ↦ 1/(2k+1).
    intros a _ b _ hab
    have h2a1 : (0 : ℝ) < 2 * (a : ℝ) + 1 := by positivity
    have h2b1 : (0 : ℝ) < 2 * (b : ℝ) + 1 := by positivity
    have heq : 2 * (a : ℝ) + 1 = 2 * (b : ℝ) + 1 := by
      have := hab
      field_simp at this
      linarith
    have : (a : ℝ) = b := by linarith
    exact_mod_cast this
  · -- { k : ℕ | 1 ≤ k } is infinite.
    have : { k : ℕ | 1 ≤ k } = Set.Ici 1 := rfl
    rw [this]
    exact Set.Ici_infinite _

/-! ### Part (b): the Cantor construction.

The construction outlined in the docstring produces a continuous
`f : [0, 1] → ℝ` whose set of crossing points contains the standard Cantor
set (which is uncountable).  We do not formalize the Cantor construction
here; we state the theorem and leave it as `sorry`. -/

/-- **Part (b).** There exists a continuous function `f : ℝ → ℝ` that
crosses the axis at uncountably many points of `[0, 1]`. -/
problem imc1997_p12_part_b :
    ∃ f : ℝ → ℝ, Continuous f ∧
      ¬ Set.Countable { x ∈ Icc (0 : ℝ) 1 | CrossesAt f x } := by
  -- TODO.  Construction:
  --
  --   * Let `C ⊆ [0, 1]` be the standard Cantor set (uncountable).
  --   * Its complement in `[0, 1)` is a disjoint countable union of open
  --     intervals `J_{k, i}` where `k ≥ 1` is the depth and `i` indexes
  --     the `2^{k-1}` intervals at depth `k`.
  --   * On each interval `J_{k, i} = (a, b)`, define a tent function
  --       `tent_k(x) := 2^{-k} · max(0, 1 - |2(x - (a+b)/2)/(b - a)|)`,
  --     which equals `0` at the endpoints, peaks at `2^{-k}` at the
  --     midpoint, and is `0` outside `J_{k, i}`. Let `g_k` be the sum of
  --     these tents over all `i` at depth `k`; then `‖g_k‖_∞ ≤ 2^{-k}`.
  --   * Define `f(x) := ∑_{k=1}^∞ (-1)^k g_k(x)`. Uniform convergence
  --     follows from `|(-1)^k g_k| ≤ 2^{-k}`. Hence `f` is continuous.
  --   * For `x ∈ C`, every neighborhood of `x` meets infinitely many
  --     `J_{k,i}` of every parity, on which `f` has the corresponding sign.
  --     Hence `f` vanishes on `C` and crosses the axis at every `x ∈ C`.
  --   * Since `C` is uncountable, the set of crossing points is uncountable.
  sorry

end Imc1997P12
