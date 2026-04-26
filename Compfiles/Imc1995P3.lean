/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1995, Problem 3 (Day 1)

Let `f` be twice continuously differentiable on `(0, +∞)` with
`lim_{x → 0+} f'(x) = -∞` and `lim_{x → 0+} f''(x) = +∞`. Show

  `lim_{x → 0+} f(x) / f'(x) = 0`.

## Proof outline (official solution)

Pick `r > 0` with `f'(x) < 0` and `f''(x) > 0` on `(0, r)`. Then `f` is
strictly decreasing and `f'` is strictly increasing on `(0, r)`. Fix
`x₀ ∈ (0, r)`. By the Mean Value Theorem applied to `f` on `[x, x₀]` for
`0 < x < x₀`, there is `ξ ∈ (x, x₀)` with

  `f(x) - f(x₀) = f'(ξ)(x - x₀)`.

Since `f' < 0` and `f'` is increasing, `f'(x) < f'(ξ) < 0`, so
`0 < f'(ξ) / f'(x) < 1`. Multiplying the negative quantity `x - x₀ < 0`
by this number in `(0, 1)` gives

  `x - x₀ < (f'(ξ) / f'(x)) · (x - x₀) = (f(x) - f(x₀)) / f'(x) < 0`.

Hence `x - x₀ < f(x) / f'(x) - f(x₀) / f'(x) < 0`. As `x → 0+`, the term
`f(x₀) / f'(x) → 0` since `f'(x) → -∞` and `f(x₀)` is a constant.
Therefore

  `-x₀ ≤ liminf_{x → 0+} f(x) / f'(x) ≤ limsup_{x → 0+} f(x) / f'(x) ≤ 0`.

Since `x₀ > 0` is arbitrary in `(0, r)` and can be taken arbitrarily
small, both `liminf` and `limsup` equal `0`, giving the result.
-/

namespace Imc1995P3

set_option linter.unusedVariables false

open Filter Topology Set

problem imc1995_p3
    (f f' f'' : ℝ → ℝ)
    (hf'  : ∀ x ∈ Ioi (0:ℝ), HasDerivAt f (f' x) x)
    (hf'' : ∀ x ∈ Ioi (0:ℝ), HasDerivAt f' (f'' x) x)
    (hf'_cont  : ContinuousOn f' (Ioi 0))
    (hf''_cont : ContinuousOn f'' (Ioi 0))
    (hlim_f'  : Tendsto f'  (𝓝[>] 0) atBot)
    (hlim_f'' : Tendsto f'' (𝓝[>] 0) atTop) :
    Tendsto (fun x => f x / f' x) (𝓝[>] 0) (𝓝 0) := by
  -- Step 1: pick r > 0 with f' < 0 and f'' > 0 on (0, r).
  -- From `hlim_f'` we get f'(x) < 0 eventually.
  have hf'_neg_event : ∀ᶠ x in 𝓝[>] (0:ℝ), f' x < 0 :=
    hlim_f' (Iio_mem_atBot 0)
  -- From `hlim_f''` we get f''(x) > 0 eventually.
  have hf''_pos_event : ∀ᶠ x in 𝓝[>] (0:ℝ), 0 < f'' x :=
    hlim_f'' (Ioi_mem_atTop 0)
  -- The events (0,r) are a basis of 𝓝[>] 0; extract `r` so both hold.
  have hboth : ∀ᶠ x in 𝓝[>] (0:ℝ), f' x < 0 ∧ 0 < f'' x :=
    hf'_neg_event.and hf''_pos_event
  -- Translate this into: there exists r > 0 such that for all x ∈ (0, r),
  -- f' x < 0 and f'' x > 0.
  rw [eventually_nhdsWithin_iff] at hboth
  rw [Metric.eventually_nhds_iff] at hboth
  obtain ⟨r, hr_pos, hr⟩ := hboth
  -- For x ∈ (0, r), simplify hr.
  have hr' : ∀ x ∈ Ioo (0:ℝ) r, f' x < 0 ∧ 0 < f'' x := by
    intro x hx
    have hxd : dist x 0 < r := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hx.1]; exact hx.2
    exact hr hxd hx.1
  -- f' is strictly monotone on (0, r): use that f'' > 0 there.
  have hmono_f' : StrictMonoOn f' (Ioo (0:ℝ) r) := by
    have hderiv : ∀ x ∈ interior (Ioo (0:ℝ) r), HasDerivAt f' (f'' x) x := by
      intro x hx
      rw [interior_Ioo] at hx
      exact hf'' x (Ioo_subset_Ioi_self hx)
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioo 0 r)
      (hf'_cont.mono (Ioo_subset_Ioi_self))
      (fun x hx => (hderiv x hx).hasDerivWithinAt)
    intro x hx
    rw [interior_Ioo] at hx
    exact (hr' x hx).2
  -- f is strictly antitone on (0, r): use that f' < 0 there.
  have hanti_f : StrictAntiOn f (Ioo (0:ℝ) r) := by
    have hderiv : ∀ x ∈ interior (Ioo (0:ℝ) r), HasDerivAt f (f' x) x := by
      intro x hx
      rw [interior_Ioo] at hx
      exact hf' x (Ioo_subset_Ioi_self hx)
    have hf_cont : ContinuousOn f (Ioo (0:ℝ) r) := by
      intro x hx
      exact (hf' x (Ioo_subset_Ioi_self hx)).continuousAt.continuousWithinAt
    apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Ioo 0 r) hf_cont
      (fun x hx => (hderiv x hx).hasDerivWithinAt)
    intro x hx
    rw [interior_Ioo] at hx
    exact (hr' x hx).1
  -- Now the main argument: show liminf ≥ 0 and limsup ≤ 0 of f/f' as x → 0+.
  -- Equivalently, show |f(x)/f'(x)| → 0, i.e. for every ε > 0, eventually |f/f'| < ε.
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Pick x₀ = min (r/2, ε/2) ∈ (0, r) and small.
  set x₀ : ℝ := min (r/2) (ε/2) with hx₀_def
  have hx₀_pos : 0 < x₀ := lt_min (by linarith) (by linarith)
  have hx₀_lt_r : x₀ < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hx₀_le_eps2 : x₀ ≤ ε/2 := min_le_right _ _
  have hx₀_mem : x₀ ∈ Ioo (0:ℝ) r := ⟨hx₀_pos, hx₀_lt_r⟩
  -- Let M = f x₀; this is a constant.
  set M : ℝ := f x₀ with hM_def
  -- Eventually as x → 0+: x ∈ (0, x₀) and |M / f' x| < ε/2.
  -- For the latter, use that f' x → -∞, so 1/f'(x) → 0, hence M/f'(x) → 0.
  have h_one_div : Tendsto (fun x => 1 / f' x) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := hlim_f'.inv_tendsto_atBot
    have heq : (fun x => 1 / f' x) = (f')⁻¹ := by
      funext x; rw [Pi.inv_apply, one_div]
    rw [heq]; exact h
  have h_M_div : Tendsto (fun x => M / f' x) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun x => M * (1 / f' x)) (𝓝[>] (0:ℝ)) (𝓝 (M * 0)) :=
      h_one_div.const_mul M
    rw [mul_zero] at h1
    convert h1 using 1
    funext x; rw [mul_one_div]
  have h_M_small : ∀ᶠ x in 𝓝[>] (0:ℝ), |M / f' x| < ε/2 := by
    have := h_M_div
    rw [Metric.tendsto_nhds] at this
    have hε2 : 0 < ε/2 := by linarith
    have := this (ε/2) hε2
    filter_upwards [this] with x hx
    rw [Real.dist_eq, sub_zero] at hx
    exact hx
  -- Eventually x ∈ (0, x₀).
  have h_x_small : ∀ᶠ x in 𝓝[>] (0:ℝ), x < x₀ := by
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨x₀, hx₀_pos, ?_⟩
    intro y hy hy_pos
    rw [Real.dist_eq, sub_zero, abs_of_pos hy_pos] at hy
    exact hy
  -- Eventually x > 0 trivially in 𝓝[>] 0.
  have h_x_pos : ∀ᶠ x in 𝓝[>] (0:ℝ), 0 < x := self_mem_nhdsWithin
  -- f' x < 0 eventually.
  have h_fp_neg : ∀ᶠ x in 𝓝[>] (0:ℝ), f' x < 0 := hf'_neg_event
  -- f' is monotone on (0,r) eventually-restrictable.
  -- Combine all eventualities.
  filter_upwards [h_M_small, h_x_small, h_x_pos, h_fp_neg] with x hMε hxx₀ hxpos hf'xneg
  -- We're at a point x ∈ (0, x₀) ⊂ (0, r). Show |f x / f' x| < ε.
  have hx_mem : x ∈ Ioo (0:ℝ) r := ⟨hxpos, lt_trans hxx₀ hx₀_lt_r⟩
  -- MVT on [x, x₀]: there is ξ ∈ (x, x₀) with f x - f x₀ = f' ξ * (x - x₀).
  have hxle : x ≤ x₀ := le_of_lt hxx₀
  have hf_cont_xx0 : ContinuousOn f (Icc x x₀) := by
    intro y hy
    have hy_mem : y ∈ Ioi (0:ℝ) :=
      lt_of_lt_of_le hxpos hy.1
    exact (hf' y hy_mem).continuousAt.continuousWithinAt
  have hf_diff_xx0 : ∀ y ∈ Ioo x x₀, HasDerivAt f (f' y) y := by
    intro y hy
    have hy_mem : y ∈ Ioi (0:ℝ) := lt_trans hxpos hy.1
    exact hf' y hy_mem
  -- exists_hasDerivAt_eq_slope (Cauchy-like).
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ :=
    exists_hasDerivAt_eq_slope f f' hxx₀ hf_cont_xx0
      (fun y hy => hf_diff_xx0 y hy)
  -- hξ_eq : f' ξ = (f x₀ - f x) / (x₀ - x)
  -- ξ ∈ (x, x₀) ⊂ (0, r).
  have hξ_in_0r : ξ ∈ Ioo (0:ℝ) r :=
    ⟨lt_trans hxpos hξ_mem.1, lt_trans hξ_mem.2 hx₀_lt_r⟩
  -- f' is strictly monotone on (0, r), x < ξ, so f' x < f' ξ.
  have hf'x_lt_f'ξ : f' x < f' ξ :=
    hmono_f' hx_mem hξ_in_0r hξ_mem.1
  -- f' ξ < 0:
  have hf'ξ_neg : f' ξ < 0 := (hr' ξ hξ_in_0r).1
  -- so 0 < f' ξ / f' x < 1.
  have hratio_pos : 0 < f' ξ / f' x := div_pos_of_neg_of_neg hf'ξ_neg hf'xneg
  have hratio_lt_one : f' ξ / f' x < 1 := by
    rw [div_lt_one_of_neg hf'xneg]; exact hf'x_lt_f'ξ
  -- Now: from `hξ_eq`, f x - f x₀ = f' ξ * (x - x₀).
  have hslope : f x - f x₀ = f' ξ * (x - x₀) := by
    have : (f x₀ - f x) / (x₀ - x) = f' ξ := hξ_eq.symm
    have hsub_ne : x₀ - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hxx₀)
    field_simp at this
    linarith [this]
  -- Divide by f' x (nonzero), get (f x - f x₀) / f' x = (f' ξ / f' x) * (x - x₀).
  have hf'x_ne : f' x ≠ 0 := ne_of_lt hf'xneg
  have hquot : (f x - f x₀) / f' x = (f' ξ / f' x) * (x - x₀) := by
    rw [hslope]; field_simp
  -- Now bound: x - x₀ < 0 since x < x₀.
  have hx_minus_neg : x - x₀ < 0 := by linarith
  -- (f' ξ / f' x) ∈ (0, 1) and x - x₀ < 0, so:
  -- x - x₀ < (f' ξ / f' x) * (x - x₀) < 0
  have hineq_lower : x - x₀ < (f' ξ / f' x) * (x - x₀) := by
    -- Multiplying x - x₀ < 0 by ratio < 1 (and > 0) reverses or preserves?
    -- Equivalent to (1 - ratio) * (x - x₀) < 0, true since 1 - ratio > 0.
    nlinarith
  have hineq_upper : (f' ξ / f' x) * (x - x₀) < 0 :=
    mul_neg_of_pos_of_neg hratio_pos hx_minus_neg
  -- So x - x₀ < (f x - f x₀) / f' x < 0.
  rw [← hquot] at hineq_lower hineq_upper
  -- Rewrite (f x - f x₀)/f' x = f x / f' x - f x₀ / f' x.
  have hsplit : (f x - f x₀) / f' x = f x / f' x - f x₀ / f' x := by
    rw [sub_div]
  rw [hsplit] at hineq_lower hineq_upper
  -- Recall M = f x₀, so f x₀ / f' x = M / f' x.
  -- Thus: x - x₀ + M / f' x < f x / f' x < M / f' x.
  -- Now goal: |f x / f' x - 0| < ε.
  rw [Real.dist_eq, sub_zero]
  -- |f x / f' x| < ε.
  -- f x / f' x ≤ M / f' x, and ≥ x - x₀ + M / f' x.
  -- |M / f' x| < ε/2 ≤ ε/2. Also x₀ - x ≤ x₀ ≤ ε/2.
  -- Upper bound: f x / f' x < M / f' x ≤ |M / f' x| < ε/2 < ε.
  -- Lower bound: f x / f' x > x - x₀ + M / f' x ≥ -x₀ - |M / f' x| > -ε/2 - ε/2 = -ε.
  rw [abs_lt]
  refine ⟨?_, ?_⟩
  · -- show -ε < f x / f' x
    have h1 : -x₀ ≤ x - x₀ := by linarith
    have h2 : -|M / f' x| ≤ M / f' x := neg_abs_le _
    have h3 : -x₀ + (-(ε/2)) < x - x₀ + M / f' x := by
      have : -|M / f' x| > -(ε/2) := by linarith [hMε]
      linarith
    have h4 : -x₀ ≥ -(ε/2) := by linarith
    have hlow : x - x₀ + M / f' x < f x / f' x - M / f' x + M / f' x := by
      have := hineq_lower
      linarith
    have hlow' : x - x₀ + M / f' x < f x / f' x := by linarith
    linarith
  · -- show f x / f' x < ε
    have h2 : M / f' x ≤ |M / f' x| := le_abs_self _
    have hup : f x / f' x - M / f' x < 0 := hineq_upper
    have : f x / f' x < M / f' x := by linarith
    linarith [le_abs_self (M / f' x), hMε]

end Imc1995P3
