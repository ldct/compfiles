/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2020, Problem 5

Find all twice continuously differentiable functions `f : ℝ → (0, +∞)`
satisfying
  `f''(x) · f(x) ≥ 2 (f'(x))²` for all `x ∈ ℝ`.

Answer: the positive constant functions.
-/

namespace Imc2020P5

open Set

/-- The problem: a twice continuously differentiable positive function `f`
satisfying `f(x) · f''(x) ≥ 2 (f'(x))²` must be constant.

The official proof: let `g = 1/f`. Then `g'' = (2(f')² - f''f) / f³ ≤ 0`,
so `g > 0` is concave. A positive concave function on `ℝ` must be constant:
if `g(a) ≠ g(b)` with `a < b`, concavity forces `g` to become negative on
one side by extrapolation.
-/
problem imc2020_p5 (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hpos : ∀ x, 0 < f x)
    (hineq : ∀ x, f x * iteratedDeriv 2 f x ≥ 2 * (deriv f x) ^ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, f x = c := by
  have hf_diff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hf'_diff : Differentiable ℝ (deriv f) := hf.differentiable_deriv_two
  have hne : ∀ x, f x ≠ 0 := fun x => (hpos x).ne'
  -- Define g = 1/f.
  set g : ℝ → ℝ := fun x => (f x)⁻¹ with hg_def
  have hg_pos : ∀ x, 0 < g x := fun x => inv_pos.mpr (hpos x)
  -- Compute g'.
  have hg_deriv : ∀ x, deriv g x = -deriv f x / (f x) ^ 2 := by
    intro x
    exact deriv_fun_inv'' (hf_diff x) (hne x)
  have hg_diff : Differentiable ℝ g := fun x => (hf_diff x).inv (hne x)
  have hg'_diff : Differentiable ℝ (deriv g) := by
    have hfun : deriv g = fun x => -deriv f x / (f x) ^ 2 := funext hg_deriv
    rw [hfun]
    intro x
    refine DifferentiableAt.div ?_ ?_ ?_
    · exact (hf'_diff x).neg
    · exact ((hf_diff x).pow 2)
    · exact pow_ne_zero 2 (hne x)
  have h_iter2 : iteratedDeriv 2 f = deriv (deriv f) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  -- g''(x) ≤ 0.
  have hg''_nonpos : ∀ x, deriv (deriv g) x ≤ 0 := by
    intro x
    have hfun : deriv g = fun x => -deriv f x / (f x) ^ 2 := funext hg_deriv
    rw [hfun]
    have hf2_ne : (f x) ^ 2 ≠ 0 := pow_ne_zero 2 (hne x)
    have h_has : HasDerivAt (fun y => -deriv f y / (f y) ^ 2)
        ((- deriv (deriv f) x * (f x) ^ 2 -
          (- deriv f x) * (2 * f x ^ 1 * deriv f x)) / ((f x) ^ 2) ^ 2) x := by
      have hnum : HasDerivAt (fun y => -deriv f y) (-deriv (deriv f) x) x :=
        ((hf'_diff x).hasDerivAt).neg
      have hden : HasDerivAt (fun y => (f y) ^ 2) (2 * f x ^ 1 * deriv f x) x := by
        have := ((hf_diff x).hasDerivAt).pow 2
        simpa using this
      exact hnum.div hden hf2_ne
    rw [h_has.deriv]
    rw [h_iter2] at hineq
    have key : 2 * (deriv f x) ^ 2 - f x * deriv (deriv f) x ≤ 0 := by
      have := hineq x
      linarith
    have hf_pos_pow4 : 0 < ((f x) ^ 2) ^ 2 := by positivity
    have hnum_nonpos :
        -deriv (deriv f) x * (f x) ^ 2 - -deriv f x * (2 * f x ^ 1 * deriv f x) ≤ 0 := by
      have hrewrite : -deriv (deriv f) x * (f x) ^ 2 -
          -deriv f x * (2 * f x ^ 1 * deriv f x) =
          f x * (2 * (deriv f x) ^ 2 - f x * deriv (deriv f) x) := by ring
      rw [hrewrite]
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hpos x)) key
    exact div_nonpos_of_nonpos_of_nonneg hnum_nonpos (le_of_lt hf_pos_pow4)
  -- g is concave on ℝ.
  have hg_concave : ConcaveOn ℝ univ g :=
    concaveOn_univ_of_deriv2_nonpos hg_diff hg'_diff (by
      intro x
      have : deriv^[2] g x = deriv (deriv g) x := by
        simp [Function.iterate_succ]
      rw [this]
      exact hg''_nonpos x)
  -- A positive concave function on ℝ is constant.
  have hg_const : ∀ a b, g a = g b := by
    intro a b
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · -- Case g a < g b.
      rcases lt_trichotomy a b with hab | hab | hab
      · -- a < b. Extrapolate left.
        set s : ℝ := (g b - g a) / (b - a) with hs_def
        have hs_pos : 0 < s := div_pos (by linarith) (by linarith)
        have hs_ne : s ≠ 0 := ne_of_gt hs_pos
        set N : ℝ := g a / s + 1 with hN_def
        have hN_pos : 0 < N := by
          have hga : 0 < g a := hg_pos a
          have hdiv : 0 ≤ g a / s := div_nonneg hga.le hs_pos.le
          linarith
        set u : ℝ := a - N with hu_def
        have hua : u < a := by simp [hu_def]; linarith
        have hconc := hg_concave.slope_anti_adjacent (mem_univ u) (mem_univ b) hua hab
        have hau_pos : 0 < a - u := by simp [hu_def]; linarith
        have h1 : s ≤ (g a - g u) / (a - u) := hconc
        have hu_eq : a - u = N := by simp [hu_def]
        rw [hu_eq] at h1
        have h2 : s * N ≤ g a - g u := (le_div_iff₀ hN_pos).mp h1
        have h3 : s * N = g a + s := by
          rw [hN_def, mul_add, mul_one]
          have hcancel : s * (g a / s) = g a := mul_div_cancel₀ (g a) hs_ne
          linarith [hcancel]
        have h4 : g u ≤ -s := by linarith
        exact absurd (lt_of_le_of_lt h4 (by linarith : -s < 0)) (not_lt.mpr (hg_pos u).le)
      · exact hne' (by rw [hab])
      · -- b < a, but g a < g b. Extrapolate right of a.
        set s : ℝ := (g a - g b) / (a - b) with hs_def
        have hs_neg : s < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
        have hnegs_pos : 0 < -s := by linarith
        have hnegs_ne : -s ≠ 0 := ne_of_gt hnegs_pos
        set N : ℝ := g a / (-s) + 1 with hN_def
        have hN_pos : 0 < N := by
          have hga : 0 < g a := hg_pos a
          have hdiv : 0 ≤ g a / (-s) := div_nonneg hga.le hnegs_pos.le
          linarith
        set v : ℝ := a + N with hv_def
        have hav : a < v := by simp [hv_def]; linarith
        have hconc := hg_concave.slope_anti_adjacent (mem_univ b) (mem_univ v) hab hav
        have hva_pos : 0 < v - a := by simp [hv_def]; linarith
        have h1 : (g v - g a) / (v - a) ≤ s := hconc
        have hv_eq : v - a = N := by simp [hv_def]
        rw [hv_eq] at h1
        have h2 : g v - g a ≤ s * N := (div_le_iff₀ hN_pos).mp h1
        have hnegs_ne : -s ≠ 0 := ne_of_gt hnegs_pos
        have h3 : s * N = -g a + s := by
          rw [hN_def, mul_add, mul_one]
          have hcancel : -s * (g a / (-s)) = g a := mul_div_cancel₀ (g a) hnegs_ne
          have : s * (g a / (-s)) = -g a := by linarith [hcancel]
          linarith [this]
        have h4 : g v ≤ s := by linarith
        exact absurd (lt_of_le_of_lt h4 hs_neg) (not_lt.mpr (hg_pos v).le)
    · -- Case g a > g b (symmetric).
      rcases lt_trichotomy a b with hab | hab | hab
      · -- a < b, g a > g b. Extrapolate right of b.
        set s : ℝ := (g b - g a) / (b - a) with hs_def
        have hs_neg : s < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
        have hnegs_pos : 0 < -s := by linarith
        set N : ℝ := g b / (-s) + 1 with hN_def
        have hN_pos : 0 < N := by
          have hgb : 0 < g b := hg_pos b
          have hdiv : 0 ≤ g b / (-s) := div_nonneg hgb.le hnegs_pos.le
          linarith
        set v : ℝ := b + N with hv_def
        have hbv : b < v := by simp [hv_def]; linarith
        have hconc := hg_concave.slope_anti_adjacent (mem_univ a) (mem_univ v) hab hbv
        have hvb_pos : 0 < v - b := by simp [hv_def]; linarith
        have h1 : (g v - g b) / (v - b) ≤ s := hconc
        have hv_eq : v - b = N := by simp [hv_def]
        rw [hv_eq] at h1
        have h2 : g v - g b ≤ s * N := (div_le_iff₀ hN_pos).mp h1
        have hnegs_ne : -s ≠ 0 := ne_of_gt hnegs_pos
        have h3 : s * N = -g b + s := by
          rw [hN_def, mul_add, mul_one]
          have hcancel : -s * (g b / (-s)) = g b := mul_div_cancel₀ (g b) hnegs_ne
          have : s * (g b / (-s)) = -g b := by linarith [hcancel]
          linarith [this]
        have h4 : g v ≤ s := by linarith
        exact absurd (lt_of_le_of_lt h4 hs_neg) (not_lt.mpr (hg_pos v).le)
      · exact hne' (by rw [hab])
      · -- b < a, g a > g b. Extrapolate left of b.
        set s : ℝ := (g a - g b) / (a - b) with hs_def
        have hs_pos : 0 < s := div_pos (by linarith) (by linarith)
        have hs_ne : s ≠ 0 := ne_of_gt hs_pos
        set N : ℝ := g b / s + 1 with hN_def
        have hN_pos : 0 < N := by
          have hgb : 0 < g b := hg_pos b
          have hdiv : 0 ≤ g b / s := div_nonneg hgb.le hs_pos.le
          linarith
        set u : ℝ := b - N with hu_def
        have hub : u < b := by simp [hu_def]; linarith
        have hconc := hg_concave.slope_anti_adjacent (mem_univ u) (mem_univ a) hub hab
        have hbu_pos : 0 < b - u := by simp [hu_def]; linarith
        have h1 : s ≤ (g b - g u) / (b - u) := hconc
        have hu_eq : b - u = N := by simp [hu_def]
        rw [hu_eq] at h1
        have h2 : s * N ≤ g b - g u := (le_div_iff₀ hN_pos).mp h1
        have h3 : s * N = g b + s := by
          rw [hN_def, mul_add, mul_one]
          have hcancel : s * (g b / s) = g b := mul_div_cancel₀ (g b) hs_ne
          linarith [hcancel]
        have h4 : g u ≤ -s := by linarith
        exact absurd (lt_of_le_of_lt h4 (by linarith : -s < 0)) (not_lt.mpr (hg_pos u).le)
  -- So g is constant. f x = f 0.
  refine ⟨f 0, hpos 0, fun x => ?_⟩
  have hg_eq : g x = g 0 := hg_const x 0
  have hfx_inv : (f x)⁻¹ = (f 0)⁻¹ := hg_eq
  exact inv_injective hfx_inv

end Imc2020P5
