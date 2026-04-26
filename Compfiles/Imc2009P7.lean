/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2009, Problem 7
(Day 2, Problem 2)

Suppose `f : ℝ → ℝ` is `C²` with `f(0) = 1`, `f'(0) = 0`, and
`f''(x) - 5 f'(x) + 6 f(x) ≥ 0` on `[0, ∞)`. Prove that
`f(x) ≥ 3 e^{2x} - 2 e^{3x}` for all `x ≥ 0`.

## Solution sketch

Let `g(x) = f'(x) - 2 f(x)`. Then
`g'(x) - 3 g(x) = f''(x) - 5 f'(x) + 6 f(x) ≥ 0`.
So `(g(x) e^{-3x})' = (g'(x) - 3 g(x)) e^{-3x} ≥ 0`, hence `g(x) e^{-3x}` is
monotone non-decreasing on `[0, ∞)`. Its value at `0` is
`g(0) = f'(0) - 2 f(0) = -2`, so `g(x) ≥ -2 e^{3x}`.

Now let `p(x) = f(x) e^{-2x} + 2 e^x`. Then
`p'(x) = (f'(x) - 2 f(x)) e^{-2x} + 2 e^x = g(x) e^{-2x} + 2 e^x
  ≥ -2 e^x + 2 e^x = 0`.
So `p` is monotone non-decreasing on `[0, ∞)`, thus `p(x) ≥ p(0) = 1 + 2 = 3`,
i.e., `f(x) e^{-2x} ≥ 3 - 2 e^x`, i.e., `f(x) ≥ 3 e^{2x} - 2 e^{3x}`.
-/

namespace Imc2009P7

open Real Set

snip begin

/-- `f` has a derivative at every point if `ContDiff ℝ 2 f`. -/
lemma hasDerivAt_of_contDiff2 {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    HasDerivAt f (deriv f x) x :=
  (hf.differentiable (by decide) x).hasDerivAt

/-- `deriv f` has a derivative at every point if `ContDiff ℝ 2 f`. -/
lemma hasDerivAt_deriv_of_contDiff2 {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    HasDerivAt (deriv f) (iteratedDeriv 2 f x) x := by
  have h2 : Differentiable ℝ (deriv f) := hf.differentiable_deriv_two
  have h3 : HasDerivAt (deriv f) (deriv (deriv f) x) x := (h2 x).hasDerivAt
  have heq : iteratedDeriv 2 f = deriv (deriv f) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [heq]; exact h3

snip end

problem imc2009_p7 (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hf0 : f 0 = 1) (hf'0 : deriv f 0 = 0)
    (hineq : ∀ x, 0 ≤ x → iteratedDeriv 2 f x - 5 * deriv f x + 6 * f x ≥ 0) :
    ∀ x, 0 ≤ x → f x ≥ 3 * Real.exp (2 * x) - 2 * Real.exp (3 * x) := by
  intro x hx
  -- f has a derivative everywhere.
  have hf_deriv : ∀ y, HasDerivAt f (deriv f y) y := hasDerivAt_of_contDiff2 hf
  -- deriv f has a derivative everywhere.
  have hdf_deriv : ∀ y, HasDerivAt (deriv f) (iteratedDeriv 2 f y) y :=
    hasDerivAt_deriv_of_contDiff2 hf
  -- Step 1: Show `h(x) := (deriv f x - 2 * f x) * exp (-3 x) ≥ -2` for x ≥ 0.
  set h : ℝ → ℝ := fun y => (deriv f y - 2 * f y) * Real.exp (-3 * y) with hh_def
  have hh0 : h 0 = -2 := by
    simp only [h, hf0, hf'0]; simp
  have hh_deriv : ∀ y, HasDerivAt h
      ((iteratedDeriv 2 f y - 5 * deriv f y + 6 * f y) * Real.exp (-3 * y)) y := by
    intro y
    -- d/dy [(f'(y) - 2 f(y)) e^{-3y}] =
    --   (f''(y) - 2 f'(y)) e^{-3y} + (f'(y) - 2 f(y)) * (-3) e^{-3y}.
    have h1 : HasDerivAt (fun y => deriv f y - 2 * f y)
        (iteratedDeriv 2 f y - 2 * deriv f y) y :=
      (hdf_deriv y).sub ((hf_deriv y).const_mul 2)
    have h2 : HasDerivAt (fun y => Real.exp (-3 * y)) (-3 * Real.exp (-3 * y)) y := by
      have hid : HasDerivAt (fun y : ℝ => -3 * y) (-3) y := by
        have := (hasDerivAt_id y).const_mul (-3)
        simpa using this
      have := hid.exp
      convert this using 1
      ring
    have h3 := h1.mul h2
    convert h3 using 1
    ring
  -- h is non-decreasing on [0, ∞) because its derivative is nonneg.
  have hh_mono : MonotoneOn h (Ici (0 : ℝ)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · intro y _
      exact (hh_deriv y).continuousAt.continuousWithinAt
    · intro y _
      exact (hh_deriv y).hasDerivWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hy' : 0 ≤ y := le_of_lt hy
      have := hineq y hy'
      have hexp_pos : 0 < Real.exp (-3 * y) := Real.exp_pos _
      exact mul_nonneg this hexp_pos.le
  -- So h x ≥ h 0 = -2 for x ≥ 0.
  have hhx : h x ≥ -2 := by
    have := hh_mono (self_mem_Ici) hx hx
    rw [hh0] at this; exact this
  -- Rearrange: deriv f x - 2 * f x ≥ -2 * exp (3 * x).
  have hg_bound : deriv f x - 2 * f x ≥ -2 * Real.exp (3 * x) := by
    have hexp_pos : 0 < Real.exp (-3 * x) := Real.exp_pos _
    have : (deriv f x - 2 * f x) * Real.exp (-3 * x) ≥ -2 := hhx
    have hm : (deriv f x - 2 * f x) * Real.exp (-3 * x) * Real.exp (3 * x) ≥
        -2 * Real.exp (3 * x) := by
      have hexp3_pos : 0 < Real.exp (3 * x) := Real.exp_pos _
      exact mul_le_mul_of_nonneg_right this hexp3_pos.le
    have heq : Real.exp (-3 * x) * Real.exp (3 * x) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    calc deriv f x - 2 * f x
        = (deriv f x - 2 * f x) * 1 := by ring
      _ = (deriv f x - 2 * f x) * (Real.exp (-3 * x) * Real.exp (3 * x)) := by rw [heq]
      _ = (deriv f x - 2 * f x) * Real.exp (-3 * x) * Real.exp (3 * x) := by ring
      _ ≥ -2 * Real.exp (3 * x) := hm
  -- Step 2: Show `p(x) := f(x) * exp(-2x) + 2 * exp(x) ≥ 3` for x ≥ 0.
  set p : ℝ → ℝ := fun y => f y * Real.exp (-2 * y) + 2 * Real.exp y with hp_def
  have hp0 : p 0 = 3 := by
    simp only [p, hf0]
    simp
    norm_num
  -- p'(y) = (f'(y) - 2 f(y)) * exp(-2y) + 2 * exp(y).
  have hp_deriv : ∀ y, HasDerivAt p
      ((deriv f y - 2 * f y) * Real.exp (-2 * y) + 2 * Real.exp y) y := by
    intro y
    -- d/dy [f y * exp(-2y)] = f' y * exp(-2y) + f y * (-2) * exp(-2y)
    --                      = (f' y - 2 f y) * exp(-2y).
    have h2exp : HasDerivAt (fun y => Real.exp (-2 * y)) (-2 * Real.exp (-2 * y)) y := by
      have hid : HasDerivAt (fun y : ℝ => -2 * y) (-2) y := by
        have := (hasDerivAt_id y).const_mul (-2)
        simpa using this
      have := hid.exp
      convert this using 1
      ring
    have hfe : HasDerivAt (fun y => f y * Real.exp (-2 * y))
        ((deriv f y - 2 * f y) * Real.exp (-2 * y)) y := by
      have := (hf_deriv y).mul h2exp
      convert this using 1
      ring
    have hexp : HasDerivAt (fun y => 2 * Real.exp y) (2 * Real.exp y) y := by
      have := (Real.hasDerivAt_exp y).const_mul 2
      simpa using this
    exact hfe.add hexp
  -- p is non-decreasing on [0, ∞).
  have hp_mono : MonotoneOn p (Ici (0 : ℝ)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · intro y _
      exact (hp_deriv y).continuousAt.continuousWithinAt
    · intro y _
      exact (hp_deriv y).hasDerivWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hy' : 0 ≤ y := le_of_lt hy
      -- Need: 0 ≤ (deriv f y - 2 f y) * exp(-2y) + 2 exp y.
      -- From step 1 applied at y: deriv f y - 2 f y ≥ -2 * exp(3y).
      have hbdy : deriv f y - 2 * f y ≥ -2 * Real.exp (3 * y) := by
        -- redo the argument using y in place of x.
        have hhy : h y ≥ -2 := by
          have := hh_mono (self_mem_Ici) hy' hy'
          rw [hh0] at this; exact this
        have hexp3_pos : 0 < Real.exp (3 * y) := Real.exp_pos _
        have hm : (deriv f y - 2 * f y) * Real.exp (-3 * y) * Real.exp (3 * y) ≥
            -2 * Real.exp (3 * y) :=
          mul_le_mul_of_nonneg_right hhy hexp3_pos.le
        have heqexp : Real.exp (-3 * y) * Real.exp (3 * y) = 1 := by
          rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
        calc deriv f y - 2 * f y
            = (deriv f y - 2 * f y) * 1 := by ring
          _ = (deriv f y - 2 * f y) * (Real.exp (-3 * y) * Real.exp (3 * y)) := by rw [heqexp]
          _ = (deriv f y - 2 * f y) * Real.exp (-3 * y) * Real.exp (3 * y) := by ring
          _ ≥ -2 * Real.exp (3 * y) := hm
      -- Now (deriv f y - 2 f y) * exp(-2y) ≥ -2 * exp(3y) * exp(-2y) = -2 * exp(y).
      have hexp2_pos : 0 < Real.exp (-2 * y) := Real.exp_pos _
      have hexp_y_pos : 0 < Real.exp y := Real.exp_pos _
      have hineq1 : (deriv f y - 2 * f y) * Real.exp (-2 * y) ≥
          (-2 * Real.exp (3 * y)) * Real.exp (-2 * y) :=
        mul_le_mul_of_nonneg_right hbdy hexp2_pos.le
      have heqsimp : (-2 * Real.exp (3 * y)) * Real.exp (-2 * y) = -2 * Real.exp y := by
        rw [show (-2 * Real.exp (3 * y)) * Real.exp (-2 * y)
            = -2 * (Real.exp (3 * y) * Real.exp (-2 * y)) from by ring]
        rw [← Real.exp_add]
        ring_nf
      linarith [hineq1, heqsimp]
  -- p x ≥ p 0 = 3.
  have hpx : p x ≥ 3 := by
    have := hp_mono (self_mem_Ici) hx hx
    rw [hp0] at this; exact this
  -- Rearrange p x ≥ 3 into f x ≥ 3 exp(2x) - 2 exp(3x).
  -- p x = f x * exp(-2x) + 2 exp x ≥ 3.
  -- Multiply by exp(2x): f x + 2 exp(3x) ≥ 3 exp(2x).
  have hexp2x_pos : 0 < Real.exp (2 * x) := Real.exp_pos _
  have hmult : (f x * Real.exp (-2 * x) + 2 * Real.exp x) * Real.exp (2 * x) ≥
      3 * Real.exp (2 * x) :=
    mul_le_mul_of_nonneg_right hpx hexp2x_pos.le
  have heq1 : Real.exp (-2 * x) * Real.exp (2 * x) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have heq2 : Real.exp x * Real.exp (2 * x) = Real.exp (3 * x) := by
    rw [← Real.exp_add]; ring_nf
  have : (f x * Real.exp (-2 * x) + 2 * Real.exp x) * Real.exp (2 * x)
      = f x + 2 * Real.exp (3 * x) := by
    calc (f x * Real.exp (-2 * x) + 2 * Real.exp x) * Real.exp (2 * x)
        = f x * (Real.exp (-2 * x) * Real.exp (2 * x))
          + 2 * (Real.exp x * Real.exp (2 * x)) := by ring
      _ = f x * 1 + 2 * Real.exp (3 * x) := by rw [heq1, heq2]
      _ = f x + 2 * Real.exp (3 * x) := by ring
  rw [this] at hmult
  linarith

end Imc2009P7
