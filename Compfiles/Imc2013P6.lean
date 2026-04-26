/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2013, Problem 6

Let `z` be a complex number with `|z + 1| > 2`. Prove that `|z^3 + 1| > 1`.
-/

namespace Imc2013P6

open Complex

snip begin

/--
Key algebraic identity: if `w = x + iy` is a complex number with
`|w|^2 = r2 = x^2 + y^2`, then
`|w^2 - 3w + 3|^2 = 12 * (x - (r2 + 3)/4)^2 + (r2 - 3)^2 / 4`.
This is verified as a polynomial identity in `x, y, r2` using `y^2 = r2 - x^2`.
-/
lemma normSq_w2_sub_3w_add_3 (w : ℂ) :
    Complex.normSq (w^2 - 3*w + 3) =
      12 * (w.re - (Complex.normSq w + 3) / 4)^2 + (Complex.normSq w - 3)^2 / 4 := by
  -- Expand |w^2 - 3w + 3|^2 = A^2 + B^2 in terms of x = w.re, y = w.im.
  -- A = x^2 - y^2 - 3x + 3, B = 2xy - 3y.
  -- Then substitute y^2 = (normSq w) - x^2.
  -- Replace (3 : ℂ) with ((3 : ℝ) : ℂ) so real/imag parts compute directly.
  have h3 : (3 : ℂ) = ((3 : ℝ) : ℂ) := by norm_cast
  rw [h3]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
             Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
             Complex.ofReal_re, Complex.ofReal_im, pow_two]
  set x := w.re
  set y := w.im
  ring

/-- From `|w|^2 > 4` we get `|w^2 - 3w + 3|^2 > 1/4`. -/
lemma normSq_lower_bound {w : ℂ} (hw : 4 < Complex.normSq w) :
    1/4 < Complex.normSq (w^2 - 3*w + 3) := by
  rw [normSq_w2_sub_3w_add_3]
  -- 12 * (...)^2 ≥ 0
  have h1 : 0 ≤ 12 * (w.re - (Complex.normSq w + 3) / 4)^2 := by positivity
  -- (|w|^2 - 3)^2 / 4 > 1/4 since |w|^2 > 4 implies |w|^2 - 3 > 1, so squared > 1.
  have h2 : 1/4 < (Complex.normSq w - 3)^2 / 4 := by
    have h3 : 1 < Complex.normSq w - 3 := by linarith
    have h4 : (1 : ℝ) < (Complex.normSq w - 3)^2 := by nlinarith
    linarith
  linarith

snip end

problem imc2013_p6 (z : ℂ) (hz : 2 < ‖z + 1‖) : 1 < ‖z^3 + 1‖ := by
  -- Set w = z + 1, so |w| > 2 and z = w - 1.
  set w : ℂ := z + 1 with hw_def
  have hz_eq : z = w - 1 := by rw [hw_def]; ring
  -- Factor: z^3 + 1 = (z+1)(z^2 - z + 1) = w * (w^2 - 3w + 3).
  have hfact : z^3 + 1 = w * (w^2 - 3*w + 3) := by rw [hz_eq]; ring
  rw [hfact]
  rw [norm_mul]
  -- |w| > 2.
  have hw_norm : 2 < ‖w‖ := hz
  -- |w^2 - 3w + 3| > 1/2.
  have hw_normSq : 4 < Complex.normSq w := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hw_norm, norm_nonneg w]
  have hq_normSq : 1/4 < Complex.normSq (w^2 - 3*w + 3) := normSq_lower_bound hw_normSq
  have hq_norm : 1/2 < ‖w^2 - 3*w + 3‖ := by
    have h1 : Complex.normSq (w^2 - 3*w + 3) = ‖w^2 - 3*w + 3‖^2 := Complex.normSq_eq_norm_sq _
    have hnn : 0 ≤ ‖w^2 - 3*w + 3‖ := norm_nonneg _
    nlinarith [h1, hq_normSq, hnn]
  -- Combine: |w| * |w^2 - 3w + 3| > 2 * (1/2) = 1.
  have hw_nn : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
  nlinarith [hw_norm, hq_norm, hw_nn, norm_nonneg (w^2 - 3*w + 3)]

end Imc2013P6
