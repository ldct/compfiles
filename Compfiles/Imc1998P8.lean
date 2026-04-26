/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1998, Problem 8 (Day 2, Problem 2)

Let `𝒫` denote the set of cubic polynomials
`f(x) = a₀ + a₁ x + a₂ x² + a₃ x³` with real coefficients satisfying
`|f(±1)| ≤ 1` and `|f(±1/2)| ≤ 1`. Determine

  `sup_{f ∈ 𝒫}  max_{x ∈ [-1, 1]} |f''(x)|`

and the polynomials achieving this supremum.

## Answer

The supremum equals `24`, attained (for example) by the Chebyshev polynomial
`T₃(x) = 4 x³ − 3 x`.

## Solution sketch

Since `f` has degree at most `3`, `f''(x) = 2 a₂ + 6 a₃ x` is linear, so its
maximum on `[-1, 1]` is `max(|2 a₂ + 6 a₃|, |2 a₂ - 6 a₃|) = |f''(±1)|`.

We use Lagrange-style interpolation at the four nodes `-1, -1/2, 1/2, 1`. The
identity (verified by expanding the linear form on `(a₀, a₁, a₂, a₃)`)

  `2 a₂ + 6 a₃
    = (16/3) f(1) - (8/3) f(-1) - (28/3) f(1/2) + (20/3) f(-1/2)`

gives, by the triangle inequality,

  `|2 a₂ + 6 a₃| ≤ (16 + 8 + 28 + 20)/3 = 24`.

Replacing `x` by `-x` (i.e. swapping `a₃ ↔ -a₃`, `a₁ ↔ -a₁`) gives the same
bound for `|2 a₂ - 6 a₃|`.

For attainment, take `T₃(x) = 4 x³ - 3 x`: its values at `±1, ±1/2` are
`±1, ∓1` (all in `[-1, 1]`) and `T₃''(1) = 24`.
-/

namespace Imc1998P8

open scoped BigOperators

/-- The set of admissible cubic polynomials, parametrised by their coefficients
`(a₀, a₁, a₂, a₃)`. -/
def Admissible (a₀ a₁ a₂ a₃ : ℝ) : Prop :=
  |a₀ + a₁ + a₂ + a₃| ≤ 1 ∧
  |a₀ - a₁ + a₂ - a₃| ≤ 1 ∧
  |a₀ + a₁/2 + a₂/4 + a₃/8| ≤ 1 ∧
  |a₀ - a₁/2 + a₂/4 - a₃/8| ≤ 1

/-- The cubic polynomial `f(x) = a₀ + a₁ x + a₂ x² + a₃ x³`. -/
def poly (a₀ a₁ a₂ a₃ x : ℝ) : ℝ := a₀ + a₁ * x + a₂ * x^2 + a₃ * x^3

/-- Its second derivative `f''(x) = 2 a₂ + 6 a₃ x`. -/
def poly'' (a₂ a₃ x : ℝ) : ℝ := 2 * a₂ + 6 * a₃ * x

/-- The answer: the supremum equals `24`. -/
determine answer : ℝ := 24

/-- Key lemma: for an admissible cubic, `|f''(1)| ≤ 24`. -/
lemma abs_second_deriv_at_one_le
    (a₀ a₁ a₂ a₃ : ℝ) (h : Admissible a₀ a₁ a₂ a₃) :
    |2 * a₂ + 6 * a₃| ≤ 24 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  -- The identity: 2 a₂ + 6 a₃ = (16/3) (a₀+a₁+a₂+a₃) - (8/3) (a₀-a₁+a₂-a₃)
  --                               - (28/3) (a₀+a₁/2+a₂/4+a₃/8)
  --                               + (20/3) (a₀-a₁/2+a₂/4-a₃/8)
  have key : 2 * a₂ + 6 * a₃ =
      (16/3) * (a₀ + a₁ + a₂ + a₃)
      + (-(8/3)) * (a₀ - a₁ + a₂ - a₃)
      + (-(28/3)) * (a₀ + a₁/2 + a₂/4 + a₃/8)
      + (20/3) * (a₀ - a₁/2 + a₂/4 - a₃/8) := by ring
  rw [key]
  have e1 : |(16/3 : ℝ) * (a₀ + a₁ + a₂ + a₃)| ≤ 16/3 := by
    rw [abs_mul, show |(16/3 : ℝ)| = 16/3 from abs_of_pos (by norm_num)]
    have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 16/3)
    linarith
  have e2 : |(-(8/3) : ℝ) * (a₀ - a₁ + a₂ - a₃)| ≤ 8/3 := by
    rw [abs_mul, show |(-(8/3) : ℝ)| = 8/3 from by rw [abs_neg]; exact abs_of_pos (by norm_num)]
    have := mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 8/3)
    linarith
  have e3 : |(-(28/3) : ℝ) * (a₀ + a₁/2 + a₂/4 + a₃/8)| ≤ 28/3 := by
    rw [abs_mul, show |(-(28/3) : ℝ)| = 28/3 from by rw [abs_neg]; exact abs_of_pos (by norm_num)]
    have := mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 28/3)
    linarith
  have e4 : |(20/3 : ℝ) * (a₀ - a₁/2 + a₂/4 - a₃/8)| ≤ 20/3 := by
    rw [abs_mul, show |(20/3 : ℝ)| = 20/3 from abs_of_pos (by norm_num)]
    have := mul_le_mul_of_nonneg_left h4 (by norm_num : (0:ℝ) ≤ 20/3)
    linarith
  calc |(16/3) * (a₀ + a₁ + a₂ + a₃)
        + (-(8/3)) * (a₀ - a₁ + a₂ - a₃)
        + (-(28/3)) * (a₀ + a₁/2 + a₂/4 + a₃/8)
        + (20/3) * (a₀ - a₁/2 + a₂/4 - a₃/8)|
      ≤ |(16/3) * (a₀ + a₁ + a₂ + a₃)
          + (-(8/3)) * (a₀ - a₁ + a₂ - a₃)
          + (-(28/3)) * (a₀ + a₁/2 + a₂/4 + a₃/8)|
        + |(20/3) * (a₀ - a₁/2 + a₂/4 - a₃/8)| := abs_add_le _ _
    _ ≤ (|(16/3) * (a₀ + a₁ + a₂ + a₃)
          + (-(8/3)) * (a₀ - a₁ + a₂ - a₃)|
        + |(-(28/3)) * (a₀ + a₁/2 + a₂/4 + a₃/8)|)
        + |(20/3) * (a₀ - a₁/2 + a₂/4 - a₃/8)| := by
            gcongr
            exact abs_add_le _ _
    _ ≤ ((|(16/3) * (a₀ + a₁ + a₂ + a₃)|
          + |(-(8/3)) * (a₀ - a₁ + a₂ - a₃)|)
        + |(-(28/3)) * (a₀ + a₁/2 + a₂/4 + a₃/8)|)
        + |(20/3) * (a₀ - a₁/2 + a₂/4 - a₃/8)| := by
            gcongr
            exact abs_add_le _ _
    _ ≤ 16/3 + 8/3 + 28/3 + 20/3 := by linarith
    _ = 24 := by norm_num

/-- The admissibility predicate is invariant under the substitution `x ↦ -x`,
which negates `a₁` and `a₃`. -/
lemma admissible_neg
    (a₀ a₁ a₂ a₃ : ℝ) (h : Admissible a₀ a₁ a₂ a₃) :
    Admissible a₀ (-a₁) a₂ (-a₃) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : a₀ + -a₁ + a₂ + -a₃ = a₀ - a₁ + a₂ - a₃ := by ring
    rw [this]; exact h2
  · have : a₀ - -a₁ + a₂ - -a₃ = a₀ + a₁ + a₂ + a₃ := by ring
    rw [this]; exact h1
  · have : a₀ + -a₁/2 + a₂/4 + -a₃/8 = a₀ - a₁/2 + a₂/4 - a₃/8 := by ring
    rw [this]; exact h4
  · have : a₀ - -a₁/2 + a₂/4 - -a₃/8 = a₀ + a₁/2 + a₂/4 + a₃/8 := by ring
    rw [this]; exact h3

/-- For an admissible cubic, `|f''(-1)| ≤ 24`. Reduces to the previous lemma
applied to the polynomial `f(-x)`. -/
lemma abs_second_deriv_at_neg_one_le
    (a₀ a₁ a₂ a₃ : ℝ) (h : Admissible a₀ a₁ a₂ a₃) :
    |2 * a₂ - 6 * a₃| ≤ 24 := by
  have h' := abs_second_deriv_at_one_le a₀ (-a₁) a₂ (-a₃) (admissible_neg _ _ _ _ h)
  have heq : 2 * a₂ + 6 * (-a₃) = 2 * a₂ - 6 * a₃ := by ring
  rw [heq] at h'
  exact h'

/-- For an admissible cubic, the second derivative is bounded by `24` on
`[-1, 1]`. -/
lemma abs_second_deriv_le
    (a₀ a₁ a₂ a₃ : ℝ) (h : Admissible a₀ a₁ a₂ a₃)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |poly'' a₂ a₃ x| ≤ 24 := by
  obtain ⟨hxl, hxr⟩ := hx
  -- Since `f''` is linear in `x`, its maximum on `[-1,1]` is at `±1`.
  -- Write `x = (1+x)/2 · 1 + (1-x)/2 · (-1)` (convex combination).
  unfold poly''
  have hx1 : (1 + x) / 2 ≥ 0 := by linarith
  have hx2 : (1 - x) / 2 ≥ 0 := by linarith
  have hx3 : (1 + x) / 2 + (1 - x) / 2 = 1 := by ring
  have key : 2 * a₂ + 6 * a₃ * x =
      ((1 + x) / 2) * (2 * a₂ + 6 * a₃) + ((1 - x) / 2) * (2 * a₂ - 6 * a₃) := by
    ring
  rw [key]
  calc |((1 + x) / 2) * (2 * a₂ + 6 * a₃) + ((1 - x) / 2) * (2 * a₂ - 6 * a₃)|
      ≤ |((1 + x) / 2) * (2 * a₂ + 6 * a₃)| + |((1 - x) / 2) * (2 * a₂ - 6 * a₃)| :=
        abs_add_le _ _
    _ = ((1 + x) / 2) * |2 * a₂ + 6 * a₃| + ((1 - x) / 2) * |2 * a₂ - 6 * a₃| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hx1, abs_of_nonneg hx2]
    _ ≤ ((1 + x) / 2) * 24 + ((1 - x) / 2) * 24 := by
        gcongr
        · exact abs_second_deriv_at_one_le _ _ _ _ h
        · exact abs_second_deriv_at_neg_one_le _ _ _ _ h
    _ = 24 := by linarith

/-- The Chebyshev polynomial `T₃(x) = 4 x³ - 3 x`, given by coefficients
`a₀ = 0, a₁ = -3, a₂ = 0, a₃ = 4`, is admissible. -/
lemma chebyshev_admissible : Admissible 0 (-3) 0 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-- The second derivative of the Chebyshev polynomial at `1` is `24`,
witnessing the bound. -/
lemma chebyshev_second_deriv_at_one : poly'' 0 4 1 = 24 := by
  unfold poly''; norm_num

/-- IMC 1998 Problem 8: the supremum of `max_{x ∈ [-1,1]} |f''(x)|` over the
admissible set `𝒫` equals `24`.

We state the result as the conjunction of:

* the upper bound: every admissible cubic satisfies `|f''(x)| ≤ 24` on
  `[-1, 1]`;

* attainment: the Chebyshev polynomial `T₃(x) = 4 x³ - 3 x` is admissible and
  satisfies `|T₃''(1)| = 24`.
-/
problem imc1998_p8 :
    (∀ a₀ a₁ a₂ a₃ : ℝ, Admissible a₀ a₁ a₂ a₃ →
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, |poly'' a₂ a₃ x| ≤ answer) ∧
    (∃ a₀ a₁ a₂ a₃ : ℝ, Admissible a₀ a₁ a₂ a₃ ∧
      ∃ x ∈ Set.Icc (-1 : ℝ) 1, |poly'' a₂ a₃ x| = answer) := by
  refine ⟨?_, ?_⟩
  · intro a₀ a₁ a₂ a₃ h x hx
    exact abs_second_deriv_le a₀ a₁ a₂ a₃ h hx
  · refine ⟨0, -3, 0, 4, chebyshev_admissible, 1, ?_, ?_⟩
    · exact ⟨by norm_num, le_refl _⟩
    · rw [chebyshev_second_deriv_at_one]; norm_num

end Imc1998P8
