/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1999, Problem 7 (Day 2, Problem 1)

In a (not necessarily commutative) ring `R`, the square of every element is
zero. Prove that `a*b*c + a*b*c = 0` for all `a, b, c ∈ R`.

## Solution sketch (official solution)

From `(a+b)^2 = 0`, expanding yields `a*b + b*a = 0`, i.e. `a*b = -(b*a)`.
Applying this anticommutativity three times:
`a*b*c = a*(b*c) = -(b*c)*a = -b*(c*a) = (c*a)*b = c*(a*b) = -(a*b)*c = -a*b*c`.
So `2 * a*b*c = 0`, equivalently `a*b*c + a*b*c = 0`.
-/

namespace Imc1999P7

snip begin

/-- In a ring where every element squares to zero, multiplication is
anticommutative: `a*b + b*a = 0`. -/
lemma anticomm_add {R : Type*} [Ring R] (h : ∀ x : R, x * x = 0) (a b : R) :
    a * b + b * a = 0 := by
  have hab : (a + b) * (a + b) = 0 := h (a + b)
  have ha : a * a = 0 := h a
  have hb : b * b = 0 := h b
  have expand : (a + b) * (a + b) = a * a + a * b + b * a + b * b := by
    noncomm_ring
  rw [expand, ha, hb] at hab
  -- hab : 0 + a * b + b * a + 0 = 0
  simpa using hab

snip end

problem imc1999_p7 {R : Type*} [Ring R] (h : ∀ x : R, x * x = 0)
    (a b c : R) : a * b * c + a * b * c = 0 := by
  -- Apply anticomm_add to (a, b*c): a*(b*c) + (b*c)*a = 0, i.e. abc + bca = 0.
  have hA : a * b * c + b * c * a = 0 := by
    have := anticomm_add h a (b * c)
    have e1 : a * (b * c) = a * b * c := by noncomm_ring
    have e2 : b * c * a = b * c * a := rfl
    rw [e1] at this
    exact this
  -- Apply anticomm_add to (b, c*a): b*(c*a) + (c*a)*b = 0, i.e. bca + cab = 0.
  have hB : b * c * a + c * a * b = 0 := by
    have := anticomm_add h b (c * a)
    have e : b * (c * a) = b * c * a := by noncomm_ring
    rw [e] at this
    exact this
  -- Apply anticomm_add to (c, a*b): c*(a*b) + (a*b)*c = 0, i.e. cab + abc = 0.
  have hC : c * a * b + a * b * c = 0 := by
    have := anticomm_add h c (a * b)
    have e : c * (a * b) = c * a * b := by noncomm_ring
    rw [e] at this
    exact this
  -- From hB: b*c*a + c*a*b = 0, so c*a*b = -(b*c*a).
  have hcab : c * a * b = -(b * c * a) := eq_neg_of_add_eq_zero_right hB
  -- Substitute into hC: cab + abc = 0 → -(bca) + abc = 0 → abc = bca.
  have habc_eq : a * b * c = b * c * a := by
    rw [hcab] at hC
    -- hC : -(b * c * a) + a * b * c = 0
    have := neg_add_eq_zero.mp hC
    -- this : b * c * a = a * b * c
    exact this.symm
  -- Substitute into hA: abc + bca = 0 → abc + abc = 0.
  rw [habc_eq]
  rw [habc_eq] at hA
  exact hA

end Imc1999P7
