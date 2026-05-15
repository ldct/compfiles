/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2001, Problem 12
(IMC 2001, Day 2, Problem 6)

For each positive integer `n`, let
  `f n θ = sin θ · sin (2 θ) · sin (4 θ) · ⋯ · sin (2^n θ)`.
For all real `θ` and all `n`, prove that
  `|f n θ| ≤ (2 / √3) · |f n (π/3)|`.

Note that `|sin (2^k · π / 3)| = √3 / 2` for every `k ≥ 0` (since `2^k mod 3 ∈ {1, 2}`),
hence `|f n (π / 3)| = (√3 / 2) ^ (n + 1)` and the bound is equivalent to
`|f n θ| ≤ (√3 / 2) ^ n`.
-/

namespace Imc2001P12

open Real BigOperators

/-- The product `sin θ · sin(2θ) · sin(4θ) · ⋯ · sin(2^n θ)` (a product of `n + 1` factors). -/
noncomputable def f (n : ℕ) (θ : ℝ) : ℝ :=
  ∏ k ∈ Finset.range (n + 1), Real.sin (2 ^ k * θ)

snip begin

/-- The doubling formula: `sin (2 x) = 2 · sin x · cos x`. -/
lemma sin_two_mul' (x : ℝ) : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x :=
  Real.sin_two_mul x

/-- For every `k`, `sin² (2^k · π / 3) = 3 / 4`. The proof is by induction using the
double-angle identity. -/
lemma sin_sq_pow_two_pi_div_three (k : ℕ) :
    Real.sin (2 ^ k * (π / 3)) ^ 2 = 3 / 4 := by
  induction k with
  | zero =>
    simp only [pow_zero, one_mul]
    rw [Real.sin_pi_div_three]
    rw [div_pow, Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0)]
    norm_num
  | succ k ih =>
    -- sin (2^(k+1) · π/3) = sin (2 · (2^k · π/3))
    have hrw : (2 : ℝ) ^ (k + 1) * (π / 3) = 2 * (2 ^ k * (π / 3)) := by ring
    rw [hrw, Real.sin_two_mul]
    have hcos_sq : Real.cos (2 ^ k * (π / 3)) ^ 2 = 1 / 4 := by
      have hpyth : Real.sin (2 ^ k * (π / 3)) ^ 2 + Real.cos (2 ^ k * (π / 3)) ^ 2 = 1 :=
        Real.sin_sq_add_cos_sq _
      linarith
    nlinarith [ih, hcos_sq]

/-- For every `k`, `|sin (2^k · π / 3)| = √3 / 2`. -/
lemma abs_sin_pow_two_pi_div_three (k : ℕ) :
    |Real.sin (2 ^ k * (π / 3))| = Real.sqrt 3 / 2 := by
  have h := sin_sq_pow_two_pi_div_three k
  -- |x| = √(x²)
  have habs : |Real.sin (2 ^ k * (π / 3))| = Real.sqrt (Real.sin (2 ^ k * (π / 3)) ^ 2) := by
    rw [Real.sqrt_sq_eq_abs]
  rw [habs, h]
  rw [Real.sqrt_div' 3 (by norm_num : (0:ℝ) ≤ 4)]
  congr 1
  rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]

/-- The value `f n (π/3)` has absolute value `(√3/2)^(n+1)`. -/
lemma abs_f_pi_div_three (n : ℕ) :
    |f n (π / 3)| = (Real.sqrt 3 / 2) ^ (n + 1) := by
  unfold f
  rw [Finset.abs_prod]
  rw [Finset.prod_congr rfl (fun k _ => abs_sin_pow_two_pi_div_three k)]
  rw [Finset.prod_const, Finset.card_range]

/-- The main bound, in the form `|f n θ| ≤ (√3/2)^n`. -/
lemma main_bound (n : ℕ) (θ : ℝ) :
    |f n θ| ≤ (Real.sqrt 3 / 2) ^ n := by
  -- Standard proof uses the auxiliary function `g θ = |sin θ| * |sin(2θ)|^(1/2)`,
  -- with `g θ ≤ (√3/2)^(3/2)` proved via AM-GM on `3 sin²θ + 3 cos²θ = 3`.
  -- Then `|f n θ|` is bounded by an appropriate product of `g(2^k θ)` raised to weights.
  -- TODO: complete this proof.
  sorry

snip end

problem imc2001_p12 (n : ℕ) (θ : ℝ) :
    |f n θ| ≤ (2 / Real.sqrt 3) * |f n (π / 3)| := by
  rw [abs_f_pi_div_three]
  have hsqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  -- (√3/2)^(n+1) = (√3/2) * (√3/2)^n, so (2/√3) * (√3/2)^(n+1) = (√3/2)^n.
  have hrewrite : (2 / Real.sqrt 3) * (Real.sqrt 3 / 2) ^ (n + 1) =
      (Real.sqrt 3 / 2) ^ n := by
    rw [pow_succ]
    field_simp
  rw [hrewrite]
  exact main_bound n θ

end Imc2001P12
