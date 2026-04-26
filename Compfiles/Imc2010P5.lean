/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2010, Problem 5

Suppose `a, b, c ∈ [-1, 1]` satisfy `1 + 2abc ≥ a² + b² + c²`. Prove that
  `1 + 2(abc)^n ≥ a^{2n} + b^{2n} + c^{2n}`
for all positive integers `n`.
-/

namespace Imc2010P5

open Matrix

/-- The symmetric matrix `M(a,b,c)` whose determinant is `1 + 2abc - a² - b² - c²`. -/
def tripleMatrix (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, a, b; a, 1, c; b, c, 1]

snip begin

lemma tripleMatrix_isHermitian (a b c : ℝ) : (tripleMatrix a b c).IsHermitian := by
  unfold tripleMatrix
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose, Matrix.transpose]

/-- The key identity: the quadratic form on `(x,y,z)` associated to `tripleMatrix a b c`,
after multiplying by `(1-a²)`, equals a sum of squares plus `P(a,b,c) · z²`, where
`P(a,b,c) = 1 + 2abc - a² - b² - c²`. -/
lemma quadratic_identity (a b c x y z : ℝ) :
    (1 - a^2) * (x^2 + y^2 + z^2 + 2*a*x*y + 2*b*x*z + 2*c*y*z) =
      (1 - a^2) * (x + a*y + b*z)^2 + ((1 - a^2)*y + (c - a*b)*z)^2 +
      (1 + 2*a*b*c - a^2 - b^2 - c^2) * z^2 := by
  ring

/-- If `|a|,|b|,|c| ≤ 1` and `1 + 2abc ≥ a² + b² + c²`, then the matrix
`tripleMatrix a b c` is positive semi-definite. -/
lemma tripleMatrix_posSemidef {a b c : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hc : |c| ≤ 1)
    (hP : a^2 + b^2 + c^2 ≤ 1 + 2*a*b*c) :
    (tripleMatrix a b c).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg (tripleMatrix_isHermitian a b c) ?_
  intro v
  -- The quadratic form is `v₀² + v₁² + v₂² + 2a v₀v₁ + 2b v₀v₂ + 2c v₁v₂`.
  set x := v 0
  set y := v 1
  set z := v 2
  have hdot : star v ⬝ᵥ ((tripleMatrix a b c) *ᵥ v) =
      x^2 + y^2 + z^2 + 2*a*x*y + 2*b*x*z + 2*c*y*z := by
    simp [dotProduct, mulVec, tripleMatrix, Fin.sum_univ_three, x, y, z]
    ring
  rw [hdot]
  -- `1 - a² ≥ 0` since `|a| ≤ 1`, similarly for b, c.
  have h1a : 0 ≤ 1 - a^2 := by nlinarith [abs_le.mp ha]
  have h1b : 0 ≤ 1 - b^2 := by nlinarith [abs_le.mp hb]
  have h1c : 0 ≤ 1 - c^2 := by nlinarith [abs_le.mp hc]
  have hPnonneg : 0 ≤ 1 + 2*a*b*c - a^2 - b^2 - c^2 := by linarith
  -- Case split on whether `1 - a² > 0` or `1 - a² = 0`.
  rcases eq_or_lt_of_le h1a with h1a_eq | h1a_pos
  · -- `a² = 1`. Then from `hP`, we have `(c - ab)² ≤ 0`, so `c = ab`.
    have ha2 : a^2 = 1 := by linarith
    have hcab : c - a*b = 0 := by
      have : (c - a*b)^2 ≤ 0 := by nlinarith [abs_le.mp hb]
      have hsq : 0 ≤ (c - a*b)^2 := sq_nonneg _
      nlinarith
    -- Quadratic form becomes `(x + ay + bz)² + (1-a²)y² + (1-b²)z² = (x+ay+bz)² + (1-b²)z²`.
    have : x^2 + y^2 + z^2 + 2*a*x*y + 2*b*x*z + 2*c*y*z =
        (x + a*y + b*z)^2 + (1 - a^2)*y^2 + (1 - b^2)*z^2 := by
      have hc_eq : c = a*b := by linarith
      rw [hc_eq]; ring
    rw [this]
    have h1 : 0 ≤ (x + a*y + b*z)^2 := sq_nonneg _
    have h2 : 0 ≤ (1 - a^2)*y^2 := mul_nonneg h1a (sq_nonneg _)
    have h3 : 0 ≤ (1 - b^2)*z^2 := mul_nonneg h1b (sq_nonneg _)
    linarith
  · -- `1 - a² > 0`. Use the polynomial identity.
    have hid := quadratic_identity a b c x y z
    have hRHS_nonneg :
        0 ≤ (1 - a^2) * (x + a*y + b*z)^2 + ((1 - a^2)*y + (c - a*b)*z)^2 +
            (1 + 2*a*b*c - a^2 - b^2 - c^2) * z^2 := by
      have h1 : 0 ≤ (1 - a^2) * (x + a*y + b*z)^2 :=
        mul_nonneg h1a (sq_nonneg _)
      have h2 : 0 ≤ ((1 - a^2)*y + (c - a*b)*z)^2 := sq_nonneg _
      have h3 : 0 ≤ (1 + 2*a*b*c - a^2 - b^2 - c^2) * z^2 :=
        mul_nonneg hPnonneg (sq_nonneg _)
      linarith
    have hLHS_nonneg : 0 ≤ (1 - a^2) * (x^2 + y^2 + z^2 + 2*a*x*y + 2*b*x*z + 2*c*y*z) := by
      linarith
    -- Divide by `(1 - a²) > 0`.
    have := (mul_nonneg_iff_of_pos_left h1a_pos).mp hLHS_nonneg
    exact this

/-- Hadamard product of two `tripleMatrix`s is a `tripleMatrix` of products. -/
lemma tripleMatrix_hadamard (a b c a' b' c' : ℝ) :
    tripleMatrix a b c ⊙ tripleMatrix a' b' c' =
      tripleMatrix (a * a') (b * b') (c * c') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tripleMatrix, hadamard]

/-- Positive-semi-definiteness is preserved under arbitrary Hadamard powers; concretely,
if `M = tripleMatrix a b c` is PSD, then `tripleMatrix aⁿ bⁿ cⁿ` is PSD for all `n ≥ 1`. -/
lemma tripleMatrix_pow_posSemidef {a b c : ℝ}
    (hM : (tripleMatrix a b c).PosSemidef) (n : ℕ) (hn : 1 ≤ n) :
    (tripleMatrix (a^n) (b^n) (c^n)).PosSemidef := by
  -- Induct on `n`.
  induction n, hn using Nat.le_induction with
  | base =>
    simpa using hM
  | succ k hk ih =>
    have hhad : (tripleMatrix (a^k) (b^k) (c^k) ⊙ tripleMatrix a b c).PosSemidef :=
      ih.hadamard hM
    have heq : tripleMatrix (a^k) (b^k) (c^k) ⊙ tripleMatrix a b c =
        tripleMatrix (a^(k+1)) (b^(k+1)) (c^(k+1)) := by
      rw [tripleMatrix_hadamard, ← pow_succ, ← pow_succ, ← pow_succ]
    rwa [heq] at hhad

/-- The determinant of `tripleMatrix a b c` is `1 + 2abc - a² - b² - c²`. -/
lemma tripleMatrix_det (a b c : ℝ) :
    (tripleMatrix a b c).det = 1 + 2*a*b*c - a^2 - b^2 - c^2 := by
  rw [det_fin_three]
  simp [tripleMatrix]
  ring

snip end

problem imc2010_p5 (a b c : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hc : |c| ≤ 1)
    (h : a^2 + b^2 + c^2 ≤ 1 + 2*a*b*c) :
    ∀ n : ℕ, 1 ≤ n → a^(2*n) + b^(2*n) + c^(2*n) ≤ 1 + 2*(a*b*c)^n := by
  intro n hn
  -- The matrix `tripleMatrix a b c` is PSD.
  have hPSD : (tripleMatrix a b c).PosSemidef :=
    tripleMatrix_posSemidef ha hb hc h
  -- Its n-th Hadamard power `tripleMatrix aⁿ bⁿ cⁿ` is also PSD.
  have hPSDn : (tripleMatrix (a^n) (b^n) (c^n)).PosSemidef :=
    tripleMatrix_pow_posSemidef hPSD n hn
  -- Take determinants: det ≥ 0.
  have hdet : 0 ≤ (tripleMatrix (a^n) (b^n) (c^n)).det := hPSDn.det_nonneg
  rw [tripleMatrix_det] at hdet
  -- Rewrite: `(aⁿ)² = a^{2n}`, etc., and `aⁿ bⁿ cⁿ = (abc)ⁿ`.
  have h1 : (a^n)^2 = a^(2*n) := by rw [← pow_mul]; ring_nf
  have h2 : (b^n)^2 = b^(2*n) := by rw [← pow_mul]; ring_nf
  have h3 : (c^n)^2 = c^(2*n) := by rw [← pow_mul]; ring_nf
  have h4 : a^n * b^n * c^n = (a*b*c)^n := by
    rw [mul_pow, mul_pow]
  linarith [hdet, h1, h2, h3, h4, sq (a^n), sq (b^n), sq (c^n)]

end Imc2010P5
