/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2005, Problem 4

Find all polynomials `P(x) = a_n x^n + … + a_1 x + a_0` with nonzero
leading coefficient such that `(a_0, a_1, …, a_n)` is a permutation of
`(0, 1, …, n)` and all roots of `P` are rational numbers.

The answer is:
`x`,
`x² + 2x`,
`2x² + x`,
`x³ + 3x² + 2x`,
`2x³ + 3x² + x`.
-/

namespace Imc2005P4

open Polynomial

/-- Coefficients of `P : ℤ[X]` form a permutation of `{0, 1, …, n}`
where `n = natDegree P`. -/
def CoeffsArePerm (P : ℤ[X]) : Prop :=
  (Multiset.map P.coeff (Multiset.range (P.natDegree + 1))) =
    (Multiset.map (fun i : ℕ => (i : ℤ)) (Multiset.range (P.natDegree + 1)))

/-- Every root of `P` (in ℂ) is rational. Equivalently, `P` splits over `ℚ`. -/
def AllRootsRational (P : ℤ[X]) : Prop :=
  Splits (P.map (Int.castRingHom ℚ))

/-- A polynomial is a *solution* if it is nonzero, its coefficients are a
permutation of `{0, …, natDegree P}`, and all its roots are rational. -/
def IsSolution (P : ℤ[X]) : Prop :=
  P ≠ 0 ∧ CoeffsArePerm P ∧ AllRootsRational P

/-- The explicit list of five answer polynomials. -/
noncomputable determine answer : Finset ℤ[X] :=
  { X,
    X^2 + C 2 * X,
    C 2 * X^2 + X,
    X^3 + C 3 * X^2 + C 2 * X,
    C 2 * X^3 + C 3 * X^2 + X }

snip begin

/-! ### Factorizations of the answer polynomials. -/

lemma factor_X2_plus_2X : (X^2 + C 2 * X : ℤ[X]) = X * (X + C 2) := by ring

lemma factor_2X2_plus_X : (C 2 * X^2 + X : ℤ[X]) = X * (C 2 * X + 1) := by ring

lemma factor_cubic1 :
    (X^3 + C 3 * X^2 + C 2 * X : ℤ[X]) = X * (X + 1) * (X + C 2) := by
  have h3 : (C 3 : ℤ[X]) = 1 + C 2 := by
    rw [show (1 : ℤ[X]) = C 1 from (map_one _).symm, ← C_add]; norm_num
  rw [h3]; ring

lemma factor_cubic2 :
    (C 2 * X^3 + C 3 * X^2 + X : ℤ[X]) = X * (X + 1) * (C 2 * X + 1) := by
  have h3 : (C 3 : ℤ[X]) = 1 + C 2 := by
    rw [show (1 : ℤ[X]) = C 1 from (map_one _).symm, ← C_add]; norm_num
  rw [h3]; ring

/-! ### Coefficient permutation checks.

We verify each answer polynomial has the correct `natDegree` and compute its
coefficient multiset explicitly. -/

/-- Coefficients of `X : ℤ[X]` form a permutation of {0, 1}. -/
lemma coeffs_X : CoeffsArePerm (X : ℤ[X]) := by
  unfold CoeffsArePerm
  rw [natDegree_X]
  show ({(X:ℤ[X]).coeff 0, (X:ℤ[X]).coeff 1} : Multiset ℤ) = {((0:ℕ):ℤ), ((1:ℕ):ℤ)}
  simp [coeff_X]

/-- Coefficients of `X^2 + 2X : ℤ[X]` form a permutation of {0, 1, 2}. -/
lemma coeffs_X2_plus_2X : CoeffsArePerm (X^2 + C 2 * X : ℤ[X]) := by
  have hdeg : (X^2 + C 2 * X : ℤ[X]).natDegree = 2 := by compute_degree!
  unfold CoeffsArePerm
  rw [hdeg]
  show ({_, _, _} : Multiset ℤ) = {_, _, _}
  have h0 : (X^2 + C 2 * X : ℤ[X]).coeff 0 = 0 := by
    simp [coeff_add, coeff_X_pow, coeff_X]
  have h1 : (X^2 + C 2 * X : ℤ[X]).coeff 1 = 2 := by
    simp [coeff_add, coeff_X_pow, coeff_X]
  have h2 : (X^2 + C 2 * X : ℤ[X]).coeff 2 = 1 := by
    simp [coeff_add, coeff_X_pow, coeff_X]
  rw [h0, h1, h2]
  decide

/-- Coefficients of `2X^2 + X : ℤ[X]` form a permutation of {0, 1, 2}. -/
lemma coeffs_2X2_plus_X : CoeffsArePerm (C 2 * X^2 + X : ℤ[X]) := by
  have hdeg : (C 2 * X^2 + X : ℤ[X]).natDegree = 2 := by compute_degree!
  unfold CoeffsArePerm
  rw [hdeg]
  show ({_, _, _} : Multiset ℤ) = {_, _, _}
  have h0 : (C 2 * X^2 + X : ℤ[X]).coeff 0 = 0 := by
    simp [coeff_add, coeff_X_pow, coeff_X]
  have h1 : (C 2 * X^2 + X : ℤ[X]).coeff 1 = 1 := by
    simp [coeff_add, coeff_X_pow, coeff_X]
  have h2 : (C 2 * X^2 + X : ℤ[X]).coeff 2 = 2 := by
    simp [coeff_add, coeff_X_pow, coeff_X]
  rw [h0, h1, h2]
  decide

/-- Coefficients of `X^3 + 3X^2 + 2X : ℤ[X]` form a permutation of {0, 1, 2, 3}. -/
lemma coeffs_cubic1 : CoeffsArePerm (X^3 + C 3 * X^2 + C 2 * X : ℤ[X]) := by
  have hdeg : (X^3 + C 3 * X^2 + C 2 * X : ℤ[X]).natDegree = 3 := by compute_degree!
  unfold CoeffsArePerm
  rw [hdeg]
  show ({_, _, _, _} : Multiset ℤ) = {_, _, _, _}
  have h0 : (X^3 + C 3 * X^2 + C 2 * X : ℤ[X]).coeff 0 = 0 := by
    simp [coeff_add, coeff_X_pow, coeff_X]
  have h1 : (X^3 + C 3 * X^2 + C 2 * X : ℤ[X]).coeff 1 = 2 := by
    simp [coeff_add, coeff_X_pow, coeff_X]
  have h2 : (X^3 + C 3 * X^2 + C 2 * X : ℤ[X]).coeff 2 = 3 := by
    simp [coeff_add, coeff_X_pow, coeff_X]
  have h3 : (X^3 + C 3 * X^2 + C 2 * X : ℤ[X]).coeff 3 = 1 := by
    simp [coeff_add, coeff_X_pow, coeff_X]
  rw [h0, h1, h2, h3]
  decide

/-- Coefficients of `2X^3 + 3X^2 + X : ℤ[X]` form a permutation of {0, 1, 2, 3}. -/
lemma coeffs_cubic2 : CoeffsArePerm (C 2 * X^3 + C 3 * X^2 + X : ℤ[X]) := by
  have hdeg : (C 2 * X^3 + C 3 * X^2 + X : ℤ[X]).natDegree = 3 := by compute_degree!
  unfold CoeffsArePerm
  rw [hdeg]
  show ({_, _, _, _} : Multiset ℤ) = {_, _, _, _}
  have h0 : (C 2 * X^3 + C 3 * X^2 + X : ℤ[X]).coeff 0 = 0 := by
    simp [coeff_add, coeff_X_pow, coeff_X]
  have h1 : (C 2 * X^3 + C 3 * X^2 + X : ℤ[X]).coeff 1 = 1 := by
    simp [coeff_add, coeff_X_pow, coeff_X]
  have h2 : (C 2 * X^3 + C 3 * X^2 + X : ℤ[X]).coeff 2 = 3 := by
    simp [coeff_add, coeff_X_pow, coeff_X]
  have h3 : (C 2 * X^3 + C 3 * X^2 + X : ℤ[X]).coeff 3 = 2 := by
    simp [coeff_add, coeff_X_pow, coeff_X]
  rw [h0, h1, h2, h3]
  decide

/-! ### Each answer polynomial splits over ℚ. -/

/-- `C a * X + C b` splits over ℚ. -/
lemma splits_aX_plus_b_ℚ (a b : ℚ) : Splits (C a * X + C b : ℚ[X]) := by
  by_cases ha : a = 0
  · rw [ha]; simp
  · have : C a * X + C b = C a * (X + C (b / a)) := by
      rw [mul_add]
      congr 1
      rw [← C_mul, mul_div_cancel₀ _ ha]
    rw [this]
    exact (Splits.C a).mul (Splits.X_add_C _)

lemma splits_ans_X : AllRootsRational (X : ℤ[X]) := by
  unfold AllRootsRational
  rw [Polynomial.map_X]; exact Splits.X

lemma splits_ans_X2_plus_2X : AllRootsRational (X^2 + C 2 * X : ℤ[X]) := by
  unfold AllRootsRational
  rw [factor_X2_plus_2X]
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  exact Splits.X.mul (Splits.X_add_C _)

lemma splits_ans_2X2_plus_X : AllRootsRational (C 2 * X^2 + X : ℤ[X]) := by
  unfold AllRootsRational
  rw [factor_2X2_plus_X]
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_one]
  exact Splits.X.mul (splits_aX_plus_b_ℚ 2 1)

lemma splits_ans_cubic1 :
    AllRootsRational (X^3 + C 3 * X^2 + C 2 * X : ℤ[X]) := by
  unfold AllRootsRational
  rw [factor_cubic1]
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_one]
  exact (Splits.X.mul (Splits.X_add_C _)).mul (Splits.X_add_C _)

lemma splits_ans_cubic2 :
    AllRootsRational (C 2 * X^3 + C 3 * X^2 + X : ℤ[X]) := by
  unfold AllRootsRational
  rw [factor_cubic2]
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_one]
  exact (Splits.X.mul (Splits.X_add_C _)).mul (splits_aX_plus_b_ℚ 2 1)

/-- Each of the five answer polynomials is a solution. -/
lemma answer_subset_solutions : ∀ P ∈ answer, IsSolution P := by
  intro P hP
  simp only [answer, Finset.mem_insert, Finset.mem_singleton] at hP
  rcases hP with h | h | h | h | h
  all_goals subst h
  · refine ⟨X_ne_zero, coeffs_X, splits_ans_X⟩
  · refine ⟨?_, coeffs_X2_plus_2X, splits_ans_X2_plus_2X⟩
    intro h
    have : (X^2 + C 2 * X : ℤ[X]).natDegree = 2 := by compute_degree!
    rw [h, natDegree_zero] at this; omega
  · refine ⟨?_, coeffs_2X2_plus_X, splits_ans_2X2_plus_X⟩
    intro h
    have : (C 2 * X^2 + X : ℤ[X]).natDegree = 2 := by compute_degree!
    rw [h, natDegree_zero] at this; omega
  · refine ⟨?_, coeffs_cubic1, splits_ans_cubic1⟩
    intro h
    have : (X^3 + C 3 * X^2 + C 2 * X : ℤ[X]).natDegree = 3 := by compute_degree!
    rw [h, natDegree_zero] at this; omega
  · refine ⟨?_, coeffs_cubic2, splits_ans_cubic2⟩
    intro h
    have : (C 2 * X^3 + C 3 * X^2 + X : ℤ[X]).natDegree = 3 := by compute_degree!
    rw [h, natDegree_zero] at this; omega

snip end

problem imc2005_p4 (P : ℤ[X]) : IsSolution P ↔ P ∈ answer := by
  constructor
  · intro hP
    -- The forward direction requires the full enumeration argument via Vieta and AM-HM.
    -- TODO: formalize the remaining enumeration argument.
    sorry
  · intro hP
    exact answer_subset_solutions P hP

end Imc2005P4
