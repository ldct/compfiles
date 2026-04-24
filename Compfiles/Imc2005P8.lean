/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2005, Problem 8
(Second day, Problem 2)

Let `f : ℝ → ℝ` be such that for every integer `n ≥ 2` the function `x ↦ f x ^ n`
agrees with some polynomial. Prove that `f` itself is a polynomial.

(In fact, having `f^2` and `f^3` polynomial already suffices.)
-/

namespace Imc2005P8

open Polynomial

snip begin

/-- If `f^2` and `f^3` both agree with polynomials, then `f` is a polynomial. -/
theorem poly_of_sq_cube
    (f : ℝ → ℝ)
    (P Q : ℝ[X])
    (hP : ∀ x, f x ^ 2 = P.eval x)
    (hQ : ∀ x, f x ^ 3 = Q.eval x) :
    ∃ g : ℝ[X], ∀ x, f x = g.eval x := by
  -- First: `P ^ 3 = Q ^ 2` as polynomials (pointwise both equal `f x ^ 6`).
  have hPQ : P ^ 3 = Q ^ 2 := by
    have hpoint : ∀ x, (P ^ 3).eval x = (Q ^ 2).eval x := by
      intro x
      have h1 : (P ^ 3).eval x = (f x ^ 2) ^ 3 := by
        rw [eval_pow, hP]
      have h2 : (Q ^ 2).eval x = (f x ^ 3) ^ 2 := by
        rw [eval_pow, hQ]
      rw [h1, h2]; ring
    -- Two real polynomials that agree on all of ℝ are equal
    apply Polynomial.funext
    intro x
    exact hpoint x
  -- Case split on whether Q = 0.
  by_cases hQ0 : Q = 0
  · -- Q = 0 means f x ^ 3 = 0, so f x = 0.
    refine ⟨0, fun x => ?_⟩
    have : f x ^ 3 = 0 := by rw [hQ, hQ0]; simp
    have : f x = 0 := by
      have h := pow_eq_zero_iff (n := 3) (by norm_num : (3:ℕ) ≠ 0) |>.mp this
      exact h
    rw [this]; simp
  · -- Q ≠ 0, hence P ≠ 0 (since Q^2 = P^3).
    have hP0 : P ≠ 0 := by
      intro hP0
      apply hQ0
      have : Q ^ 2 = 0 := by rw [← hPQ, hP0]; ring
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    -- Work in the fraction field K = RatFunc ℝ.
    -- Let aP = algebraMap P, aQ = algebraMap Q.
    let aP : RatFunc ℝ := algebraMap ℝ[X] (RatFunc ℝ) P
    let aQ : RatFunc ℝ := algebraMap ℝ[X] (RatFunc ℝ) Q
    have hinj : Function.Injective (algebraMap ℝ[X] (RatFunc ℝ)) :=
      IsFractionRing.injective ℝ[X] (RatFunc ℝ)
    have haP_ne : aP ≠ 0 := fun h =>
      hP0 (hinj (by simpa [aP] using h))
    -- Let y = aQ / aP ∈ RatFunc ℝ.
    let y : RatFunc ℝ := aQ / aP
    have hy_sq : y ^ 2 = aP := by
      -- y^2 * aP^2 = aQ^2 = aP^3, so y^2 = aP.
      have h1 : y ^ 2 * aP ^ 2 = aQ ^ 2 := by
        show (aQ / aP) ^ 2 * aP ^ 2 = aQ ^ 2
        rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 haP_ne)]
      have h2 : aQ ^ 2 = aP ^ 3 := by
        have : (aQ : RatFunc ℝ) ^ 2 = aP ^ 3 := by
          show (algebraMap ℝ[X] (RatFunc ℝ) Q) ^ 2 = (algebraMap ℝ[X] (RatFunc ℝ) P) ^ 3
          rw [← map_pow, ← map_pow, hPQ]
        exact this
      have h3 : y ^ 2 * aP ^ 2 = aP ^ 3 := by rw [h1, h2]
      have h4 : aP ^ 2 ≠ 0 := pow_ne_zero _ haP_ne
      have h5 : y ^ 2 * aP ^ 2 = aP * aP ^ 2 := by rw [h3]; ring
      exact mul_right_cancel₀ h4 h5
    -- y^2 ∈ image of ℝ[X] → K (namely aP), so y^2 is integral over ℝ[X].
    have hy_int : IsIntegral ℝ[X] (y ^ 2) := by
      rw [hy_sq]
      exact isIntegral_algebraMap
    -- ℝ[X] is integrally closed in its fraction field.
    haveI : IsIntegrallyClosed ℝ[X] := UniqueFactorizationMonoid.instIsIntegrallyClosed
    obtain ⟨g, hg⟩ : ∃ g : ℝ[X], algebraMap ℝ[X] (RatFunc ℝ) g = y := by
      have := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
        (K := RatFunc ℝ) (n := 2) (by norm_num) hy_int
      exact this
    -- Now show g^3 = Q in ℝ[X].
    have hg3 : g ^ 3 = Q := by
      have h : algebraMap ℝ[X] (RatFunc ℝ) (g ^ 3) = aQ := by
        rw [map_pow, hg]
        show y ^ 3 = aQ
        have hy3 : y ^ 3 = y ^ 2 * y := by ring
        rw [hy3, hy_sq]
        show aP * (aQ / aP) = aQ
        rw [mul_div_cancel₀ _ haP_ne]
      exact hinj h
    -- Finally, g(x)^3 = Q(x) = f(x)^3 for all x, so g(x) = f(x) by injectivity of cubing.
    refine ⟨g, fun x => ?_⟩
    have h1 : g.eval x ^ 3 = f x ^ 3 := by
      rw [← eval_pow, hg3, ← hQ]
    have hodd : Odd 3 := ⟨1, rfl⟩
    have hinj := hodd.strictMono_pow (R := ℝ) |>.injective
    exact (hinj h1).symm

snip end

problem imc2005_p8
    (f : ℝ → ℝ)
    (hf : ∀ n, 2 ≤ n → ∃ p : ℝ[X], ∀ x, f x ^ n = p.eval x) :
    ∃ g : ℝ[X], ∀ x, f x = g.eval x := by
  obtain ⟨P, hP⟩ := hf 2 (by norm_num)
  obtain ⟨Q, hQ⟩ := hf 3 (by norm_num)
  exact poly_of_sq_cube f P Q hP hQ

end Imc2005P8
