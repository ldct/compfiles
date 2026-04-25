/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2018, Problem 3
(IMC 2018, Day 1, Problem 3)

Determine all rational `a` for which the matrix
```
⎡  a  -a  -1   0 ⎤
⎢  a  -a   0  -1 ⎥
⎢  1   0   a  -a ⎥
⎣  0   1   a  -a ⎦
```
is the square of a matrix with rational entries.

Answer: `a = 0`.
-/

namespace Imc2018P3

open Matrix Polynomial

/-- The matrix `A(a)` from the problem. -/
def matA (a : ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  !![ a, -a, -1,  0;
      a, -a,  0, -1;
      1,  0,  a, -a;
      0,  1,  a, -a]

/-- The set of all rational `a` for which `matA a` is the square of a rational matrix. -/
determine answer : Set ℚ := {0}

snip begin

/-- A specific rational matrix `B` whose square is `matA 0`.
This is the companion matrix of `x^4 + 1`. -/
def matB : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 0, 0, -1;
     1, 0, 0,  0;
     0, 1, 0,  0;
     0, 0, 1,  0]

lemma matB_sq : matB * matB = matA 0 := by
  unfold matB matA
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

/-- Computation of `(matA a)^2 + I`. -/
lemma matA_sq_add_one (a : ℚ) :
    matA a * matA a + 1 =
      !![0, 0, -2*a,  2*a;
         0, 0, -2*a,  2*a;
         2*a, -2*a, 0, 0;
         2*a, -2*a, 0, 0] := by
  unfold matA
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The matrix `(matA a)^2 + I` is nilpotent of index 2: its square is zero. -/
lemma matA_sq_add_one_sq (a : ℚ) :
    (matA a * matA a + 1) * (matA a * matA a + 1) = 0 := by
  rw [matA_sq_add_one a]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

/-- If `matA a * matA a + 1 = 0`, then `a = 0`. -/
lemma a_eq_zero_of_matA_sq_eq_neg_one {a : ℚ} (h : matA a * matA a + 1 = 0) : a = 0 := by
  rw [matA_sq_add_one] at h
  have h13 : (!![0, 0, -2*a,  2*a;
                 0, 0, -2*a,  2*a;
                 2*a, -2*a, 0, 0;
                 2*a, -2*a, 0, 0] : Matrix (Fin 4) (Fin 4) ℚ) 0 2 = 0 := by
    rw [h]; rfl
  simp at h13
  linarith

/-- The 8th cyclotomic polynomial is `X^4 + 1` over any commutative ring. -/
lemma cyclotomic_eight (R : Type*) [CommRing R] :
    Polynomial.cyclotomic 8 R = X ^ 4 + 1 := by
  have h2prime : Nat.Prime 2 := by decide
  have h : (8 : ℕ) = 2 ^ (2 + 1) := by norm_num
  rw [h, cyclotomic_prime_pow_eq_geom_sum h2prime]
  simp [Finset.sum_range_succ, pow_succ]
  ring

/-- `X^4 + 1` is irreducible over `ℚ`. -/
lemma X_pow_four_add_one_irreducible : Irreducible (X ^ 4 + 1 : ℚ[X]) := by
  rw [← cyclotomic_eight ℚ]
  exact cyclotomic.irreducible_rat (by norm_num)

/-- `X^4 + 1` as a polynomial over ℚ is monic. -/
lemma X_pow_four_add_one_monic : (X ^ 4 + 1 : ℚ[X]).Monic := by
  have h : (X ^ 4 + 1 : ℚ[X]) = X ^ 4 + C 1 := by simp
  rw [h]
  refine (monic_X_pow 4).add_of_left ?_
  rw [degree_C one_ne_zero, degree_X_pow]
  exact_mod_cast Nat.zero_lt_succ _

/-- `X^4 + 1` has natural degree `4` over ℚ. -/
lemma X_pow_four_add_one_natDegree : (X ^ 4 + 1 : ℚ[X]).natDegree = 4 := by
  have h : (X ^ 4 + 1 : ℚ[X]) = X ^ 4 + C 1 := by simp
  rw [h]
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact Polynomial.natDegree_X_pow 4
  · rw [natDegree_C, natDegree_X_pow]; norm_num

/-- For any `4 × 4` matrix `B` over `ℚ` with `(B^4 + 1)^2 = 0`, we have `B^4 + 1 = 0`. -/
lemma B_pow_four_add_one_eq_zero
    (B : Matrix (Fin 4) (Fin 4) ℚ)
    (h : (B ^ 4 + 1) * (B ^ 4 + 1) = 0) :
    B ^ 4 + 1 = 0 := by
  -- `(X^4 + 1)^2` annihilates `B`.
  have hAnn : aeval B ((X ^ 4 + 1) ^ 2 : ℚ[X]) = 0 := by
    have e1 : ((X ^ 4 + 1) ^ 2 : ℚ[X]) = (X ^ 4 + 1) * (X ^ 4 + 1) := sq (X ^ 4 + 1)
    rw [e1]
    simp only [map_mul, map_add, map_pow, aeval_X, aeval_one]
    exact h
  -- `B` is integral over `ℚ`.
  have hint : IsIntegral ℚ B := Matrix.isIntegral B
  -- minpoly divides `(X^4+1)^2`.
  have hdvd : minpoly ℚ B ∣ (X ^ 4 + 1) ^ 2 := minpoly.dvd ℚ B hAnn
  -- `X^4+1` is prime in `ℚ[X]` (since irreducible in a UFD).
  have hprime : Prime (X ^ 4 + 1 : ℚ[X]) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp X_pow_four_add_one_irreducible
  -- By `dvd_prime_pow`, `minpoly` is associated to `(X^4+1)^i` for some `i ≤ 2`.
  obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hprime 2).mp hdvd
  -- minpoly is monic and so are the powers; associated monic polys are equal.
  have hminmonic : (minpoly ℚ B).Monic := minpoly.monic hint
  have hpow_monic : ((X ^ 4 + 1 : ℚ[X]) ^ i).Monic :=
    X_pow_four_add_one_monic.pow i
  have hmin_eq : minpoly ℚ B = (X ^ 4 + 1) ^ i :=
    eq_of_monic_of_associated hminmonic hpow_monic hassoc
  -- The charpoly has degree 4, and minpoly divides it, so deg minpoly ≤ 4.
  have hcharpoly_dvd : minpoly ℚ B ∣ B.charpoly := minpoly_dvd_charpoly B
  have hdeg_charpoly : B.charpoly.natDegree = 4 := by
    rw [Matrix.charpoly_natDegree_eq_dim]; simp
  have hcharmonic : B.charpoly.Monic := Matrix.charpoly_monic B
  have hdeg_minpoly_le : (minpoly ℚ B).natDegree ≤ 4 := by
    have := Polynomial.natDegree_le_of_dvd hcharpoly_dvd hcharmonic.ne_zero
    rw [hdeg_charpoly] at this
    exact this
  -- We have `(X^4+1)^i` of natDegree `4*i ≤ 4`, so `i ≤ 1`.
  have hdeg_pow : ((X ^ 4 + 1 : ℚ[X]) ^ i).natDegree = 4 * i := by
    rw [Polynomial.natDegree_pow, X_pow_four_add_one_natDegree, mul_comm]
  have hi_le : i ≤ 1 := by
    have : 4 * i ≤ 4 := by rw [← hdeg_pow, ← hmin_eq]; exact hdeg_minpoly_le
    omega
  -- minpoly is nontrivial, ruling out `i = 0`.
  have hne : minpoly ℚ B ≠ 1 := minpoly.ne_one ℚ B
  have hi_pos : 0 < i := by
    rcases Nat.eq_zero_or_pos i with hzero | hpos
    · rw [hzero, pow_zero] at hmin_eq
      exact absurd hmin_eq hne
    · exact hpos
  have hi1 : i = 1 := by omega
  -- So minpoly = X^4 + 1.
  have hmin_eq' : minpoly ℚ B = X ^ 4 + 1 := by rw [hmin_eq, hi1, pow_one]
  -- minpoly annihilates B.
  have hCH : aeval B (minpoly ℚ B) = 0 := minpoly.aeval ℚ B
  rw [hmin_eq'] at hCH
  simpa [map_add, map_pow, aeval_X, aeval_one] using hCH

snip end

problem imc2018_p3 (a : ℚ) :
    a ∈ answer ↔ ∃ B : Matrix (Fin 4) (Fin 4) ℚ, B * B = matA a := by
  unfold answer
  constructor
  · -- a = 0 case: provide the explicit B.
    intro ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact ⟨matB, matB_sq⟩
  · -- A = B² implies a = 0.
    rintro ⟨B, hB⟩
    rw [Set.mem_singleton_iff]
    -- (B^4 + 1)^2 = (A^2 + 1)^2 = 0.
    have hAsq : matA a * matA a = B ^ 4 := by
      have h4 : B ^ 4 = (B * B) * (B * B) := by
        rw [pow_succ, pow_succ, pow_succ, pow_one, mul_assoc]
      rw [h4, hB]
    have hnil : (B ^ 4 + 1) * (B ^ 4 + 1) = 0 := by
      rw [← hAsq]; exact matA_sq_add_one_sq a
    have hzero : B ^ 4 + 1 = 0 := B_pow_four_add_one_eq_zero B hnil
    -- Hence A^2 + 1 = 0, so a = 0.
    have hAzero : matA a * matA a + 1 = 0 := by rw [hAsq]; exact hzero
    exact a_eq_zero_of_matA_sq_eq_neg_one hAzero

end Imc2018P3
