/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1995, Problem 5 (Day 1)

Let `A`, `B` be real `n × n` matrices. Suppose there exist `n + 1` distinct
reals `t_1, …, t_{n+1}` such that each `C_i = A + t_i • B` is nilpotent. Show
that `A` and `B` are nilpotent.

## Proof outline

For an `n × n` matrix `M` over `ℝ`, `IsNilpotent M` implies `M ^ n = 0`
(via `M.charpoly = X ^ n` and Cayley–Hamilton).

Lift to polynomial coefficients: define
`Mp : Matrix (Fin n) (Fin n) ℝ[X] := A.map C + (X : ℝ[X]) • B.map C`.

For each scalar `t`, applying `(Polynomial.evalRingHom t).mapMatrix` to `Mp ^ n`
yields `(A + t • B) ^ n`, which is `0` whenever `A + t • B` is nilpotent.

Hence each entry of `Mp ^ n` is a polynomial of degree at most `n` (proved by
induction on `n`: `Mp` has entry-degrees ≤ 1) with at least `n + 1` distinct
roots `t_1, …, t_{n+1}`, so it must be the zero polynomial. Therefore
`Mp ^ n = 0`. The constant coefficient of `(Mp ^ n) i j` is `(A ^ n) i j`,
and the leading coefficient (`coeff n`) is `(B ^ n) i j`. Both vanish.
-/

namespace Imc1995P5

open scoped Matrix
open Polynomial

section

variable {n : ℕ}

/-- Auxiliary: for any matrix `M : Matrix (Fin n) (Fin n) ℝ[X]` whose every
entry has `natDegree ≤ 1`, every entry of `M ^ k` has `natDegree ≤ k`. -/
private lemma natDegree_pow_entry_le {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ[X])
    (hM : ∀ i j, (M i j).natDegree ≤ 1) (k : ℕ) :
    ∀ i j, ((M ^ k) i j).natDegree ≤ k := by
  induction k with
  | zero =>
    intro i j
    simp [Matrix.one_apply]
    by_cases h : i = j
    · simp [h]
    · simp [h]
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    -- ∑ l, (M^k) i l * M l j; degree of each term ≤ k + 1.
    refine Polynomial.natDegree_sum_le_of_forall_le
      (n := k + 1) Finset.univ _ ?_
    intro l _
    refine (Polynomial.natDegree_mul_le).trans ?_
    have h1 : ((M ^ k) i l).natDegree ≤ k := ih i l
    have h2 : (M l j).natDegree ≤ 1 := hM l j
    omega

/-- The polynomial-coefficient matrix `A.map C + X • B.map C`.  Every entry has
`natDegree ≤ 1`. -/
private noncomputable def liftPoly (A B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ[X] :=
  A.map (C : ℝ →+* ℝ[X]) + (X : ℝ[X]) • B.map (C : ℝ →+* ℝ[X])

/-- Each entry of `liftPoly A B` has `natDegree ≤ 1`. -/
private lemma liftPoly_natDegree_le_one (A B : Matrix (Fin n) (Fin n) ℝ) :
    ∀ i j, ((liftPoly A B) i j).natDegree ≤ 1 := by
  intro i j
  simp only [liftPoly, Matrix.add_apply, Matrix.map_apply,
    Matrix.smul_apply, smul_eq_mul]
  refine Polynomial.natDegree_add_le_iff_left _ _ ?_ |>.mpr ?_
  · -- natDegree (X * C (B i j)) ≤ 1
    refine (Polynomial.natDegree_mul_le).trans ?_
    rw [Polynomial.natDegree_X, Polynomial.natDegree_C]
  · -- natDegree (C (A i j)) ≤ 1
    rw [Polynomial.natDegree_C]
    omega

/-- Evaluating `liftPoly A B` at a real `t` gives `A + t • B`. -/
private lemma evalRingHom_mapMatrix_liftPoly (A B : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    ((Polynomial.evalRingHom t).mapMatrix (liftPoly A B)) = A + t • B := by
  ext i j
  show ((liftPoly A B) i j).eval t = (A + t • B) i j
  simp only [liftPoly, Matrix.add_apply, Matrix.map_apply,
    Matrix.smul_apply, smul_eq_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X]

/-- For an `n × n` matrix `M` over `ℝ`, if `M` is nilpotent then `M ^ n = 0`. -/
private lemma pow_finrank_eq_zero_of_isNilpotent
    (M : Matrix (Fin n) (Fin n) ℝ) (h : IsNilpotent M) :
    M ^ n = 0 := by
  -- Move to the endomorphism `Matrix.toLin'`.
  let φ : Module.End ℝ (Fin n → ℝ) := M.toLin'
  have hφ : IsNilpotent φ := h.map (Matrix.toLinAlgEquiv'.toAlgHom (R := ℝ))
  have hpoly : φ.charpoly = X ^ n := by
    have := IsNilpotent.charpoly_eq_X_pow_finrank hφ
    simpa [Module.finrank_pi] using this
  -- Cayley–Hamilton over endomorphisms.
  have hae : (Polynomial.aeval φ) (X ^ n : ℝ[X]) = 0 := by
    rw [← hpoly]; exact φ.aeval_self_charpoly
  have hφn : φ ^ n = 0 := by simpa using hae
  -- Transport back to the matrix.
  have htoLin : M.toLin' ^ n = (M ^ n).toLin' := (Matrix.toLin'_pow M n).symm
  rw [htoLin] at hφn
  -- `Matrix.toLin'` is injective.
  have hinj : Function.Injective (Matrix.toLin' (R := ℝ) (n := Fin n)) :=
    Matrix.toLinAlgEquiv'.injective
  exact hinj (by simpa using hφn)

end

/-- The main problem statement. -/
problem imc1995_p5 (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ)
    (t : Fin (n + 1) → ℝ) (ht : Function.Injective t)
    (hC : ∀ i, IsNilpotent (A + t i • B)) :
    IsNilpotent A ∧ IsNilpotent B := by
  -- Step 1: For each `i`, `(A + t i • B) ^ n = 0`.
  have hCn : ∀ i, (A + t i • B) ^ n = 0 := fun i =>
    pow_finrank_eq_zero_of_isNilpotent _ (hC i)
  -- Step 2: `liftPoly A B` evaluated at `t i` equals `A + t i • B`.
  set Mp : Matrix (Fin n) (Fin n) ℝ[X] := liftPoly A B with hMp
  -- Step 3: each entry of `Mp ^ n` is `0` (a polynomial of degree ≤ n with n+1 distinct roots).
  have hMpn_entry : ∀ i j, (Mp ^ n) i j = 0 := by
    intro i j
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
        ((Mp ^ n) i j) ht
    · intro k
      -- Evaluate (Mp^n) i j at t k.
      have hMpval : ((Polynomial.evalRingHom (t k)).mapMatrix Mp = A + t k • B) :=
        evalRingHom_mapMatrix_liftPoly A B (t k)
      have heval :
          ((Polynomial.evalRingHom (t k)).mapMatrix (Mp ^ n)) i j
            = ((A + t k • B) ^ n) i j := by
        rw [map_pow, hMpval]
      have h0 : ((A + t k • B) ^ n) i j = 0 := by rw [hCn k]; rfl
      -- (evalRingHom (t k)).mapMatrix (Mp^n) i j = (Mp^n) i j evaluated.
      have heval' :
          ((Mp ^ n) i j).eval (t k) =
            ((Polynomial.evalRingHom (t k)).mapMatrix (Mp ^ n)) i j := rfl
      rw [heval', heval, h0]
    · -- natDegree ((Mp^n) i j) ≤ n < n + 1 = card Fin (n+1).
      have hdeg : ((Mp ^ n) i j).natDegree ≤ n :=
        natDegree_pow_entry_le Mp (liftPoly_natDegree_le_one A B) n i j
      simp; omega
  -- Step 4: extract A^n = 0 from coefficient 0, B^n = 0 from coefficient n.
  refine ⟨⟨n, ?_⟩, ⟨n, ?_⟩⟩
  · -- A^n = 0
    -- Apply `(evalRingHom 0).mapMatrix` to `Mp^n = 0`.
    have hMpn_zero : Mp ^ n = 0 := by
      apply Matrix.ext
      intro i j
      simpa using hMpn_entry i j
    have h := congrArg (Polynomial.evalRingHom (0 : ℝ)).mapMatrix hMpn_zero
    rw [map_pow] at h
    rw [show (Polynomial.evalRingHom (0 : ℝ)).mapMatrix Mp = A by
      have := evalRingHom_mapMatrix_liftPoly A B 0
      simp at this; exact this] at h
    simpa using h
  · -- B^n = 0
    -- The coefficient-`n` map `coeffNthRingHom n` is not a ring hom in general.
    -- Use `Polynomial.coeff` componentwise: `coeff n ((Mp^n) i j) = (B^n) i j`.
    ext i j
    show (B ^ n) i j = 0
    -- (Mp^n) i j = 0, so its coefficient n is 0.
    have hcoeff : ((Mp ^ n) i j).coeff n = 0 := by
      rw [hMpn_entry i j]; simp
    -- Now prove ((Mp^n) i j).coeff n = (B^n) i j.
    have hcoeff' : ((Mp ^ n) i j).coeff n = (B ^ n) i j := by
      -- Mp = A.map C + X • B.map C.
      -- Mp^n: top coeff (coeff n) of (i,j) entry equals (B^n) i j.
      -- Prove by induction on n. Use a more general statement.
      have key : ∀ k i j,
          ((Mp ^ k) i j).coeff k = (B ^ k) i j := by
        intro k
        induction k with
        | zero =>
          intro i j
          simp [Matrix.one_apply]
          by_cases h : i = j
          · simp [h]
          · simp [h]
        | succ k ih =>
          intro i j
          rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply,
              Polynomial.finset_sum_coeff]
          apply Finset.sum_congr rfl
          intro l _
          -- Goal: ((Mp^k) i l * Mp l j).coeff (k+1) = ((B^k) i l) * (B l j)
          rw [Polynomial.coeff_mul]
          -- ∑ x in antidiagonal (k+1), ((Mp^k) i l).coeff x.1 * (Mp l j).coeff x.2.
          -- We'll only have nonzero contribution from x = (k, 1) since
          -- (Mp^k) i l has natDegree ≤ k and Mp l j has natDegree ≤ 1.
          have hMpkdeg : ((Mp ^ k) i l).natDegree ≤ k :=
            natDegree_pow_entry_le Mp (liftPoly_natDegree_le_one A B) k i l
          have hMpdeg : (Mp l j).natDegree ≤ 1 :=
            liftPoly_natDegree_le_one A B l j
          rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (f := fun a b => ((Mp ^ k) i l).coeff a * (Mp l j).coeff b) (k+1)]
          -- Sum over a ∈ range (k+2) of ((Mp^k) i l).coeff a * (Mp l j).coeff (k+1-a)
          have hsum : ∀ a ∈ Finset.range (k + 1 + 1), a ≠ k →
              ((Mp ^ k) i l).coeff a * (Mp l j).coeff (k + 1 - a) = 0 := by
            intro a ha hane
            rcases lt_or_gt_of_ne hane with h | h
            · -- a < k, so k+1-a ≥ 2 > 1, so coeff (Mp l j) (k+1-a) = 0.
              have : k + 1 - a ≥ 2 := by omega
              have hzero : (Mp l j).coeff (k + 1 - a) = 0 := by
                apply Polynomial.coeff_eq_zero_of_natDegree_lt
                omega
              rw [hzero, mul_zero]
            · -- a > k, but a ≤ k+1 so a = k+1, and natDegree ≤ k.
              have hzero : ((Mp ^ k) i l).coeff a = 0 := by
                apply Polynomial.coeff_eq_zero_of_natDegree_lt
                omega
              rw [hzero, zero_mul]
          rw [Finset.sum_eq_single k]
          · -- contribution at a = k:
            -- ((Mp^k) i l).coeff k * (Mp l j).coeff 1 = (B^k) i l * (B l j) (after ih and computing Mp).
            rw [ih]
            -- goal: (B^k) i l * (Mp l j).coeff (k+1-k) = (B^k) i l * B l j
            have hMplj1 : (Mp l j).coeff 1 = B l j := by
              show (liftPoly A B l j).coeff 1 = B l j
              simp [liftPoly, Matrix.add_apply, Matrix.map_apply,
                Matrix.smul_apply, smul_eq_mul]
            have hsubeq : k + 1 - k = 1 := by omega
            rw [hsubeq, hMplj1]
          · intro a ha hane
            exact hsum a ha hane
          · intro hk
            exfalso; apply hk
            simp
      exact key n i j
    rw [← hcoeff', hcoeff]

end Imc1995P5
