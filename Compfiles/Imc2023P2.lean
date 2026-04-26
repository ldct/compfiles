/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2023, Problem 2

Let `A`, `B`, and `C` be `n × n` matrices with complex entries satisfying
  `A^2 = B^2 = C^2` and `B^3 = A * B * C + 2 * I`.
Prove that `A^6 = I`.
-/

namespace Imc2023P2

open Matrix

snip begin

/-- In a module over ℂ (such as complex matrices), `2 • M = 0` implies `M = 0`. -/
lemma nsmul_two_eq_zero_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    (2 : ℕ) • M = 0 ↔ M = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h]; simp⟩
  have h2 : (2 : ℂ) • M = 0 := by
    have : ((2 : ℕ) : ℂ) • M = (2 : ℕ) • M := Nat.cast_smul_eq_nsmul ℂ 2 M
    rw [← this] at h
    simpa using h
  have h2ne : (2 : ℂ) ≠ 0 := two_ne_zero
  rcases smul_eq_zero.mp h2 with h | h
  · exact absurd h h2ne
  · exact h

snip end

problem imc2023_p2 {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℂ)
    (hAB : A ^ 2 = B ^ 2) (hBC : B ^ 2 = C ^ 2)
    (hcube : B ^ 3 = A * B * C + 2 • (1 : Matrix (Fin n) (Fin n) ℂ)) :
    A ^ 6 = 1 := by
  -- Step 1: A^2 * B = B^3.
  have hA2B : A ^ 2 * B = B ^ 3 := by
    rw [hAB, show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one]
  -- Step 2: B * C^2 = B^3.
  have hBC2 : B * C ^ 2 = B ^ 3 := by
    rw [← hBC, show (3 : ℕ) = 1 + 2 from rfl, pow_add, pow_one]
  -- Step 3: A * (A*B - B*C) = 2 • 1.
  have hL : A * (A * B - B * C) = 2 • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have h1 : A * (A * B - B * C) = A ^ 2 * B - A * B * C := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← sq, ← Matrix.mul_assoc]
    rw [h1, hA2B, hcube]; abel
  -- Step 4: (A*B - B*C) * (-C) = 2 • 1.
  have hR : (A * B - B * C) * (-C) = 2 • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have h1 : (A * B - B * C) * (-C) = B * C ^ 2 - A * B * C := by
      rw [Matrix.sub_mul, Matrix.mul_neg, Matrix.mul_neg, Matrix.mul_assoc B C C, ← sq]
      abel
    rw [h1, hBC2, hcube]; abel
  -- Step 5: A = -C via 2•A = 2•(-C).
  have hAnegC_smul : (2 : ℕ) • A = (2 : ℕ) • (-C) := by
    have e1 : A * (A * B - B * C) * (-C) = ((2 : ℕ) • (1 : Matrix (Fin n) (Fin n) ℂ)) * (-C) := by
      rw [hL]
    have e2 : A * (A * B - B * C) * (-C) = A * ((A * B - B * C) * (-C)) := by
      rw [Matrix.mul_assoc]
    rw [e2, hR] at e1
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul] at e1
    exact e1
  have hAC : A = -C := by
    have hsub : (2 : ℕ) • (A - (-C)) = 0 := by
      rw [nsmul_sub, hAnegC_smul, sub_self]
    exact sub_eq_zero.mp ((nsmul_two_eq_zero_iff _).mp hsub)
  -- Step 6: Substitute C = -A. Then hcube becomes B^3 = -A*B*A + 2 • 1.
  have hCA : C = -A := by rw [hAC]; simp
  have hABA : A * B * A = 2 • (1 : Matrix (Fin n) (Fin n) ℂ) - B ^ 3 := by
    have h := hcube
    rw [hCA] at h
    -- h : B ^ 3 = A * B * (-A) + 2 • 1
    rw [Matrix.mul_neg] at h
    -- h : B ^ 3 = -(A * B * A) + 2 • 1
    linear_combination (norm := abel) h
  -- Step 7: A * B * A commutes with B, hence (A*B)^2 = (B*A)^2.
  have hABAB_eq : A * B * A * B = B * (A * B * A) := by
    have lhs : (A * B * A) * B =
        2 • B - B ^ 4 := by
      rw [hABA, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
          show (4 : ℕ) = 3 + 1 from rfl, pow_add, pow_one]
    have rhs : B * (A * B * A) =
        2 • B - B ^ 4 := by
      rw [hABA, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
          show (4 : ℕ) = 1 + 3 from rfl, pow_add, pow_one]
    calc A * B * A * B = (A * B * A) * B := rfl
      _ = 2 • B - B ^ 4 := lhs
      _ = B * (A * B * A) := rhs.symm
  have hABsq_BAsq : (A * B) * (A * B) = (B * A) * (B * A) := by
    have eq1 : (A * B) * (A * B) = A * B * A * B := by
      simp [Matrix.mul_assoc]
    have eq2 : B * (A * B * A) = (B * A) * (B * A) := by
      simp [Matrix.mul_assoc]
    rw [eq1, hABAB_eq, eq2]
  -- Step 8: (AB - BA)(AB + BA) = 0.
  have hA2_B2 : A ^ 2 = B ^ 2 := hAB
  have hAB2A : A * B ^ 2 * A = A ^ 4 := by
    rw [← hA2_B2]
    rw [show A * A ^ 2 * A = A ^ 1 * A ^ 2 * A ^ 1 from by rw [pow_one]]
    rw [← pow_add, ← pow_add]
  have hBA2B : B * A ^ 2 * B = B ^ 4 := by
    rw [hA2_B2]
    rw [show B * B ^ 2 * B = B ^ 1 * B ^ 2 * B ^ 1 from by rw [pow_one]]
    rw [← pow_add, ← pow_add]
  have hA4_eq_B4 : A ^ 4 = B ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, hAB]
  have hKey : (A * B - B * A) * (A * B + B * A) = 0 := by
    have expand :
      (A * B - B * A) * (A * B + B * A) =
        (A * B) * (A * B) + A * B ^ 2 * A - B * A ^ 2 * B - (B * A) * (B * A) := by
      rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add]
      have e1 : (A * B) * (B * A) = A * B ^ 2 * A := by
        rw [Matrix.mul_assoc A B (B * A), ← Matrix.mul_assoc B B A, ← sq,
            ← Matrix.mul_assoc]
      have e2 : (B * A) * (A * B) = B * A ^ 2 * B := by
        rw [Matrix.mul_assoc B A (A * B), ← Matrix.mul_assoc A A B, ← sq,
            ← Matrix.mul_assoc]
      rw [e1, e2]; abel
    rw [expand, hAB2A, hBA2B, hABsq_BAsq, hA4_eq_B4]
    abel
  -- Step 9: (AB+BA)*A = 2 • 1 (symmetric to hR via C = -A).
  have hAB_BC_eq_plus : A * B - B * C = A * B + B * A := by
    rw [hCA]; simp
  have hR' : (A * B + B * A) * A = 2 • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have hR2 := hR
    rw [hCA] at hR2
    -- hR2 : (A * B - B * -A) * -(-A) = 2 • 1
    simp only [Matrix.mul_neg, neg_neg, sub_neg_eq_add] at hR2
    -- hR2 : (A * B + B * A) * A = 2 • 1
    exact hR2
  -- Step 10: AB = BA.
  have hABeqBA : A * B = B * A := by
    -- (AB-BA)(AB+BA)*A = 0, but also = (AB-BA) * (2 • 1) = 2 • (AB-BA).
    have h0 : (A * B - B * A) * ((A * B + B * A) * A) = 0 := by
      rw [← Matrix.mul_assoc, hKey, Matrix.zero_mul]
    rw [hR', Matrix.mul_smul, Matrix.mul_one] at h0
    have hd : A * B - B * A = 0 := (nsmul_two_eq_zero_iff _).mp h0
    exact sub_eq_zero.mp hd
  -- Step 11: B^3 = I.
  have hB3 : B ^ 3 = 1 := by
    -- ABA = A(BA) = A(AB) = A^2 B = B^3 (from hA2B). Also ABA = 2•1 - B^3.
    have hABA' : A * B * A = B ^ 3 := by
      rw [Matrix.mul_assoc, ← hABeqBA, ← Matrix.mul_assoc, ← sq, hA2B]
    -- So B^3 = 2 • 1 - B^3, i.e., 2 • B^3 = 2 • 1.
    have h : B ^ 3 = 2 • (1 : Matrix (Fin n) (Fin n) ℂ) - B ^ 3 := by
      rw [← hABA]; exact hABA'.symm
    have h2 : (2 : ℕ) • B ^ 3 = (2 : ℕ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      have : B ^ 3 + B ^ 3 = 2 • (1 : Matrix (Fin n) (Fin n) ℂ) := by
        linear_combination (norm := abel) h
      rw [two_nsmul]; exact this
    have hsub : (2 : ℕ) • (B ^ 3 - 1) = 0 := by
      rw [nsmul_sub, h2, sub_self]
    exact sub_eq_zero.mp ((nsmul_two_eq_zero_iff _).mp hsub)
  -- Step 12: A^6 = B^6 = (B^3)^2 = 1.
  have hA6 : A ^ 6 = B ^ 6 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, pow_mul, hAB]
  rw [hA6, show (6 : ℕ) = 3 * 2 from rfl, pow_mul, hB3, one_pow]

end Imc2023P2
