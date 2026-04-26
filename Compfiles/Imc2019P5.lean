/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .NumberTheory] }

/-!
# International Mathematical Competition 2019, Problem 5
(IMC 2019, Day 1, Problem 5)

Determine whether there exist odd `n` and integer `n × n` matrices `A`, `B`
with `det(B) = 1`, `AB = BA`, and `A^4 + 4 A^2 B^2 + 16 B^4 = 2019 I`.

## Answer

No such matrices exist.

## Proof sketch

Reduce the equation modulo 4: in `Matrix (Fin n) (Fin n) (ZMod 4)`,
`4 A^2 B^2 = 0` and `16 B^4 = 0`, so `A^4 = 2019 I = 3 I` (mod 4).
Taking determinants: `(det A)^4 = 3^n` in `ZMod 4`. Since `n` is odd,
`3^n = 3` in `ZMod 4`. But for any `x : ZMod 4`, `x^4 ∈ {0, 1}`.
Contradiction.
-/

namespace Imc2019P5

open Matrix

snip begin

/-- In `ZMod 4`, the fourth power of any element is either `0` or `1`. -/
lemma zmod4_pow_four (x : ZMod 4) : x ^ 4 = 0 ∨ x ^ 4 = 1 := by
  -- Enumerate the four values of ZMod 4.
  fin_cases x <;> decide

/-- In `ZMod 4`, `3^n = 3` for odd `n`. -/
lemma three_pow_odd_zmod4 {n : ℕ} (hodd : Odd n) : (3 : ZMod 4) ^ n = 3 := by
  obtain ⟨k, rfl⟩ := hodd
  rw [pow_add, pow_mul, pow_one]
  have h9 : (3 : ZMod 4) ^ 2 = 1 := by decide
  rw [h9, one_pow, one_mul]

snip end

problem imc2019_p5 :
    ¬ ∃ (n : ℕ) (_ : Odd n) (A B : Matrix (Fin n) (Fin n) ℤ),
        B.det = 1 ∧ A * B = B * A ∧
        A ^ 4 + 4 * A ^ 2 * B ^ 2 + 16 * B ^ 4 = (2019 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) := by
  rintro ⟨n, hodd, A, B, _hdetB, _hcomm, hEq⟩
  -- Reduce modulo 4 via the ring hom Matrix.mapMatrix.
  let f : ℤ →+* ZMod 4 := Int.castRingHom (ZMod 4)
  let F : Matrix (Fin n) (Fin n) ℤ →+* Matrix (Fin n) (Fin n) (ZMod 4) := f.mapMatrix
  have hApp : ∀ (M : Matrix (Fin n) (Fin n) ℤ), F M = M.map f := fun _ => rfl
  -- Apply F to the equation.
  have hMap : F (A ^ 4 + 4 * A ^ 2 * B ^ 2 + 16 * B ^ 4) =
      F ((2019 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) := by rw [hEq]
  -- Let A' = F A, B' = F B.
  set A' : Matrix (Fin n) (Fin n) (ZMod 4) := F A with hA'_def
  set B' : Matrix (Fin n) (Fin n) (ZMod 4) := F B with hB'_def
  -- LHS reduces via the ring hom structure.
  have hLHS : F (A ^ 4 + 4 * A ^ 2 * B ^ 2 + 16 * B ^ 4) =
      A' ^ 4 + 4 * A' ^ 2 * B' ^ 2 + 16 * B' ^ 4 := by
    simp only [map_add, map_mul, map_pow, map_ofNat, hA'_def, hB'_def]
  -- RHS reduces: F (2019 • 1) = 3 • 1 in ZMod 4.
  have hRHS : F ((2019 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) =
      (3 : ZMod 4) • (1 : Matrix (Fin n) (Fin n) (ZMod 4)) := by
    rw [hApp]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs with h
    · show f ((2019 : ℤ) • (1 : ℤ)) = (3 : ZMod 4) • (1 : ZMod 4)
      simp; decide
    · show f ((2019 : ℤ) • (0 : ℤ)) = (3 : ZMod 4) • (0 : ZMod 4)
      simp
  rw [hLHS, hRHS] at hMap
  -- In ZMod 4, 4 = 0 and 16 = 0.
  have h4mat : (4 : Matrix (Fin n) (Fin n) (ZMod 4)) = 0 := by
    ext i j
    rw [Matrix.ofNat_apply, Matrix.zero_apply]
    split_ifs <;> decide
  have h16mat : (16 : Matrix (Fin n) (Fin n) (ZMod 4)) = 0 := by
    ext i j
    rw [Matrix.ofNat_apply, Matrix.zero_apply]
    split_ifs <;> decide
  -- Simplify hMap: 4 → 0 and 16 → 0, so LHS = A'^4.
  have hMap' : A' ^ 4 = (3 : ZMod 4) • (1 : Matrix (Fin n) (Fin n) (ZMod 4)) := by
    rw [h4mat, h16mat] at hMap
    simpa using hMap
  -- Now hMap' : A'^4 = 3 • 1.
  -- Take determinants.
  have hDet : A'.det ^ 4 = (3 : ZMod 4) ^ n := by
    have h1 : (A' ^ 4).det = ((3 : ZMod 4) • (1 : Matrix (Fin n) (Fin n) (ZMod 4))).det := by
      rw [hMap']
    rw [Matrix.det_pow, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h1
    exact h1
  -- 3^n = 3 in ZMod 4 since n is odd.
  rw [three_pow_odd_zmod4 hodd] at hDet
  -- But (det A')^4 ∈ {0, 1}.
  rcases zmod4_pow_four A'.det with h | h
  · rw [h] at hDet; exact absurd hDet (by decide)
  · rw [h] at hDet; exact absurd hDet (by decide)

end Imc2019P5
