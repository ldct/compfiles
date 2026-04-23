/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2024, Problem 7

Let `n` be a positive integer. Suppose that `A` and `B` are invertible `n × n`
matrices with complex entries such that `A + B = I` and
`(A^2 + B^2)(A^4 + B^4) = A^5 + B^5`.
Find all possible values of `det(A*B)` for the given `n`.

Answer: the set `{(1/4)^k | 0 ≤ k ≤ n}`.
-/

namespace Imc2024P7

open Matrix Polynomial

/-- The set of possible values of `det(A*B)`. -/
determine answer (n : ℕ) : Set ℂ :=
  { z | ∃ k : ℕ, k ≤ n ∧ z = (1 / 4 : ℂ) ^ k }

snip begin

/-- If `A + B = 1`, then `A * B = B * A`. -/
lemma comm_of_add_eq_one {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hAB : A + B = 1) : A * B = B * A := by
  have hB : B = 1 - A := by
    have : A + B - A = 1 - A := by rw [hAB]
    rw [add_sub_cancel_left] at this
    exact this
  rw [hB]; noncomm_ring

/-- `A^2 + B^2 = 1 - 2*(A*B)` when `A + B = 1`. -/
lemma pow2_sum {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hAB : A + B = 1) :
    A ^ 2 + B ^ 2 = 1 - 2 • (A * B) := by
  have hB : B = 1 - A := by
    have : A + B - A = 1 - A := by rw [hAB]
    rw [add_sub_cancel_left] at this
    exact this
  subst hB
  noncomm_ring

/-- `A^4 + B^4 = 1 - 4*(A*B) + 2*(A*B)^2` when `A + B = 1`. -/
lemma pow4_sum {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hAB : A + B = 1) :
    A ^ 4 + B ^ 4 = 1 - 4 • (A * B) + 2 • (A * B) ^ 2 := by
  have hB : B = 1 - A := by
    have : A + B - A = 1 - A := by rw [hAB]
    rw [add_sub_cancel_left] at this
    exact this
  subst hB
  noncomm_ring

/-- `A^5 + B^5 = 1 - 5*(A*B) + 5*(A*B)^2` when `A + B = 1`. -/
lemma pow5_sum {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hAB : A + B = 1) :
    A ^ 5 + B ^ 5 = 1 - 5 • (A * B) + 5 • (A * B) ^ 2 := by
  have hB : B = 1 - A := by
    have : A + B - A = 1 - A := by rw [hAB]
    rw [add_sub_cancel_left] at this
    exact this
  subst hB
  noncomm_ring

/-- The main polynomial identity: under the hypotheses,
`4 (A*B)^3 - 5 (A*B)^2 + (A*B) = 0`. -/
lemma poly_identity {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hAB : A + B = 1)
    (hyp : (A ^ 2 + B ^ 2) * (A ^ 4 + B ^ 4) = A ^ 5 + B ^ 5) :
    4 • (A * B) ^ 3 - 5 • (A * B) ^ 2 + (A * B) = 0 := by
  have h2 := pow2_sum A B hAB
  have h4 := pow4_sum A B hAB
  have h5 := pow5_sum A B hAB
  rw [h2, h4, h5] at hyp
  -- hyp: (1 - 2C)(1 - 4C + 2C^2) = 1 - 5C + 5C^2
  set C := A * B with hC_def
  have hexpand : ((1 : Matrix (Fin n) (Fin n) ℂ) - 2 • C) * (1 - 4 • C + 2 • C ^ 2) =
      1 - 6 • C + 10 • C ^ 2 - 4 • C ^ 3 := by
    noncomm_ring
  rw [hexpand] at hyp
  -- hyp: 1 - 6C + 10C^2 - 4C^3 = 1 - 5C + 5C^2
  -- Subtract: 4C^3 - 5C^2 + C = 0, i.e. -(1 - 6C + 10C^2 - 4C^3) + (1 - 5C + 5C^2) = ...
  -- Direct: rearrange hyp.
  have := hyp
  -- 1 - 6C + 10C^2 - 4C^3 - (1 - 5C + 5C^2) = 0
  -- = -C + 5C^2 - 4C^3 = -(4C^3 - 5C^2 + C)
  have heq : (1 : Matrix (Fin n) (Fin n) ℂ) - 6 • C + 10 • C ^ 2 - 4 • C ^ 3
             - (1 - 5 • C + 5 • C ^ 2) = -(4 • C ^ 3 - 5 • C ^ 2 + C) := by
    noncomm_ring
  have hsub : (1 : Matrix (Fin n) (Fin n) ℂ) - 6 • C + 10 • C ^ 2 - 4 • C ^ 3
             - (1 - 5 • C + 5 • C ^ 2) = 0 := by
    rw [this]; abel
  rw [heq] at hsub
  exact neg_eq_zero.mp hsub

/-- If `C` is a matrix with `4 C^3 - 5 C^2 + C = 0` and `C` is invertible,
then `(C - 1)(C - (1/4)•1) = 0`. -/
lemma factor_poly {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ)
    (hC_unit : IsUnit C)
    (hpoly : 4 • C ^ 3 - 5 • C ^ 2 + C = 0) :
    (C - 1) * (C - (1 / 4 : ℂ) • 1) = 0 := by
  -- 4 C^3 - 5 C^2 + C = C (4 C^2 - 5 C + 1)
  have hfact : C * (4 • C ^ 2 - 5 • C + 1) = 0 := by
    have : C * (4 • C ^ 2 - 5 • C + 1) = 4 • C ^ 3 - 5 • C ^ 2 + C := by noncomm_ring
    rw [this, hpoly]
  -- Cancel C on the left.
  have hcancel : 4 • C ^ 2 - 5 • C + 1 = 0 := by
    obtain ⟨u, hu⟩ := hC_unit
    have key : (↑u⁻¹ : Matrix (Fin n) (Fin n) ℂ) * (C * (4 • C ^ 2 - 5 • C + 1)) =
        (↑u⁻¹ : Matrix (Fin n) (Fin n) ℂ) * 0 := by rw [hfact]
    rw [mul_zero, ← mul_assoc] at key
    have hinv : (↑u⁻¹ : Matrix (Fin n) (Fin n) ℂ) * C = 1 := by
      rw [← hu]; exact Units.inv_mul u
    rw [hinv, one_mul] at key
    exact key
  -- Now (C - 1)(C - (1/4)•1) expanded: C*C - (1/4)•C - C + (1/4)•1
  -- 4•((C - 1)(C - (1/4)•1)) = 4•C^2 - C - 4C + 1 = 4C^2 - 5C + 1 = 0
  have h4 : (4 : ℂ) • ((C - 1) * (C - (1 / 4 : ℂ) • 1)) = 0 := by
    have exp1 : (C - 1) * (C - (1 / 4 : ℂ) • 1) =
        C * C - (1 / 4 : ℂ) • C - C + (1 / 4 : ℂ) • 1 := by
      rw [sub_mul, mul_sub, mul_sub, one_mul]
      rw [show C * ((1/4 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) = (1/4 : ℂ) • C from by
        rw [Matrix.mul_smul, mul_one]]
      rw [show (1 : Matrix (Fin n) (Fin n) ℂ) * ((1/4 : ℂ) • 1) = (1/4 : ℂ) • 1 from by
        rw [one_mul]]
      abel
    rw [exp1]
    rw [smul_add, smul_sub, smul_sub]
    -- 4 • (C * C) - 4 • ((1/4) • C) - 4 • C + 4 • ((1/4) • 1) = 0
    -- = 4 • (C*C) - C - 4•C + 1 = 4•C^2 - 5•C + 1
    rw [show (4 : ℂ) • (C * C) = 4 • C ^ 2 from by
      rw [show C * C = C ^ 2 from (sq C).symm]
      rw [show (4 : ℂ) = ((4 : ℕ) : ℂ) from by norm_num, Nat.cast_smul_eq_nsmul]]
    rw [show (4 : ℂ) • ((1/4 : ℂ) • C) = C from by rw [smul_smul]; norm_num]
    rw [show (4 : ℂ) • C = (4 : ℕ) • C from by
      rw [show (4 : ℂ) = ((4 : ℕ) : ℂ) from by norm_num, Nat.cast_smul_eq_nsmul]]
    rw [show (4 : ℂ) • ((1/4 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) = 1 from by
      rw [smul_smul]; norm_num]
    -- Now goal: 4•C^2 - C - 4•C + 1 = 0
    -- From hcancel: 4•C^2 - 5•C + 1 = 0
    have : (4 : ℕ) • C ^ 2 - C - (4 : ℕ) • C + 1 = 4 • C ^ 2 - 5 • C + 1 := by
      show (4 : ℕ) • C ^ 2 - C - (4 : ℕ) • C + 1 = (4 : ℕ) • C ^ 2 - (5 : ℕ) • C + 1
      rw [show (5 : ℕ) • C = (4 : ℕ) • C + C from by
        rw [show (5 : ℕ) = 4 + 1 from rfl, add_nsmul, one_nsmul]]
      abel
    rw [this, hcancel]
  -- From 4•(_) = 0 and 4 ≠ 0, conclude _ = 0.
  have h4ne : (4 : ℂ) ≠ 0 := by norm_num
  have hgoal : (4 : ℂ) • ((C - 1) * (C - (1/4 : ℂ) • 1)) = (4 : ℂ) • 0 := by
    rw [smul_zero]; exact h4
  exact smul_right_injective _ h4ne hgoal

snip end

problem imc2024_p7 (n : ℕ) (z : ℂ) :
    z ∈ answer n ↔
      ∃ (A B : Matrix (Fin n) (Fin n) ℂ),
        IsUnit A ∧ IsUnit B ∧ A + B = 1 ∧
        (A ^ 2 + B ^ 2) * (A ^ 4 + B ^ 4) = A ^ 5 + B ^ 5 ∧
        (A * B).det = z := by
  -- TODO: Both directions require a longer argument.
  -- Forward: for each k ≤ n, exhibit A = diag(1/2,...,1/2, e^{iπ/3},...,e^{iπ/3}) with
  --   k copies of 1/2, showing det(A*B) = (1/4)^k.
  -- Backward: C = A*B satisfies (C-1)(C-(1/4)•1) = 0 (via factor_poly and poly_identity).
  --   Over ℂ (algebraically closed), eigenvalues of C are in {1, 1/4}; det(C) is their product,
  --   which is (1/4)^k for some k ≤ n.
  sorry

end Imc2024P7
