/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2002, Problem 7
(IMC 2002, Day 2, Problem 1)

Compute `det A` where `A = [a_{ij}]` is the `n × n` real matrix with
`a_{ij} = (-1)^{|i-j|}` if `i ≠ j`, and `a_{ii} = 2`.

Answer: `n + 1`.
-/

namespace Imc2002P7

open Matrix

/-- The `n × n` real matrix `A` with `A i i = 2` and
`A i j = (-1)^|i.val - j.val|` for `i ≠ j`. -/
def matA (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then 2 else (-1 : ℝ) ^ ((i.val : ℤ) - j.val).natAbs

/-- The answer: `det(matA n) = n + 1`. -/
determine answer (n : ℕ) : ℝ := n + 1

snip begin

/-- The "alternating" vector `u : Fin n → ℝ` with `u i = (-1)^i.val`. -/
def altVec (n : ℕ) : Fin n → ℝ := fun i => (-1 : ℝ) ^ i.val

/-- `(-1 : ℝ) ^ k.natAbs = (-1 : ℝ) ^ k` (as zpow) for any integer `k`. -/
lemma neg_one_pow_natAbs (k : ℤ) : ((-1 : ℝ)) ^ k.natAbs = (-1 : ℝ) ^ k := by
  rcases Int.natAbs_eq k with h | h
  · -- k = k.natAbs
    conv_rhs => rw [h]
    rw [zpow_natCast]
  · -- k = -k.natAbs
    conv_rhs => rw [h]
    rw [zpow_neg, zpow_natCast]
    -- need (-1)^k.natAbs = ((-1)^k.natAbs)⁻¹, i.e., ((-1)^k.natAbs)^2 = 1.
    have : ((-1 : ℝ)) ^ k.natAbs * ((-1 : ℝ)) ^ k.natAbs = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      simp
    field_simp
    linarith [this]

/-- Key identity: `(-1)^i * (-1)^j = (-1)^|i-j|`. -/
lemma altVec_mul_eq (n : ℕ) (i j : Fin n) :
    altVec n i * altVec n j = (-1 : ℝ) ^ ((i.val : ℤ) - j.val).natAbs := by
  unfold altVec
  rw [← pow_add]
  rw [neg_one_pow_natAbs]
  -- Now show (-1 : ℝ)^(i.val + j.val) (as nat pow) = (-1 : ℝ)^((i.val : ℤ) - j.val) (as zpow).
  have h1 : ((-1 : ℝ)) ^ (i.val + j.val) = (-1 : ℝ) ^ ((i.val + j.val : ℕ) : ℤ) := by
    rw [zpow_natCast]
  rw [h1]
  -- Show (i.val + j.val : ℤ) and (i.val - j.val : ℤ) differ by an even number, so same parity.
  have heq : ((i.val + j.val : ℕ) : ℤ) = ((i.val : ℤ) - j.val) + 2 * j.val := by push_cast; ring
  rw [heq]
  rw [zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
  have h3 : ((-1 : ℝ)) ^ (2 * (j.val : ℤ)) = 1 := by
    have : (2 * (j.val : ℤ)) = ((2 * j.val : ℕ) : ℤ) := by push_cast; ring
    rw [this, zpow_natCast, pow_mul]
    simp
  rw [h3, mul_one]

/-- The product `replicateCol (Fin 1) u * replicateRow (Fin 1) v` evaluated at `(i, j)`
gives `u i * v j`. -/
lemma replicateCol_mul_replicateRow_fin_one (n : ℕ) (u v : Fin n → ℝ) (i j : Fin n) :
    (replicateCol (Fin 1) u * replicateRow (Fin 1) v) i j = u i * v j := by
  simp [Matrix.mul_apply, replicateCol, replicateRow]

/-- The matrix `matA n` decomposes as `1 + replicateCol (Fin 1) u * replicateRow (Fin 1) u`
where `u = altVec n`. -/
lemma matA_eq (n : ℕ) :
    matA n = 1 + replicateCol (Fin 1) (altVec n) * replicateRow (Fin 1) (altVec n) := by
  ext i j
  simp only [Matrix.add_apply]
  rw [replicateCol_mul_replicateRow_fin_one, altVec_mul_eq]
  unfold matA
  by_cases h : i = j
  · subst h
    simp only [if_true, Matrix.one_apply_eq]
    have : ((i.val : ℤ) - i.val).natAbs = 0 := by simp
    rw [this]
    norm_num
  · rw [if_neg h, Matrix.one_apply_ne h]
    ring

/-- The dot product `altVec n ⬝ᵥ altVec n = n`. -/
lemma altVec_dotProduct_self (n : ℕ) : altVec n ⬝ᵥ altVec n = (n : ℝ) := by
  unfold altVec dotProduct
  have h : ∀ i : Fin n, (-1 : ℝ) ^ i.val * (-1 : ℝ) ^ i.val = 1 := by
    intro i
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  simp_rw [h]
  simp

snip end

problem imc2002_p7 (n : ℕ) : (matA n).det = answer n := by
  have hdet : Matrix.det
      (1 + replicateCol (Fin 1) (altVec n) * replicateRow (Fin 1) (altVec n)) =
      1 + altVec n ⬝ᵥ altVec n :=
    Matrix.det_one_add_replicateCol_mul_replicateRow (altVec n) (altVec n)
  rw [matA_eq n, hdet, altVec_dotProduct_self, answer]
  ring

end Imc2002P7
