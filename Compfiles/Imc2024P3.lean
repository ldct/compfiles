/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics, .Algebra] }

/-!
# International Mathematical Competition 2024, Problem 3

For which positive integers `n` does there exist an `n × n` matrix `A`
with entries in `{0, 1}` such that `A^2` is the matrix of all ones?

Answer: iff `n` is a perfect square.
-/

namespace Imc2024P3

open Matrix Finset

/-- The all-ones `n × n` matrix. -/
def allOnes (n : ℕ) : Matrix (Fin n) (Fin n) ℕ := fun _ _ => 1

/-- The set of positive integers `n` for which there exists an `n × n` matrix
`A` with entries in `{0, 1}` such that `A^2` is the all-ones matrix. -/
determine answer : Set ℕ :=
  { n | 0 < n ∧ ∃ k : ℕ, n = k ^ 2 }

snip begin

/-- In the natural numbers, row sums of `A` are the entries of `A * J` where
`J` is the all-ones column (here a matrix with all entries 1). -/
lemma row_sum_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) (i : Fin n) :
    (A * allOnes n) i i = ∑ j, A i j := by
  simp [allOnes, Matrix.mul_apply]

/-- The `(i,i)` entry of `J^2` is `n`. -/
lemma allOnes_sq_diag (n : ℕ) (i : Fin n) :
    (allOnes n * allOnes n) i i = n := by
  simp [allOnes, Matrix.mul_apply]

snip end

problem imc2024_p3 (n : ℕ) (hn : 0 < n) :
    (∃ A : Matrix (Fin n) (Fin n) ℕ,
      (∀ i j, A i j = 0 ∨ A i j = 1) ∧ A * A = allOnes n) ↔
    ∃ k : ℕ, n = k ^ 2 := by
  constructor
  · rintro ⟨A, hA01, hA2⟩
    -- From A*A = J, we have A*(A*A) = A*J and (A*A)*A = J*A.
    -- A * (A*A) = A*J, so A^3 = A*J.
    -- (A*A) * A = J*A, so A^3 = J*A.
    -- Hence A*J = J*A.
    -- (A*J)_{ij} = row sum of A at row i (independent of j)
    -- (J*A)_{ij} = column sum of A at column j
    -- So all row sums equal all column sums = some constant k.
    -- Then J*J = (A*A)*(A*A) = A*(A*A)*A = A*J*A.
    -- (A*J*A)_{ij} = (sum of row sums of A) * (col sum at j) / ... actually:
    -- (A*J)_{ij} = k, so (A*J*A)_{ij} = sum_m k * A_{mj} = k * (col sum j) = k^2.
    -- And (J^2)_{ii} = n, so n = k^2.
    set k := ∑ j, A ⟨0, hn⟩ j with hk_def
    -- Claim: every row sum equals k.
    have hrow : ∀ i, ∑ j, A i j = k := by
      intro i
      -- (A*A*A) i j = sum_m (A*A)_{im} * A_{mj} = sum_m A_{mj} = col sum of A at j
      -- (A*A*A) i j = sum_m A_{im} * (A*A)_{mj} = sum_m A_{im} = row sum of A at i
      -- So row sum at i = col sum at j for all i, j.
      have key : ∀ i' j', ∑ m, A i' m = ∑ m, A m j' := by
        intro i' j'
        have h1 : (A * A * A) i' j' = ∑ m, A i' m := by
          rw [Matrix.mul_assoc, hA2]
          simp [allOnes, Matrix.mul_apply]
        have h2 : (A * A * A) i' j' = ∑ m, A m j' := by
          rw [hA2]
          simp [allOnes, Matrix.mul_apply]
        rw [h1] at h2; exact h2
      -- So all row sums are equal.
      have : ∑ j, A i j = ∑ m, A m ⟨0, hn⟩ := key i ⟨0, hn⟩
      rw [this]
      exact (key ⟨0, hn⟩ ⟨0, hn⟩).symm
    -- Compute (A*A*A*A) ⟨0,hn⟩ ⟨0,hn⟩ two ways.
    have hAAAA : (A * A * (A * A)) ⟨0, hn⟩ ⟨0, hn⟩ = n := by
      rw [hA2]; exact allOnes_sq_diag n _
    -- Other way: A*A*A*A = A*(A*A)*A = A*J*A
    have hAJA : (A * A * (A * A)) ⟨0, hn⟩ ⟨0, hn⟩ = k * k := by
      -- A*A*(A*A) = A*(A*A)*A·... careful: A*A*(A*A) = ((A*A)*A)*A = (A*A*A)*A
      -- = (A*A*A)·A where (A*A*A) i j = row sum = k (independent of j)
      have h3 : (A * A * A) = fun i _ => k := by
        funext i j
        have : (A * A * A) i j = ∑ m, A i m := by
          rw [Matrix.mul_assoc, hA2]
          simp [allOnes, Matrix.mul_apply]
        rw [this]
        exact hrow i
      have heq : A * A * (A * A) = (A * A * A) * A := by
        rw [← Matrix.mul_assoc]
      rw [heq, h3]
      simp [Matrix.mul_apply]
      -- sum_m k * A m 0 = k * (col sum 0) = k * k (since col sum = row sum)
      rw [← Finset.mul_sum]
      congr 1
      -- sum_m A m ⟨0,hn⟩ = k
      have : ∀ i' j', ∑ m, A i' m = ∑ m, A m j' := by
        intro i' j'
        have h1 : (A * A * A) i' j' = ∑ m, A i' m := by
          rw [Matrix.mul_assoc, hA2]
          simp [allOnes, Matrix.mul_apply]
        have h2 : (A * A * A) i' j' = ∑ m, A m j' := by
          rw [hA2]
          simp [allOnes, Matrix.mul_apply]
        rw [h1] at h2; exact h2
      exact ((this ⟨0, hn⟩ ⟨0, hn⟩).symm).trans rfl
    rw [hAAAA] at hAJA
    exact ⟨k, by linarith [hAJA, sq k]⟩
  · -- Construction for n = k^2.
    rintro ⟨k, rfl⟩
    -- Handle k = 0 separately.
    rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
    · subst hk0; simp at hn
    -- Now k ≥ 1. We construct A as a block matrix.
    -- A is k^2 × k^2. Using Fin (k^2) ≃ Fin k × Fin k via divMod.
    -- Define A(i,j) = 1 iff (j.2 - i.2) ≡ (j.1 - ?) ... actually, per solution:
    -- The (I,J)th block (size k×k) is B_{J.2}, cyclic shift with
    -- (i,j)-entry 1 iff j - i ≡ J.2 (mod k).
    -- So A((I,i),(J,j)) = 1 iff j - i ≡ J.2 (mod k), i.e. 1 iff j ≡ i + J.2 mod k.
    -- Equivalently: using indices from Fin k × Fin k (block row, intra-block row),
    -- A((I,i),(J,j)) = 1 iff (j - i) mod k = J.2... wait J.2 doesn't exist; let me re-read.
    -- From solution: A = [B_0 B_1 ... B_{k-1}; B_0 B_1 ... B_{k-1}; ...]
    -- So the block at position (block_row_idx, block_col_idx) is B_{block_col_idx}.
    -- Hence A((r, i), (c, j)) = (B_c) i j = 1 iff j - i ≡ c (mod k).
    have hk2 : k ^ 2 = k * k := sq k
    let e : Fin (k^2) ≃ Fin k × Fin k :=
      (Fin.castOrderIso hk2).toEquiv.trans finProdFinEquiv.symm
    let A : Matrix (Fin (k^2)) (Fin (k^2)) ℕ := fun I J =>
      if ((e J).2 : ℤ) - (e I).2 ≡ (e J).1 [ZMOD k] then 1 else 0
    refine ⟨A, ?_, ?_⟩
    · intro I J
      simp only [A]
      split_ifs <;> [right; left] <;> rfl
    · -- Show A * A = allOnes.
      -- TODO: for each (I, K), the system of conditions
      --   (e J).2 - (e I).2 ≡ (e J).1 (mod k)   [A I J = 1]
      --   (e K).2 - (e J).2 ≡ (e K).1 (mod k)   [A J K = 1]
      -- has a unique solution J. Concretely:
      --   (e J).1 = (e K).2 - (e K).1 - (e I).2  (as Fin k, via ZMod k)
      --   (e J).2 = (e I).2 + (e J).1
      -- So the sum ∑_J A I J * A J K has exactly one nonzero term, equal to 1.
      -- The proof requires careful manipulation of Fin k subtraction / ZMod k arithmetic,
      -- using (e.symm ⟨cJ, jJ⟩) as the unique witness and showing:
      --   (i)  the witness satisfies both conditions (so its contribution is 1),
      --   (ii) every J ≠ witness fails at least one condition.
      sorry

end Imc2024P3
