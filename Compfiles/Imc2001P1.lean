/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2001, Problem 1
(IMC 2001, Day 1, Problem 1)

Fill an `n × n` matrix with entries `1, 2, …, n²` row by row, so that the
entry at row `i` and column `j` is `n * (i - 1) + j` (for `1 ≤ i, j ≤ n`).
Select `n` entries with exactly one in each row and exactly one in each column.

Show that every such selection has the same sum, namely `n * (n² + 1) / 2`.
-/

namespace Imc2001P1

/-- The entry at row `i` and column `j` of the matrix (using 0-indexed `Fin n`),
i.e. `n * i + j + 1`. -/
def entry (n : ℕ) (i j : Fin n) : ℕ := n * i.val + j.val + 1

snip begin

/-- Sum of `i.val` over `i : Fin n` equals `n * (n - 1) / 2`, expressed without
division: twice the sum equals `n * (n - 1)`. -/
lemma two_mul_sum_val (n : ℕ) :
    2 * ∑ i : Fin n, i.val = n * (n - 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => i)]
  rw [mul_comm 2 _, Finset.sum_range_id_mul_two]

/-- A permutation of `Fin n` is a bijection on the universe, so summing `(σ i).val`
is the same as summing `i.val`. -/
lemma sum_perm_val (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ∑ i : Fin n, (σ i).val = ∑ i : Fin n, i.val :=
  Equiv.sum_comp σ (fun i : Fin n => i.val)

snip end

problem imc2001_p1 (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    2 * ∑ i : Fin n, entry n i (σ i) = n * (n ^ 2 + 1) := by
  unfold entry
  -- Split the sum: ∑ (n * i + σ(i) + 1) = n * ∑ i + ∑ σ(i) + n.
  have hsplit :
      ∑ i : Fin n, (n * i.val + (σ i).val + 1)
        = n * (∑ i : Fin n, i.val) + (∑ i : Fin n, (σ i).val) + n := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [Finset.card_univ]
  rw [hsplit, sum_perm_val n σ]
  -- Now: 2 * (n * S + S + n) = n * (n² + 1) where S = ∑ i.val = n(n-1)/2.
  have h2S : 2 * ∑ i : Fin n, i.val = n * (n - 1) := two_mul_sum_val n
  -- Strategy: multiply out and compare.
  have : 2 * (n * ∑ i : Fin n, i.val + ∑ i : Fin n, i.val + n)
        = (n + 1) * (2 * ∑ i : Fin n, i.val) + 2 * n := by ring
  rw [this, h2S]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_add_cancel hn).symm⟩
    -- Now n = m + 1, so n - 1 = m.
    simp only [Nat.add_sub_cancel]
    ring

end Imc2001P1
