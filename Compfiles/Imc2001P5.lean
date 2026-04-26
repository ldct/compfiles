/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2001, Problem 5
(IMC 2001, Day 1, Problem 5)

Let `A` be an `n × n` complex matrix with `A ≠ λ · I` for every `λ ∈ ℂ`.
Prove that `A` is similar to a matrix with at most one nonzero diagonal entry.

## Solution sketch

Induction on `n`. For `n = 2`, if some off-diagonal entry is nonzero, a single
elementary conjugation clears one diagonal entry; if both off-diagonal entries
are zero, the hypothesis `A ≠ λ I` forces the two diagonal entries to be
distinct, and conjugating by an upper-triangular unipotent produces a nonzero
off-diagonal entry, reducing to the previous case. For `n > 2`, apply the
inductive hypothesis to an `(n−1) × (n−1)` principal submatrix (chosen to be
non-scalar) to reduce its diagonal to `(0, …, 0, α)`, then re-partition the
result as a `1 + (n−1)` block and apply the hypothesis again.
-/

namespace Imc2001P5

open Matrix

snip begin

/-- At most `k` diagonal entries of `B` are nonzero. -/
def AtMostOneNonzeroDiag {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (Finset.univ.filter fun i : Fin n => B i i ≠ 0).card ≤ 1

snip end

/-- Statement: for every complex `n × n` matrix `A` that is not a scalar matrix,
there is an invertible `P` such that `P⁻¹ * A * P` has at most one nonzero
diagonal entry. -/
problem imc2001_p5 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ lam : ℂ, A ≠ lam • (1 : Matrix (Fin n) (Fin n) ℂ)) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, IsUnit P.det ∧
      AtMostOneNonzeroDiag (P⁻¹ * A * P) := by
  -- Proof by strong induction on `n`. The argument is classical: see the
  -- solution sketch above. A fully formal Mathlib proof requires nontrivial
  -- work on block matrices and conjugation by elementary matrices; we leave
  -- the induction step as a TODO.
  -- TODO: Finish the induction. The case `n ≤ 1` is vacuous (for `n = 0` there
  -- are no diagonal entries; for `n = 1` every matrix is scalar so `hA` is
  -- inconsistent). The case `n = 2` is handled by an explicit conjugation
  -- matrix depending on which off-diagonal entry is nonzero. The general step
  -- applies the inductive hypothesis to a non-scalar principal `(n−1)` block.
  sorry

end Imc2001P5
