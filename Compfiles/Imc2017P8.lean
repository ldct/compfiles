/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2017, Problem 8

Define the sequence `A₁, A₂, …` of matrices by
`A₁ = ![[0,1],[1,0]]` and recursively
`A_{n+1} = block matrix with A_n on diagonal blocks and I on off-diagonal blocks`.

Prove that `A_n` has `n+1` distinct integer eigenvalues
`λ₀ < λ₁ < ⋯ < λ_n` with multiplicities `C(n,0), C(n,1), …, C(n,n)` respectively.

We model the matrix using indices `Fin n → Bool` (vertices of the n-cube),
with `A_n` the adjacency matrix of the n-cube. The recursive block construction
in the problem corresponds to splitting on the first coordinate of `Fin (n+1)`.

The eigenvalues are `n - 2k` for `k = 0,…,n`; equivalently `λ_k = -n + 2k`.

The full statement is in terms of the characteristic polynomial:
`charpoly (A n) = ∏ k, (X - C (-n + 2k))^(n.choose k)`.
This encodes: `n+1` distinct integer eigenvalues, in increasing order, with the
required binomial multiplicities.
-/

namespace Imc2017P8

open Matrix BigOperators Polynomial

/-- The cube-edge adjacency matrix on `Fin n → Bool`: entry `1` if `u` and `v`
differ in exactly one coordinate, else `0`. This is the matrix `A_n` from the
problem (after re-indexing `Fin (2^n)` as `Fin n → Bool`). -/
def Acube (n : ℕ) : Matrix (Fin n → Bool) (Fin n → Bool) ℤ :=
  fun u v => if (Finset.univ.filter (fun i => u i ≠ v i)).card = 1 then 1 else 0

/-- The eigenvalues claimed by the problem, indexed by `k : Fin (n+1)`:
`λ_k = -n + 2k`. -/
def lam (n : ℕ) (k : Fin (n+1)) : ℤ := -n + 2 * k

snip begin

/-- The eigenvalues `lam n k` are strictly increasing in `k`. -/
lemma lam_strictMono (n : ℕ) : StrictMono (lam n) := by
  intro i j hij
  unfold lam
  have : (i : ℤ) < j := by exact_mod_cast hij
  linarith

/-- Distinctness of eigenvalues. -/
lemma lam_injective (n : ℕ) : Function.Injective (lam n) :=
  (lam_strictMono n).injective

/-!
## Proof outline (currently sketch / TODO)

The proof goes by induction on `n`.

* Base case `n = 0`: `Acube 0` is the unique 1×1 zero matrix; charpoly is `X`,
  matching `(X - C 0)^1`.

* Inductive step: Reindex `Fin (n+1) → Bool ≃ Bool × (Fin n → Bool)`. Under this
  reindexing, `Acube (n+1)` becomes the 2×2 block matrix
  `fromBlocks (Acube n) 1 1 (Acube n)`.

  Key block-matrix determinant identity: when `A` and `1` commute (which is
  automatic) the characteristic polynomial of this block matrix factors as
    `charpoly (Acube n + 1) * charpoly (Acube n - 1)`.

  This is because for any commutative ring `R[X]` and commuting `A, B`,
    `det (fromBlocks A B B A) = det(A + B) * det(A - B)`.

  Combined with `charpoly_translate` (sub_scalar), this gives the recurrence
    `p_{n+1}(X) = p_n(X-1) * p_n(X+1)`.

  Pascal's identity `C(n+1, k) = C(n, k) + C(n, k-1)` then matches the
  exponents of the corresponding linear factors.

The proof below provides the statement only, with the inductive computation
deferred to a future commit.
-/

snip end

/-- Statement of IMC 2017 Problem 8.

The matrix `Acube n` (i.e. `A_n` in the problem) has the property that for every
`k : Fin (n+1)`, the value `lam n k = -n + 2k` is an eigenvalue, the eigenvalues
are all distinct integers (encoded by `lam_strictMono`), and the algebraic
multiplicities are the binomial coefficients `C(n, k)`. We express this via the
characteristic polynomial:

  `charpoly (Acube n) = ∏ k, (X - C (lam n k)) ^ (n.choose k)`.

Note the eigenvalues `lam n k = -n + 2k` are strictly increasing in `k` and
hence pairwise distinct integers. -/
problem imc2017_p8 (n : ℕ) :
    (Acube n).charpoly =
      ∏ k : Fin (n+1), (Polynomial.X - Polynomial.C (lam n k)) ^ (n.choose (k : ℕ)) := by
  sorry

end Imc2017P8
