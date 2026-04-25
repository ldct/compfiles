/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2001, Problem 10
(IMC 2001, Day 2, Problem 4)

Let `A = (a_{kℓ})` be an `n × n` complex matrix such that for every `m`
and every `1 ≤ j₁ < ⋯ < jₘ ≤ n`, the principal minor
`det((a_{j_k, j_ℓ})_{k,ℓ=1..m}) = 0`.
Prove that `A^n = 0` and that there exists a permutation `σ` of
`{1, …, n}` such that `(a_{σ(k), σ(ℓ)})` is strictly upper triangular.

## Solution sketch

Form the digraph `G` whose vertices are `{1, …, n}` and whose edges are
`k → ℓ` iff `a_{kℓ} ≠ 0`. We claim `G` is acyclic. Suppose otherwise,
and pick a cycle of minimum length `m` through vertices
`j₁ < ⋯ < jₘ` realised by a cyclic permutation `σ₀`. Then for any other
permutation `σ ≠ σ₀` of `{j₁, …, jₘ}`, some product term
`a_{j_k, j_{σ(k)}}` must vanish, since otherwise the digraph would
contain another cycle of length `≤ m` on the same vertex set,
contradicting minimality. The Leibniz expansion of the principal
minor on these vertices then reduces to `± ∏_k a_{j_k, j_{σ₀(k)}}`,
which is nonzero by assumption — contradiction.

Hence `G` is acyclic and admits a topological ordering `σ` for which
`a_{σ(k), σ(ℓ)} ≠ 0 ⟹ k < ℓ`, i.e. the conjugated matrix is strictly
upper triangular. A strictly upper triangular `n × n` matrix is
nilpotent of index at most `n`, so `A^n = 0`.
-/

namespace Imc2001P10

open Matrix

snip begin

/-- A strictly upper triangular `n × n` matrix raised to the power `n`
is the zero matrix. -/
lemma strictly_upper_triangular_pow_eq_zero {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ i j : Fin n, j ≤ i → B i j = 0) :
    B ^ n = 0 := by
  -- We prove by induction on k that
  -- `(B^k) i j ≠ 0 ⟹ (i : ℕ) + k ≤ (j : ℕ)`.
  have key : ∀ k : ℕ, ∀ i j : Fin n,
      (B ^ k) i j ≠ 0 → (i : ℕ) + k ≤ (j : ℕ) := by
    intro k
    induction k with
    | zero =>
      intro i j h
      simp only [pow_zero, Matrix.one_apply, ne_eq, ite_eq_right_iff,
        Classical.not_imp] at h
      obtain ⟨hij, _⟩ := h
      rw [hij]; simp
    | succ k ih =>
      intro i j h
      rw [pow_succ, Matrix.mul_apply] at h
      -- Some term in the sum is nonzero.
      obtain ⟨l, _, hl⟩ : ∃ l ∈ Finset.univ, (B ^ k) i l * B l j ≠ 0 := by
        by_contra hall
        push Not at hall
        exact h (Finset.sum_eq_zero (fun l hl => hall l hl))
      have hBkil : (B ^ k) i l ≠ 0 := left_ne_zero_of_mul hl
      have hBlj : B l j ≠ 0 := right_ne_zero_of_mul hl
      have h1 : (i : ℕ) + k ≤ (l : ℕ) := ih i l hBkil
      have h2 : (l : ℕ) < (j : ℕ) := by
        by_contra hjl
        push Not at hjl
        have : (j : Fin n) ≤ (l : Fin n) := by exact_mod_cast hjl
        exact hBlj (hB l j this)
      omega
  ext i j
  simp only [Matrix.zero_apply]
  by_contra hne
  have hk := key n i j hne
  have hj : (j : ℕ) < n := j.isLt
  omega

/-- A power of `A.submatrix σ σ` agrees with the corresponding
submatrix of `A^k`. -/
lemma submatrix_pow_eq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    (A.submatrix σ σ) ^ k = (A ^ k).submatrix σ σ := by
  induction k with
  | zero =>
    ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.submatrix_apply]
    · simp [Matrix.submatrix_apply, h, σ.injective.eq_iff]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    exact Matrix.submatrix_mul_equiv (A^k) A σ σ σ

/-- Conjugating a matrix by a permutation preserves nilpotency: if the
permuted matrix has its `n`-th power equal to zero, so does the
original. -/
lemma pow_eq_zero_of_perm_pow_eq_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n))
    (hB : (A.submatrix σ σ) ^ n = 0) :
    A ^ n = 0 := by
  rw [submatrix_pow_eq] at hB
  ext i j
  have key := congr_fun (congr_fun hB (σ.symm i)) (σ.symm j)
  simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply,
    Matrix.zero_apply] at key
  exact key

snip end

problem imc2001_p10 (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hPrincipal :
      ∀ (s : Finset (Fin n)) (_h : s.Nonempty),
        (A.submatrix
            (Function.Embedding.subtype (· ∈ s))
            (Function.Embedding.subtype (· ∈ s))).det = 0) :
    A ^ n = 0 ∧ ∃ σ : Equiv.Perm (Fin n),
      ∀ k l : Fin n, l ≤ k → A (σ k) (σ l) = 0 := by
  -- Hardest combinatorial step: minimum-cycle / topological-ordering argument.
  -- We obtain the permutation σ as a single sorry; the nilpotency conclusion
  -- follows from the structure of strictly upper triangular matrices.
  -- TODO: formalize the acyclicity argument from the principal-minor hypothesis.
  have hPerm : ∃ σ : Equiv.Perm (Fin n),
      ∀ k l : Fin n, l ≤ k → A (σ k) (σ l) = 0 := by
    sorry
  refine ⟨?_, hPerm⟩
  obtain ⟨σ, hσ⟩ := hPerm
  apply pow_eq_zero_of_perm_pow_eq_zero A σ
  apply strictly_upper_triangular_pow_eq_zero
  intro k l hlk
  simp only [Matrix.submatrix_apply]
  exact hσ k l hlk

end Imc2001P10
