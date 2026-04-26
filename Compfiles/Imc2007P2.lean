/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2007, Problem 2

Let `n ≥ 2` be an integer. What are the possible values of the rank of an
`n × n` matrix whose entries are exactly the numbers `1, 2, …, n²` (each
appearing once)?

Answer: the rank can take any value from `2` up to `n`. In particular,
the minimum is `2` and the maximum is `n`.
-/

namespace Imc2007P2

open Matrix

/-- An "entry matrix" is an `n × n` real matrix whose entries form a bijection
with `{1, 2, …, n²}`. We encode this by asserting the existence of a bijection
`f : Fin n × Fin n ≃ Fin (n * n)` such that `M i j = (f (i, j)).val + 1`. -/
def IsEntryMatrix (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ f : Fin n × Fin n ≃ Fin (n * n), ∀ i j, M i j = ((f (i, j)).val + 1 : ℕ)

snip begin

/-! ### The "standard" construction achieving rank 2 -/

/-- The standard matrix `T i j = i*n + j + 1`. Its entries are `1, 2, …, n²`
listed row by row. Each row is `(1, 2, …, n)` shifted by a constant, so the
columns span a `2`-dimensional subspace. -/
def stdMat (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ((i.val * n + j.val + 1 : ℕ) : ℝ)

/-- The bijection witnessing that `stdMat` is an entry matrix. -/
def stdEquiv (n : ℕ) : Fin n × Fin n ≃ Fin (n * n) := finProdFinEquiv

lemma stdMat_isEntry (n : ℕ) : IsEntryMatrix n (stdMat n) := by
  refine ⟨stdEquiv n, ?_⟩
  intro i j
  simp [stdMat, stdEquiv, finProdFinEquiv]
  ring

/-- Each column of `stdMat n` equals `u + ((j + 1) : ℝ) • (all ones)`, where
`u i = i * n`. So the column span lies in a 2-dimensional subspace. -/
lemma stdMat_rank_le_two (n : ℕ) : (stdMat n).rank ≤ 2 := by
  rw [Matrix.rank_eq_finrank_span_cols]
  let u : Fin n → ℝ := fun i => (i.val * n : ℕ)
  let v : Fin n → ℝ := fun _ => 1
  have hcol : ∀ j : Fin n, (stdMat n)ᵀ j = u + ((j.val + 1 : ℕ) : ℝ) • v := by
    intro j
    ext i
    simp [stdMat, u, v, Matrix.transpose_apply]
    ring
  have hsub : Submodule.span ℝ (Set.range (stdMat n)ᵀ) ≤
      Submodule.span ℝ ({u, v} : Set (Fin n → ℝ)) := by
    rw [Submodule.span_le]
    rintro w ⟨j, rfl⟩
    rw [hcol j]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.subset_span (by simp)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  classical
  have hfin : Module.finrank ℝ
      (Submodule.span ℝ ({u, v} : Set (Fin n → ℝ))) ≤ 2 := by
    have hspan_eq : (Submodule.span ℝ ({u, v} : Set (Fin n → ℝ))) =
        Submodule.span ℝ (({u, v} : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
      congr 1
      ext w; simp
    rw [hspan_eq]
    calc Module.finrank ℝ (Submodule.span ℝ
            (({u, v} : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)))
        ≤ ({u, v} : Finset (Fin n → ℝ)).card :=
          finrank_span_finset_le_card _
      _ ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  exact (Submodule.finrank_mono hsub).trans hfin

/-! ### A construction achieving rank n

We build an entry matrix whose determinant is nonzero. We use a
Vandermonde-like construction: place `1, 2, …, n` on the diagonal, and
`n+1, n+2, …, n²` in the off-diagonal positions row by row. This gives a
matrix whose determinant is bounded below by a positive quantity, but
formalizing that is delicate. Instead we give an ad-hoc swap argument:
start from `stdMat n` and swap two entries; the resulting entry matrix has
a different, nonzero determinant.

For the formalization, we give only the *existence* via `sorry` and defer
the explicit construction.
-/

snip end

/-- The answer (minimum rank): `2`. -/
determine minRank : ℕ := 2

/-- The answer (maximum rank): `n`. -/
determine maxRank (n : ℕ) : ℕ := n

/-- IMC 2007 P2:

For every `n ≥ 2`,
* every `n × n` entry matrix has rank at least `2`;
* there exists an `n × n` entry matrix with rank exactly `2` (the minimum);
* there exists an `n × n` entry matrix with rank exactly `n` (the maximum).
-/
problem imc2007_p2 (n : ℕ) (hn : 2 ≤ n) :
    (∀ M : Matrix (Fin n) (Fin n) ℝ, IsEntryMatrix n M → minRank ≤ M.rank) ∧
    (∃ M : Matrix (Fin n) (Fin n) ℝ, IsEntryMatrix n M ∧ M.rank = minRank) ∧
    (∃ M : Matrix (Fin n) (Fin n) ℝ, IsEntryMatrix n M ∧ M.rank = maxRank n) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Lower bound: rank ≥ 2 for every entry matrix.
    -- Proof sketch (using Bertrand's postulate): by Bertrand there is a prime
    -- `p` with `n²/2 < p ≤ n²`. This value `p` appears exactly once in the
    -- matrix, say at position `(i₀, j₀)`. If the matrix has rank ≤ 1, it
    -- factors as `M i j = u i * v j` with `u, v` positive. Analyzing
    -- divisibility by `p`, we find that all entries in column `j₀` are
    -- divisible by `p` and ≤ n² < 2p, hence all equal `p`, contradicting
    -- distinctness.
    -- TODO: formalize the Bertrand-based rank-1 impossibility argument.
    sorry
  · -- Achieved minimum: the standard matrix has rank `2`.
    refine ⟨stdMat n, stdMat_isEntry n, ?_⟩
    -- Upper bound by `stdMat_rank_le_two`; lower bound follows from the
    -- same argument as above. We deduce from both. For now, sorry.
    sorry
  · -- Achieved maximum: some entry matrix has rank `n`.
    -- Construction: e.g. diagonal has `1, 2, …, n`, off-diagonal has the
    -- remaining values arranged to yield nonzero determinant.
    -- TODO: formalize the explicit construction.
    sorry

end Imc2007P2
