/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1996, Problem 1 (Day 1)

Let `a_j = a₀ + j d` for `j = 0, …, n`, where `a₀, d` are fixed real numbers.
Define the symmetric `(n+1) × (n+1)` matrix
`A i j = a_{|i - j|} = a₀ + |i - j| d`.
Then
`det A = (-1)^n (a₀ + a_n) · 2^{n-1} · d^n`   for `n ≥ 1`,
and `det A = a₀`                              for `n = 0`.

Note `a₀ + a_n = 2 a₀ + n d`.

## Proof outline (official solution)

Add column 0 of `A` to column `n`: the new column `n` becomes the constant
vector `(a₀ + a_n) (1, 1, …, 1)ᵀ`. Hence
  `det A = (a₀ + a_n) · det A'`
where `A'` is the same matrix with its last column replaced by all-ones.

Now subtract row `k` from row `k+1` for `k = n-1, n-2, …, 0` (from bottom to
top). The new entry in row `k+1`, column `j ≤ n-1` becomes
`(a₀ + |k+1-j| d) - (a₀ + |k-j| d) = d · (|k+1-j| - |k-j|)`,
which equals `+d` when `j ≤ k` and `-d` when `j ≥ k+1`. The last column
becomes `0` for `k+1 ≥ 1` (since the constant vector becomes the zero
difference). So `A'` is reduced to a matrix whose first row is the original
top row of `A'` and whose subsequent rows have the form `(d, d, …, d, -d, …,
-d, 0)` with the sign change at column `k+1`.

Expand the determinant along the last column (only the top-row entry `1`
contributes):
`det A' = (-1)^n · det B`
where `B` is the `n × n` matrix `B k j = d (sgn(k - j))` (i.e., `+d` if
`j ≤ k`, else `-d`). Subtracting consecutive columns of `B` reduces it to a
lower triangular matrix with `d` on the diagonal and `-2d` on the strict
sub-diagonal, whose determinant is `2^{n-1} d^n`.

Combining: `det A = (a₀ + a_n) · (-1)^n · 2^{n-1} · d^n`.

The full Lean formalization of these row/column operations on a determinant
is genuinely involved, so it is left as a `sorry` with a detailed outline.
The base cases `n = 0` and `n = 1` are proved explicitly.
-/

namespace Imc1996P1

open scoped Matrix
open Matrix

/-- The arithmetic progression `a_j = a₀ + j d`. -/
def a (a₀ d : ℝ) (j : ℕ) : ℝ := a₀ + j * d

/-- The symmetric AP matrix `A i j = a_{|i - j|}` of size `(n+1) × (n+1)`. -/
def A (n : ℕ) (a₀ d : ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => a a₀ d (max (i : ℕ) (j : ℕ) - min (i : ℕ) (j : ℕ))

/-- The proposed formula for the determinant. -/
noncomputable def detFormula (n : ℕ) (a₀ d : ℝ) : ℝ :=
  if n = 0 then a₀
  else (-1 : ℝ) ^ n * (a₀ + a a₀ d n) * 2 ^ (n - 1) * d ^ n

snip begin

/-- Base case: `1 × 1` matrix has determinant `a₀`. -/
lemma det_A_zero (a₀ d : ℝ) : (A 0 a₀ d).det = a₀ := by
  rw [Matrix.det_fin_one]
  simp [A, a]

/-- Case `n = 1`: `2 × 2` matrix `[[a₀, a₀+d], [a₀+d, a₀]]`, determinant
`-d (2 a₀ + d) = -(a₀ + a₁) d = (-1)^1 (a₀ + a₁) 2^0 d^1`. -/
lemma det_A_one (a₀ d : ℝ) : (A 1 a₀ d).det = -(a₀ + a a₀ d 1) * d := by
  rw [Matrix.det_fin_two]
  simp [A, a]
  ring

snip end

/-- The main problem: compute `det A`. -/
problem imc1996_p1 (n : ℕ) (a₀ d : ℝ) :
    (A n a₀ d).det = detFormula n a₀ d := by
  -- Handle small base cases and leave the general case as `sorry`.
  match n with
  | 0 =>
      rw [det_A_zero]
      simp [detFormula]
  | 1 =>
      rw [det_A_one]
      simp [detFormula, a]
  | n + 2 =>
      -- General case: see the outline in the file header. This is a careful
      -- determinant computation via row and column operations and is left
      -- as `sorry`.
      --
      -- TODO: Formalize the following steps.
      --
      -- Step 1. Add column 0 to column n+1 of A. Define
      --   A' i j := if j = (last : Fin (n+2)) then a₀ + a_(n+1) else A i j.
      -- This adds column 0 to column last; by `Matrix.det_updateColumn_add_self`
      -- (or `Matrix.det_add_column`), `det A = det A''` where A'' has last
      -- column equal to (a₀ + a_(n+1)) * (1, …, 1). Factor out the scalar:
      --   det A = (a₀ + a_(n+1)) * det A_ones,
      -- where A_ones replaces the last column of A by all ones.
      --
      -- Step 2. Apply row operations: subtract row k from row k+1 for
      -- k = n+1, n, …, 1 (bottom to top). Each such operation preserves the
      -- determinant. The resulting matrix C has:
      --   * row 0 unchanged: C 0 j = A_ones 0 j
      --   * for k ≥ 1, C k j = A_ones k j - A_ones (k-1) j
      --     - For j ≤ n: C k j = a_{|k-j|} - a_{|k-1-j|} = d * sign,
      --       which equals +d if j ≤ k-1, and -d if j ≥ k.
      --     - For j = last (the all-ones column): C k j = 1 - 1 = 0.
      --
      -- Step 3. Expand det C along the last column. Only C 0 last = 1 is
      -- nonzero. The cofactor is the determinant of the (n+1) × (n+1) minor
      -- obtained by deleting row 0 and column last, which is the matrix
      --   B k j = +d if j ≤ k, -d if j > k    (k, j : Fin (n+1)).
      -- The sign of the cofactor is (-1)^(0 + (n+1)) = (-1)^(n+1).
      --
      -- Step 4. Compute det B. Subtract column j+1 from column j for j = 0,
      -- 1, …, n-1 (from left to right). The result is a lower triangular
      -- matrix with d on the diagonal in the rightmost column and 2d on the
      -- (k, k-1) sub-diagonal entries elsewhere. More precisely the resulting
      -- matrix has `B' k j = d` if `k = j` (last column j = n), `B' k j = 2d`
      -- if `k = j + 1`, and 0 otherwise on row 0; sign-counting yields
      --   det B = 2^n * d^(n+1).
      -- (Equivalently, det B = (2d)^n * d via factoring.)
      --
      -- Step 5. Combine:
      --   det A = (a₀ + a_(n+1)) * det A_ones
      --         = (a₀ + a_(n+1)) * (-1)^(n+1) * det B
      --         = (a₀ + a_(n+1)) * (-1)^(n+1) * 2^n * d^(n+1)
      --         = (-1)^(n+2) * (a₀ + a_(n+1)) * (-1) * (-1)^(n+1) ... ; matching
      -- the formula with index `n+2` gives the desired
      --   (-1)^(n+2) * (a₀ + a_(n+2)) * 2^((n+2)-1) * d^(n+2).
      -- (Index alignment: in the problem statement the size is (n+1)×(n+1)
      -- for index n; here we are in the case "n+2" which corresponds to a
      -- (n+3)×(n+3) matrix and the formula becomes the given one.)
      sorry

end Imc1996P1
