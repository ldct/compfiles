/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra, .Combinatorics] }

/-!
# International Mathematical Competition 2004, Problem 12
(IMC 2004, Day 2, Problem 6)

Let `A₀ = B₀ = (1)` be the `1 × 1` matrix with single entry `1`.
For `n > 0`, define recursively the `2ⁿ × 2ⁿ` matrices

  `Aₙ = ⎡ A_{n-1}  A_{n-1} ⎤`,    `Bₙ = ⎡ A_{n-1}  A_{n-1} ⎤`.
       `⎣ A_{n-1}  B_{n-1} ⎦`           `⎣ A_{n-1}     0    ⎦`

Let `S(M)` denote the sum of all entries of `M`.  Prove that
`S(Aₙ^{k-1}) = S(Aₖ^{n-1})` for all positive integers `n, k`.
-/

namespace Imc2004P12

open scoped Matrix

/-- We index `2ⁿ × 2ⁿ` matrices by `Fin n → Bool` (binary strings of length `n`),
viewed equivalently as `Fin (2^n)` via `Fintype.equivFin`. -/
abbrev Idx (n : ℕ) := Fin n → Bool

instance (n : ℕ) : Fintype (Idx n) := inferInstance
instance (n : ℕ) : DecidableEq (Idx n) := inferInstance

/-- The leading bit of an index. -/
def head {n : ℕ} (i : Idx (n + 1)) : Bool := i 0

/-- The tail (last `n` bits) of an index. -/
def tail {n : ℕ} (i : Idx (n + 1)) : Idx n := fun k => i k.succ

/-- The matrices `Aₙ` and `Bₙ` defined by mutual recursion on `n`.

`A` and `B` return a pair `(Aₙ, Bₙ)`.  We use natural-number entries. -/
def AB : (n : ℕ) → Matrix (Idx n) (Idx n) ℕ × Matrix (Idx n) (Idx n) ℕ
  | 0 => (fun _ _ => 1, fun _ _ => 1)
  | n + 1 =>
    let (A, B) := AB n
    let A' : Matrix (Idx (n + 1)) (Idx (n + 1)) ℕ := fun i j =>
      match head i, head j with
      | false, false => A (tail i) (tail j)
      | false, true  => A (tail i) (tail j)
      | true,  false => A (tail i) (tail j)
      | true,  true  => B (tail i) (tail j)
    let B' : Matrix (Idx (n + 1)) (Idx (n + 1)) ℕ := fun i j =>
      match head i, head j with
      | false, false => A (tail i) (tail j)
      | false, true  => A (tail i) (tail j)
      | true,  false => A (tail i) (tail j)
      | true,  true  => 0
    (A', B')

/-- `Aₙ`. -/
def A (n : ℕ) : Matrix (Idx n) (Idx n) ℕ := (AB n).1

/-- `Bₙ`. -/
def B (n : ℕ) : Matrix (Idx n) (Idx n) ℕ := (AB n).2

/-- The sum of all entries of a matrix. -/
def S {m : Type*} [Fintype m] (M : Matrix m m ℕ) : ℕ :=
  ∑ i, ∑ j, M i j

snip begin

/-
Solution outline (combinatorial).

Let `f(n, k)` denote the number of `n × k` `0/1`-matrices with no `2 × 2`
all-ones submatrix in adjacent rows and columns.

**Claim.** For `n, k ≥ 1`, `S(Aₙ^{k-1}) = f(n, k)`.

This is proved by interpreting `(Aₙ)_{ij}` as `1` iff the binary expansions
of `i, j ∈ {0, …, 2ⁿ - 1}` (read as length-`n` columns) can occur as
consecutive columns of such a matrix; equivalently, there is no index `r`
with `i_r = i_{r+1} = j_r = j_{r+1} = 1`.  The block-recursive definition
of `Aₙ` matches this:

* If the leading bits `i_n, j_n` are not both `1`, the constraint reduces
  to the lower `n - 1` bits, so the entry equals `(A_{n-1})_{i', j'}`.
* If `i_n = j_n = 1`, then we additionally must avoid `i_{n-1} = j_{n-1} = 1`,
  which is the recursion defining `B_{n-1}`.

Then
`S(Aₙ^{k-1}) = ∑_{i₁, …, iₖ} (Aₙ)_{i₁ i₂} · (Aₙ)_{i₂ i₃} ⋯ (Aₙ)_{i_{k-1} iₖ}`
counts sequences of `k` columns (each a binary string of length `n`) such
that every consecutive pair is admissible — that is, exactly the `n × k`
matrices in question, so `S(Aₙ^{k-1}) = f(n, k)`.

By symmetry of the `n × k` table (transpose), `f(n, k) = f(k, n)`, so
`S(Aₙ^{k-1}) = f(n, k) = f(k, n) = S(Aₖ^{n-1})`.

The full formalization of this combinatorial bijection is substantial.  We
record the statement here.
-/

snip end

problem imc2004_p12 (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    S ((A n) ^ (k - 1)) = S ((A k) ^ (n - 1)) := by
  -- TODO: combinatorial proof.
  -- Step 1.  Show that `(Aₙ) i j = 1` iff there is no index `r` with
  --          `i r = i (r+1) = j r = j (r+1) = true`, i.e. iff the
  --          length-`n` binary words `i, j` are "compatible" as adjacent
  --          columns of a 0/1 matrix with no 2×2 all-ones submatrix.
  --          Prove similarly that `(Bₙ) i j = 1` iff in addition
  --          `i 0 = j 0 = false`, by induction on `n`.
  -- Step 2.  Expand `(Aₙ^{k-1}) i₁ iₖ = ∑_{i₂, …, i_{k-1}} ∏ (Aₙ)_{iₛ iₛ₊₁}`
  --          and conclude `S(Aₙ^{k-1})` counts `n × k` matrices in the
  --          problem family, indexed by columns.
  -- Step 3.  Conclude by transpose symmetry: `f(n, k) = f(k, n)`.
  sorry

end Imc2004P12
