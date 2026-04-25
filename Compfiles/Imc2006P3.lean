/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2006, Problem 3

(Day 1, Problem 3.)

Let `A` be an `n × n` integer matrix whose determinant equals
`b_1 * b_2 * ... * b_k` where `b_1, ..., b_k` are integers (with `k ≥ 1`).
Prove that there exist integer matrices `B_1, ..., B_k` such that
`A = B_1 * B_2 * ... * B_k` and `det B_i = b_i` for each `i`.

## Proof outline

We induct on the length `k` of the factorization. The base case `k = 1` is
trivial: take `B_1 = A`. For the inductive step, it suffices to prove the case
`k = 2`: given `A` with `det A = b * c`, find integer matrices `B`, `C` with
`A = B * C`, `det B = b`, `det C = c`.

The `k = 2` case is the technical heart of the problem and uses the Smith
normal form / Hermite normal form over `ℤ`. By multiplying by unimodular
integer matrices on either side we can reduce to the case where `A` is upper
triangular. Then we construct `B` and `C` upper triangular by setting
`B_{nn} = gcd(b, A_{nn})` and `C_{nn} = A_{nn} / B_{nn}`, recursing on the
`(n-1) × (n-1)` principal submatrix.
-/

namespace Imc2006P3

open Matrix

snip begin

/-- The `k = 2` case of the problem: given integer matrix `A` with
`det A = b * c`, there exist integer matrices `B`, `C` with `A = B * C`,
`det B = b`, `det C = c`. This is the technical core of the problem and
requires Hermite/Smith normal form over `ℤ`. We leave the proof as a
TODO. -/
lemma split_two {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (b c : ℤ)
    (hbc : b * c = A.det) :
    ∃ B C : Matrix (Fin n) (Fin n) ℤ, A = B * C ∧ B.det = b ∧ C.det = c := by
  -- TODO: This is the technical heart of the problem.
  -- Standard proof: reduce A to upper triangular via unimodular ℤ-matrices
  -- (Hermite normal form), then construct B and C upper triangular by setting
  -- B_{nn} = gcd(b, A_{nn}), C_{nn} = A_{nn} / B_{nn}, recursing on the
  -- principal submatrix.
  sorry

snip end

/-- Statement: for any `bs : List ℤ` of length at least one whose product equals
`det A`, there exists a list `Bs` of integer matrices of the same length with
determinants matching `bs` and product equal to `A`. -/
problem imc2006_p3
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (bs : List ℤ) (hne : bs ≠ []) (hprod : bs.prod = A.det) :
    ∃ Bs : List (Matrix (Fin n) (Fin n) ℤ),
      Bs.length = bs.length ∧
      Bs.map Matrix.det = bs ∧
      Bs.prod = A := by
  -- Induct on bs.
  induction bs generalizing A with
  | nil => exact (hne rfl).elim
  | cons b bs ih =>
    by_cases hbs : bs = []
    · -- Single element: bs = [b]. Take Bs = [A].
      subst hbs
      simp only [List.prod_cons, List.prod_nil, mul_one] at hprod
      refine ⟨[A], ?_, ?_, ?_⟩
      · simp
      · simp [hprod]
      · simp
    · -- bs ≠ []. Then b * bs.prod = A.det. Apply split_two with c = bs.prod.
      have hsplit : b * bs.prod = A.det := by
        have := hprod
        simpa [List.prod_cons] using this
      obtain ⟨B, C, hBC, hBdet, hCdet⟩ := split_two A b bs.prod hsplit
      -- Recurse on C with bs.
      have hCprod : bs.prod = C.det := hCdet.symm
      obtain ⟨Cs, hCs_len, hCs_map, hCs_prod⟩ := ih C hbs hCprod
      refine ⟨B :: Cs, ?_, ?_, ?_⟩
      · simp [hCs_len]
      · simp [hBdet, hCs_map]
      · simp [hCs_prod, hBC]

end Imc2006P3
