/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2013, Problem 4

Let `n ≥ 3` and let `x_1, ..., x_n` be nonnegative reals. Define
`A = ∑ x_i`, `B = ∑ x_i^2`, `C = ∑ x_i^3`. Prove that
`(n+1) A^2 B + (n-2) B^2 ≥ A^4 + (2n-2) AC`.
-/

namespace Imc2013P4

open Finset

snip begin

/-- The elementary symmetric polynomial `e_2 = ∑_{i<j} x_i x_j`, written as
a sum over ordered pairs divided by 2 in spirit; we use `Finset.offDiag`
and divide by 2. We instead work with the explicit form using `Finset.Ioi`. -/
noncomputable def esym2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, x i * x j

/-- The elementary symmetric polynomial `e_3 = ∑_{i<j<k} x_i x_j x_k`. -/
noncomputable def esym3 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, ∑ k ∈ Finset.Ioi j, x i * x j * x k

/-- The basic Newton identity `A^2 - B = 2 e_2`. -/
lemma sum_sq_eq_sub_two_esym2 {n : ℕ} (x : Fin n → ℝ) :
    (∑ i, x i) ^ 2 = (∑ i, (x i) ^ 2) + 2 * esym2 x := by
  sorry

/-- The Newton identity `A^3 - 3 A B + 2 C = 6 e_3` for nonneg reals. -/
lemma sum_cube_newton {n : ℕ} (x : Fin n → ℝ) :
    (∑ i, x i) ^ 3 - 3 * (∑ i, x i) * (∑ i, (x i) ^ 2) + 2 * (∑ i, (x i) ^ 3) =
      6 * esym3 x := by
  sorry

/-- Newton's inequality for the second elementary symmetric polynomial. For nonneg
reals `x_1, ..., x_n` with `n ≥ 3`,
  `2(n-2) e_2^2 ≥ 3(n-1) e_1 e_3`. -/
lemma newton_ineq {n : ℕ} (hn : 3 ≤ n) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    3 * (n - 1 : ℝ) * (∑ i, x i) * esym3 x ≤ 2 * (n - 2 : ℝ) * (esym2 x) ^ 2 := by
  sorry

snip end

problem imc2013_p4 {n : ℕ} (hn : 3 ≤ n) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    let A := ∑ i, x i
    let B := ∑ i, (x i) ^ 2
    let C := ∑ i, (x i) ^ 3
    A ^ 4 + (2 * n - 2) * A * C ≤ (n + 1) * A ^ 2 * B + (n - 2) * B ^ 2 := by
  intro A B C
  -- Express everything in terms of A, B, C, e_2 and e_3.
  set e2 := esym2 x with he2_def
  set e3 := esym3 x with he3_def
  have hAB : A ^ 2 = B + 2 * e2 := sum_sq_eq_sub_two_esym2 x
  have hABC : A ^ 3 - 3 * A * B + 2 * C = 6 * e3 := sum_cube_newton x
  -- Reduce: LHS - RHS = 4(n-2) e_2^2 - 6(n-1) e_1 e_3
  have hkey : (n + 1 : ℝ) * A ^ 2 * B + (n - 2) * B ^ 2 - (A ^ 4 + (2 * n - 2) * A * C) =
      4 * (n - 2 : ℝ) * e2 ^ 2 - 6 * (n - 1 : ℝ) * A * e3 := by
    have hB : B = A ^ 2 - 2 * e2 := by linarith
    -- After substituting B, get C = 3 e_3 + A^3 - 3 A e_2.
    have hC : C = 3 * e3 + A ^ 3 - 3 * A * e2 := by
      have h1 : A ^ 3 - 3 * A * B + 2 * C = 6 * e3 := hABC
      rw [hB] at h1
      linarith
    rw [hB, hC]
    ring
  -- Apply Newton's inequality.
  have hni : 3 * (n - 1 : ℝ) * A * e3 ≤ 2 * (n - 2 : ℝ) * e2 ^ 2 := newton_ineq hn x hx
  -- Conclude.
  linarith

end Imc2013P4
