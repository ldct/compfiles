/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1999, Problem 1 (Day 1)

(a) Show that for any `m ∈ ℕ` (with `m ≥ 1`) there exists a real `m × m`
    matrix `A` with `A^3 = A + I`.

(b) Show that `det A > 0` for any such matrix.

## Solution sketch (official solution)

(a) Let `λ` be a real root of the polynomial `p(x) = x^3 - x - 1`. Such a
    root exists by the intermediate value theorem since `p(0) = -1 < 0` and
    `p(2) = 5 > 0`. Then `A := λ • I` satisfies
    `A^3 = λ^3 • I = (λ + 1) • I = λ • I + I = A + I`.

(b) The polynomial `p(x) = x^3 - x - 1` has discriminant
    `(-1/3)^3 + (-1/2)^2 = 23/108 > 0`, so it has exactly one real root
    `λ_1` (which is positive, since `p(0) = -1 < 0 < p(2)`) and two complex
    conjugate roots `λ_2, λ_3 = λ_2.bar`. Any `m × m` real matrix `A` with
    `A^3 = A + I` satisfies `p(A) = 0`, so its eigenvalues (over `ℂ`) lie
    among `{λ_1, λ_2, λ_3}`. Since `A` is real, the conjugate complex
    eigenvalues `λ_2, λ_3` occur with the same multiplicity `β`. Letting
    `α` be the multiplicity of `λ_1`, we have
    `det A = λ_1^α · (λ_2 λ_3)^β = λ_1^α · |λ_2|^(2β) > 0`,
    using that `λ_1 > 0` and that `λ_2 λ_3 = |λ_2|^2 > 0` (and
    `λ_1 (λ_2 λ_3) = -p(0) = 1`, in particular all three are non-zero).

## Status

(a) is fully proved.

(b) is a `sorry` skeleton. A clean Mathlib proof requires: complex
    spectrum of a real matrix annihilated by a polynomial lies in the roots
    of that polynomial (with conjugate-paired multiplicities), plus the
    factorization `det A = ∏ eigenvalues` via `Matrix.det_eq_prod_roots_charpoly_of_splits`
    over `ℂ`. The route is sketched in detail below.
-/

namespace Imc1999P1

open scoped Matrix BigOperators
open Polynomial

/-- The polynomial `p(x) = x^3 - x - 1` over `ℝ`. -/
noncomputable def p : ℝ[X] := X ^ 3 - X - 1

snip begin

lemma p_eval (x : ℝ) : p.eval x = x ^ 3 - x - 1 := by
  simp [p]

/-- `p(0) = -1 < 0`. -/
lemma p_eval_zero : p.eval 0 = -1 := by
  simp [p_eval]

/-- `p(2) = 5 > 0`. -/
lemma p_eval_two : p.eval 2 = 5 := by
  simp [p_eval]; norm_num

/-- There exists a real `λ ∈ (0, 2)` with `p(λ) = 0`, by IVT. -/
lemma exists_real_root : ∃ lam : ℝ, 0 < lam ∧ lam < 2 ∧ lam ^ 3 - lam - 1 = 0 := by
  -- IVT on [0, 2]
  have hcont : ContinuousOn (fun x : ℝ => x ^ 3 - x - 1) (Set.Icc 0 2) := by
    fun_prop
  have h0 : ((fun x : ℝ => x ^ 3 - x - 1) 0) = -1 := by norm_num
  have h2 : ((fun x : ℝ => x ^ 3 - x - 1) 2) = 5 := by norm_num
  have hlt : (fun x : ℝ => x ^ 3 - x - 1) 0 ≤ 0 ∧ 0 ≤ (fun x : ℝ => x ^ 3 - x - 1) 2 := by
    constructor
    · rw [h0]; norm_num
    · rw [h2]; norm_num
  obtain ⟨lam, hmem, hzero⟩ :=
    intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 2) hcont ⟨hlt.1, hlt.2⟩
  refine ⟨lam, ?_, ?_, hzero⟩
  · -- 0 < lam: if lam = 0, p(0) = -1 ≠ 0.
    rcases lt_or_eq_of_le hmem.1 with hlt | hle
    · exact hlt
    · exfalso; rw [← hle] at hzero; norm_num at hzero
  · -- lam < 2: if lam = 2, p(2) = 5 ≠ 0.
    rcases lt_or_eq_of_le hmem.2 with hlt | hge
    · exact hlt
    · exfalso; rw [hge] at hzero; norm_num at hzero

snip end

/-- **Part (a)**: For any `m`, there exists a real `m × m` matrix `A`
with `A^3 = A + 1`. -/
problem imc1999_p1a (m : ℕ) :
    ∃ A : Matrix (Fin m) (Fin m) ℝ, A ^ 3 = A + 1 := by
  obtain ⟨lam, _, _, hlam⟩ := exists_real_root
  refine ⟨lam • (1 : Matrix (Fin m) (Fin m) ℝ), ?_⟩
  -- (lam • I)^3 = lam^3 • I = (lam + 1) • I = lam • I + I
  have hcube : (lam • (1 : Matrix (Fin m) (Fin m) ℝ)) ^ 3
      = lam ^ 3 • (1 : Matrix (Fin m) (Fin m) ℝ) := by
    rw [_root_.smul_pow, one_pow]
  rw [hcube]
  have : lam ^ 3 = lam + 1 := by linarith
  rw [this, add_smul, one_smul]

/-- **Part (b)**: For any real `m × m` matrix `A` with `A^3 = A + I`,
`det A > 0`. -/
problem imc1999_p1b (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ) (hA : A ^ 3 = A + 1) :
    0 < A.det := by
  -- Sketch (TODO):
  --
  -- 1. Pass to ℂ: let A_ℂ := A.map (algebraMap ℝ ℂ). Then `A_ℂ^3 = A_ℂ + 1`,
  --    so the polynomial p_ℂ(X) = X^3 - X - 1 ∈ ℂ[X] annihilates A_ℂ.
  --
  -- 2. The polynomial p_ℂ factors over ℂ as
  --      p_ℂ(X) = (X - λ_1)(X - λ_2)(X - λ_3)
  --    where λ_1 ∈ ℝ, λ_1 > 0, and λ_2, λ_3 = conj λ_2 are complex
  --    conjugates with |λ_2|^2 = λ_2 · λ_3 > 0.
  --    (By exists_real_root for λ_1 > 0; the factorization over ℂ follows
  --    from `Polynomial.splits_iff_card_roots` with `IsAlgClosed ℂ`.
  --    Vieta: λ_1 · λ_2 · λ_3 = -(-1) = 1, so all three are non-zero
  --    and λ_2 · λ_3 = 1 / λ_1 > 0; alternatively λ_2 · λ_3 = |λ_2|^2 ≥ 0,
  --    and = 0 would force λ_2 = 0, contradicting p_ℂ(0) = -1 ≠ 0.)
  --
  -- 3. The eigenvalues of A_ℂ all lie in {λ_1, λ_2, λ_3} (as roots of any
  --    annihilating polynomial). Use `Matrix.IsEigenvalue.isRoot_charpoly`
  --    and `Polynomial.roots_pow_sub_pow` style lemmas. Equivalently, the
  --    characteristic polynomial of A_ℂ divides p_ℂ^m, so its roots (the
  --    eigenvalues) are in {λ_1, λ_2, λ_3}.
  --
  -- 4. Since A is real, the characteristic polynomial of A_ℂ has real
  --    coefficients (it equals charpoly of A, mapped into ℂ). So the
  --    multiset of eigenvalues is closed under complex conjugation. Hence
  --    if α = mult(λ_1) and β = mult(λ_2), then mult(λ_3) = β as well, and
  --    α + 2β = m.
  --
  -- 5. Using `Matrix.det_eq_prod_roots_charpoly_of_splits` over ℂ
  --    (or directly `Matrix.det_eq_prod_roots_charpoly` since ℂ is
  --    algebraically closed), we get
  --      (algebraMap ℝ ℂ) (A.det) = det A_ℂ
  --                                = λ_1^α · (λ_2 · λ_3)^β
  --                                = λ_1^α · |λ_2|^(2β).
  --
  -- 6. The right-hand side is a positive real, so A.det > 0 in ℝ.
  sorry

end Imc1999P1
