/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1998, Problem 5 (Day 1)

Let `P` be a real polynomial of degree `n` whose roots are all real.
Show that for every real `x`,

  `(n - 1) (P'(x))^2 ≥ n · P(x) · P''(x)`.

## Proof outline (official solution)

If `P(x) ≠ 0`, write the roots (with multiplicity) as `x_1, …, x_n`. Then

  `P'(x)/P(x) = ∑_i 1/(x - x_i)`,
  `P''(x)/P(x) = 2 · ∑_{i<j} 1/((x - x_i)(x - x_j))`.

A direct computation gives

  `(n - 1) (P'(x)/P(x))^2 - n · (P''(x)/P(x))
    = ∑_i (n - 1) / (x - x_i)^2 - 2 ∑_{i<j} 1/((x - x_i)(x - x_j))
    = ∑_{i<j} (1/(x - x_i) - 1/(x - x_j))^2 ≥ 0`.

Multiplying by `P(x)^2` gives the required inequality.

If `P(x) = 0`, then `x` is a root, so the right-hand side is `0`, while the
left-hand side `(n - 1) (P'(x))^2 ≥ 0` (and is zero iff `x` is a multiple
root, i.e. `P'(x) = 0` as well).
-/

namespace Imc1998P5

open Polynomial

/-- IMC 1998 Problem 5: if `P` is a polynomial over `ℝ` of degree `n` that
splits over `ℝ` (equivalently, has only real roots, counted with multiplicity),
then `(n - 1) (P'(x))^2 ≥ n · P(x) · P''(x)` for every `x : ℝ`. -/
problem imc1998_p5
    (P : ℝ[X]) (hP : P.Splits) (x : ℝ) :
    ((P.natDegree : ℝ) - 1) * (P.derivative.eval x) ^ 2 ≥
      (P.natDegree : ℝ) * P.eval x * P.derivative.derivative.eval x := by
  -- TODO: Full proof. The official approach:
  --
  -- Case `P.eval x ≠ 0`. Use `Splits.eval_derivative_div_eval_of_ne_zero`
  -- to write `P'(x)/P(x) = ∑_{r ∈ P.roots} 1/(x - r)`. A second application
  -- (or a direct computation expanding `P''` using
  -- `Splits.eval_eq_prod_roots`) gives
  -- `P''(x)/P(x) = 2 ∑_{i < j} 1/((x - r_i)(x - r_j))`.
  -- Multiplying through by `P(x)^2` and rearranging the algebraic identity
  -- `(n - 1) (∑ a_i)^2 - 2 n ∑_{i<j} a_i a_j = ∑_{i<j} (a_i - a_j)^2`
  -- (with `a_i := 1/(x - r_i)`) shows the difference is a sum of squares.
  --
  -- Case `P.eval x = 0`. Then `x` is a real root of `P`. The RHS is `0`.
  -- The LHS is `(n - 1) (P'(x))^2 ≥ 0`, since `n ≥ 1` whenever `P` has a
  -- root (and the case `P = 0` is degenerate but trivially gives `0 ≥ 0`).
  --
  -- The main technical hurdle is the second-derivative formula and the
  -- combinatorial sum-of-squares identity. Mathlib has
  -- `Splits.eval_derivative_div_eval_of_ne_zero` for the first derivative
  -- but no direct analogue for the second derivative; one would need to
  -- differentiate the product formula `P = leadingCoeff · ∏ (X - r)` twice
  -- and rearrange.
  by_cases hPx : P.eval x = 0
  · -- Easy case: P(x) = 0, so RHS = 0; LHS = (n-1) * P'(x)^2.
    -- We need (n-1) ≥ 0; this holds because P has a root, so either P = 0
    -- (then natDegree = 0 and both sides are 0) or natDegree ≥ 1.
    rw [hPx]
    by_cases hP0 : P = 0
    · simp [hP0]
    · have hdeg : 1 ≤ P.natDegree := by
        have hxmem : x ∈ P.roots := by
          rw [Polynomial.mem_roots hP0]
          exact hPx
        have hne : P.roots ≠ 0 := fun h => by
          rw [h] at hxmem; exact Multiset.notMem_zero x hxmem
        have hcard : 1 ≤ P.roots.card := by
          rw [Nat.one_le_iff_ne_zero]
          intro hcard0
          exact hne (Multiset.card_eq_zero.mp hcard0)
        have hcard_eq : P.roots.card = P.natDegree :=
          Polynomial.splits_iff_card_roots.mp hP
        omega
      have hn1 : (0 : ℝ) ≤ (P.natDegree : ℝ) - 1 := by
        have : (1 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hdeg
        linarith
      have hsq : (0 : ℝ) ≤ (P.derivative.eval x) ^ 2 := sq_nonneg _
      have hLHS : (0 : ℝ) ≤ ((P.natDegree : ℝ) - 1) * (P.derivative.eval x) ^ 2 :=
        mul_nonneg hn1 hsq
      simpa using hLHS
  · -- Hard case: P(x) ≠ 0. Use the partial fractions identity.
    sorry


end Imc1998P5
