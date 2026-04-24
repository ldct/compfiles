/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2006, Problem 4

(Day 1, Problem 4.)

Let `f` be a rational function (i.e., the quotient of two real polynomials). Suppose
that `f(n)` is an integer for infinitely many integers `n`. Prove that `f` is a
polynomial.

We formalize this as: given real polynomials `p, q` with `q ≠ 0`, if the set of
integers `n` for which `q(n) ≠ 0` and `p(n) / q(n)` is an integer is infinite,
then `q` divides `p` in `ℝ[X]` (equivalently, `p / q`, as a rational function,
equals a polynomial).
-/

namespace Imc2006P4

open Polynomial

problem imc2006_p4
    (p q : ℝ[X]) (hq : q ≠ 0)
    (hS : {n : ℤ | q.eval (n : ℝ) ≠ 0 ∧ ∃ k : ℤ, p.eval (n : ℝ) = k * q.eval (n : ℝ)}.Infinite) :
    q ∣ p := by
  -- The standard solution proceeds as follows.
  --
  -- Write `p = q * s + r` with `r = 0` or `deg r < deg q` (polynomial division).
  -- The goal is to show `r = 0`, which gives `q ∣ p`.
  --
  -- Since `deg r < deg q`, we have `r.eval x / q.eval x → 0` as `|x| → ∞`.
  -- Thus for sufficiently large `|n|` with `n ∈ S` (our infinite set), we have
  -- `|r.eval n / q.eval n| < 1`.
  --
  -- Moreover, a system of linear equations determined by `S` forces the
  -- coefficients of `p` and `q` (up to common scaling) to be rational, then by
  -- multiplying by a common denominator we may assume they are integer.
  -- Then `p = q * s + r` has `s, r` with rational coefficients; multiply by
  -- `N` the common denominator of `s`'s coefficients to clear denominators.
  -- `N * (p(n) / q(n)) - N * s(n) = N * r(n) / q(n)` is an integer for
  -- infinitely many `n`, while its absolute value tends to `0`. Thus for
  -- large `n`, `N * r(n) / q(n) = 0`, hence `r(n) = 0` for infinitely many
  -- `n`. Since `r` is a polynomial, `r = 0`.
  sorry

end Imc2006P4
