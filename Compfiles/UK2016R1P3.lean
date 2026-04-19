/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2016, Round 1, Problem 3

Suppose that a sequence t₀, t₁, t₂, . . . is defined by a formula
tₙ = An² + Bn + C for all integers n ≥ 0. Here A, B and C are real
constants with A ≠ 0. Determine values of A, B and C which give the
greatest possible number of successive terms of the sequence which are
also successive terms of the Fibonacci sequence. The Fibonacci sequence
is defined by F₀ = 0, F₁ = 1 and Fₘ = F_{m−1} + F_{m−2} for m ≥ 2.
-/

namespace UK2016R1P3

def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

/-- The set of triples (A, B, C) with A ≠ 0 such that there exists some
starting index k so that t_n = A n² + B n + C matches F_{k+n} for
(at least) some number L of consecutive values of n. -/
def matchesFib (A B C : ℝ) (k L : ℕ) : Prop :=
  ∀ n, n < L → A * n^2 + B * n + C = (fib (k + n) : ℝ)

/-- The greatest number of successive Fibonacci terms attainable by a
quadratic formula A n² + B n + C with A ≠ 0. -/
determine max_consecutive : ℕ := 4

problem uk2016_r1_p3 :
    (∃ A B C : ℝ, A ≠ 0 ∧ ∃ k : ℕ, matchesFib A B C k max_consecutive) ∧
    (∀ L : ℕ, max_consecutive < L →
      ¬ ∃ A B C : ℝ, A ≠ 0 ∧ ∃ k : ℕ, matchesFib A B C k L) := by
  sorry

end UK2016R1P3
