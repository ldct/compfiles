/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2020, Problem 1

Let `n` be a positive integer. Compute the number of words `w`
(finite sequences of letters) satisfying:
  (1) `w` consists of `n` letters from `{a, b, c, d}`;
  (2) `w` contains an even number of letters `a`;
  (3) `w` contains an even number of letters `b`.

Answer: `4^(n-1) + 2^(n-1)`.

We encode the four letters `{a, b, c, d}` as `Fin 4` with `0 ↦ a`,
`1 ↦ b`, `2 ↦ c`, `3 ↦ d`.
-/

namespace Imc2020P1

open Finset

/-- The set of words of length `n` over `{a, b, c, d}` with even counts
of `a` and `b`. Here `0` represents `a` and `1` represents `b`. -/
noncomputable def goodWords (n : ℕ) : Finset (Fin n → Fin 4) :=
  (Finset.univ : Finset (Fin n → Fin 4)).filter fun w =>
    Even ((Finset.univ : Finset (Fin n)).filter (fun i => w i = 0)).card ∧
    Even ((Finset.univ : Finset (Fin n)).filter (fun i => w i = 1)).card

/-- The answer: `4^(n-1) + 2^(n-1)`. -/
determine answer (n : ℕ) : ℕ := 4 ^ (n - 1) + 2 ^ (n - 1)

/-- Compute the number of words of length `n` over `{a, b, c, d}` with
even counts of `a` and `b`.

The official proof uses generating functions: the count is
`((4^n) + (-1+1+1+1)^n + (-1+1+1+1)^n + (1-1+1+1)^n) / 4`
`= (4^n + 2^n + 2^n + 0) / 4 = 4^{n-1} + 2^{n-1}`.

TODO: This is a counting argument that would be non-trivial in Lean.
We leave it as a `sorry`.
-/
problem imc2020_p1 (n : ℕ) (hn : 0 < n) :
    (goodWords n).card = answer n := by
  sorry

end Imc2020P1
