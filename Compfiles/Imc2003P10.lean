/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2003, Problem 10
(IMC 2003, Day 2, Problem 4)

Find all positive integers `n` for which there exists a family `F` of
3-element subsets of `S = {1, …, n}` such that
  (i) every 2-element subset of `S` is contained in exactly one member of `F`;
  (ii) whenever `{a,b,x}, {a,c,y}, {b,c,z} ∈ F` with `a, b, c` pairwise
       distinct, then `{x, y, z} ∈ F`.

The answer is `n = 2^m - 1` for some natural number `m`.
-/

namespace Imc2003P10

open Finset

/-- The combinatorial property of a family `F` of 3-element subsets of
`{1,…,n}`. -/
def IsGoodFamily (n : ℕ) (F : Set (Finset ℕ)) : Prop :=
  (∀ A ∈ F, A ⊆ Icc 1 n ∧ A.card = 3) ∧
  (∀ a b, a ∈ Icc 1 n → b ∈ Icc 1 n → a ≠ b →
      ∃! A : Finset ℕ, A ∈ F ∧ a ∈ A ∧ b ∈ A) ∧
  (∀ a b c x y z, ({a, b, x} : Finset ℕ) ∈ F → ({a, c, y} : Finset ℕ) ∈ F →
      ({b, c, z} : Finset ℕ) ∈ F →
      a ≠ b → a ≠ c → b ≠ c → ({x, y, z} : Finset ℕ) ∈ F)

snip begin

/-
Sketch.

For a good family, define `a * b = c` to be the unique third element of the
triple containing `a, b` (for `a ≠ b`). Properties of (i) and (ii) imply that
on `S ∪ {0}` (a new symbol) with `a * a = 0`, `0 * a = a * 0 = a` and `*` as
above otherwise, we obtain an abelian group of exponent 2. Hence
`|S ∪ {0}| = 2^m`, so `n = 2^m - 1`.

For the converse, identify `S` with `(Fin m → ZMod 2) \ {0}` and let `F` be
the set of triples `{a, b, c}` with `a + b + c = 0`. Both axioms are easily
verified.
-/

snip end

determine SolutionSet : Set ℕ := { n | ∃ m : ℕ, n = 2 ^ m - 1 }

problem imc2003_p10 :
    SolutionSet = { n | ∃ F : Set (Finset ℕ), IsGoodFamily n F } := by
  -- The full proof is substantial. The forward direction (construction)
  -- exhibits the family obtained from `(ZMod 2)^m`. The reverse direction
  -- builds an abelian group of exponent 2 on `S ∪ {0}`.
  sorry

end Imc2003P10
