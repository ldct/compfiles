/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2022, Problem 4

Let `n > 3` be an integer. Let `Ω` be the set of all triples of distinct
elements of `{1, 2, …, n}`. Let `m` denote the minimal number of
colours which suffice to colour `Ω` so that whenever
`1 ≤ a < b < c < d ≤ n`, the triples `{a,b,c}` and `{b,c,d}` have
different colours. Prove that

  `(1/100) log log n ≤ m ≤ 100 log log n`.
-/

namespace Imc2022P4

/-- The set of unordered triples of distinct elements of `{1, …, n}`. -/
def Omega (n : ℕ) : Finset (Finset ℕ) :=
  ((Finset.Icc 1 n).powerset).filter (fun s => s.card = 3)

/-- A colouring is valid if whenever `a < b < c < d ∈ [1, n]`, the triples
`{a, b, c}` and `{b, c, d}` receive different colours. -/
def ValidColouring (n : ℕ) (k : ℕ) (c : Finset ℕ → Fin k) : Prop :=
  ∀ a b cc d : ℕ, 1 ≤ a → a < b → b < cc → cc < d → d ≤ n →
    c {a, b, cc} ≠ c {b, cc, d}

/-- The chromatic number `m n`: the least `k` such that a valid colouring
with `k` colours exists. -/
noncomputable def m (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ c : Finset ℕ → Fin k, ValidColouring n k c}

problem imc2022_p4 :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((1 : ℝ) / 100) * Real.log (Real.log n) ≤ m n ∧
      (m n : ℝ) ≤ 100 * Real.log (Real.log n) := by
  -- TODO: Following the official solution.
  -- Setup directed graphs G_k on k-subsets with an edge from
  -- (a_1,…,a_k) to (a_2,…,a_{k+1}). An admissible edge set has no
  -- directed path of length 2; let b(G) be the min number of admissible
  -- sets covering E. Then chi(G_k) = b(G_{k-1}) and
  --   log₂ chi(G) ≤ b(G) ≤ 2 ⌈log₂ chi(G)⌉.
  -- Applying twice starting from chi(G_1) = n gives
  --   log₂ ⌈log₂ n⌉ ≤ m ≤ 2 ⌈log₂ ⌈log₂ n⌉⌉.
  sorry

end Imc2022P4
