/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Competition 2025, Problem 7

Let `ℤ>0` be the set of positive integers. Find all nonempty subsets
`M ⊆ ℤ>0` satisfying both of the following properties:

  (a) if `x ∈ M`, then `2x ∈ M`,
  (b) if `x, y ∈ M` and `x + y` is even, then `(x + y)/2 ∈ M`.

Answer: `M` is of the form `{(m + k) * d | k ∈ ℕ}` for some positive integer
`m` and positive *odd* integer `d`.
-/

namespace Imc2025P7

/-- The set of "nice" subsets — those of the form `{(m + k) * d | k ∈ ℕ}`
for some positive integer `m` and positive odd integer `d`. -/
determine answer : Set (Set ℕ) :=
  { M | ∃ m d : ℕ, 0 < m ∧ 0 < d ∧ Odd d ∧
    M = { x | ∃ k : ℕ, x = (m + k) * d } }

problem imc2025_p7 (M : Set ℕ) (hMsub : M ⊆ Set.Ioi 0) (hMne : M.Nonempty) :
    M ∈ answer ↔
    ((∀ x ∈ M, 2 * x ∈ M) ∧
     (∀ x ∈ M, ∀ y ∈ M, Even (x + y) → (x + y) / 2 ∈ M)) := by
  -- TODO: Forward direction is computation.
  -- Reverse direction (following the official solution):
  -- (1) M is closed under addition: x + y = (2x + 2y)/2 (since 2x, 2y ∈ M
  --     and their sum is even).
  -- (2) M contains odd numbers: from x ∈ M, 3x/2 ∈ M (via x and 2x), iterate.
  -- (3) Let d = gcd of M. Then d is odd. There exist a, a' ∈ M with
  --     a' - a = d. Taking the least such with c := min M, one shows that
  --     a - d ∈ M. Symmetrically, a + d ∈ M. Hence M is an arithmetic
  --     progression c + k*d, k ∈ ℕ.
  sorry

end Imc2025P7
