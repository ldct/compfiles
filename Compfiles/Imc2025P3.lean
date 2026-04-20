/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2025, Problem 3

Denote by `S` the set of all real symmetric `2025 × 2025` matrices of rank 1
whose entries take values `-1` or `+1`. Let `A, B ∈ S` be matrices chosen
independently uniformly at random. Find the probability that `A` and `B`
commute, i.e. `AB = BA`.

Answer: `1 / 2^2024`.
-/

namespace Imc2025P3

open Matrix

/-- `n = 2025`. -/
abbrev n : ℕ := 2025

/-- The set `S` of real symmetric `n × n` matrices of rank 1
with entries in `{-1, +1}`. -/
def S : Set (Matrix (Fin n) (Fin n) ℝ) :=
  { A | A.IsSymm ∧ A.rank = 1 ∧ ∀ i j, A i j = 1 ∨ A i j = -1 }

/-- The answer: `1 / 2^(n-1) = 1/2^2024`. -/
noncomputable determine answer : ℝ := 1 / 2 ^ (n - 1)

/-- The problem statement: the probability that two independently uniformly random
matrices from `S` commute equals `answer`.

We express the problem as: the ratio of (number of commuting pairs) to
`|S|^2` equals `answer`, assuming `S` is finite (which we encode in the
hypothesis using `Fintype`).
-/
problem imc2025_p3
    [Fintype S] (hSne : Nonempty S) :
    ((Finset.univ.filter (fun p : S × S =>
        (p.1.1 : Matrix (Fin n) (Fin n) ℝ) * p.2.1 = p.2.1 * p.1.1)).card : ℝ) /
      ((Fintype.card S : ℝ) ^ 2) = answer := by
  -- TODO: The proof proceeds as follows.
  -- 1. Characterize S: every A ∈ S has the form ±u uᵀ where u has first
  --    coordinate 1 and remaining coordinates ±1. Thus |S| = 2^n.
  -- 2. For A = ε_A u uᵀ and B = ε_B v vᵀ, compute
  --    AB = ε_A ε_B ⟨u,v⟩ u vᵀ  and  BA = ε_A ε_B ⟨u,v⟩ v uᵀ.
  --    Since n = 2025 is odd, ⟨u,v⟩ is odd, hence nonzero.
  --    So AB = BA iff u vᵀ = v uᵀ iff u = v (columns match).
  -- 3. Therefore AB = BA iff A = ±B, giving exactly 2 choices of B for each A.
  -- 4. Probability = 2 / |S| = 2 / 2^n = 1 / 2^(n-1).
  sorry

end Imc2025P3
