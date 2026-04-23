/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2023, Problem 5

Fix positive integers `n` and `k` with `2 ≤ k ≤ n` and a set `M` of
`n` fruits. A *permutation* is a sequence `x = (x₁, …, xₙ)` with
`{x₁, …, xₙ} = M`. Ivan prefers a nonempty set `P` of permutations such
that for every `x ∈ P` there exist indices `i₁ < i₂ < ⋯ < i_k` with the
property that for every `1 ≤ j < k`, swapping `x_{iⱼ}` and `x_{i_{j+1}}`
yields another preferred permutation.

Prove that `|P| ≥ k!`.
-/

namespace Imc2023P5

/-- Swap the values at positions `i` and `j` in a permutation `x : Fin n → α`. -/
def swapAt {α : Type*} {n : ℕ} (x : Fin n → α) (i j : Fin n) : Fin n → α :=
  fun t => if t = i then x j else if t = j then x i else x t

problem imc2023_p5 {α : Type*} (n k : ℕ) (h2k : 2 ≤ k) (hkn : k ≤ n)
    (P : Set (Fin n → α))
    (hne : P.Nonempty)
    (hpref : ∀ x ∈ P, ∃ idx : Fin k → Fin n,
      StrictMono idx ∧
        ∀ j : Fin (k - 1),
          swapAt x (idx ⟨j.val, by omega⟩)
              (idx ⟨j.val + 1, by omega⟩) ∈ P) :
    (Nat.factorial k : ℕ∞) ≤ P.encard := by
  -- TODO: Following the official solution.
  -- Induction on k. For k = 2, there are at least 2 permutations (x and
  -- the single swap). For the step, one shows there is an orbit of the
  -- preferred permutations under the allowed swaps forming an
  -- S_k-torsor, hence of size ≥ k!.
  sorry

end Imc2023P5
