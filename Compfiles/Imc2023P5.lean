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
  -- TODO: The statement as written is in fact too weak: it does not require
  -- the elements of `P` to be bijections onto a fixed set `M` of size `n`.
  -- For example, taking `x` to be a constant function, every `swapAt x i j`
  -- equals `x`, so `P = {x}` satisfies all hypotheses with `|P| = 1 < k!`.
  -- A correct formalization would impose `Function.Injective x` (equivalently
  -- `x` ranges over a fixed `n`-element set `M`) for every `x ∈ P`.
  --
  -- Assuming bijectivity, the official solution proceeds as follows. Let
  -- `S` be all `n!` bijective permutations. For each `x ∈ P`, set
  --   A(x) = { z ∈ S : ∀ y ∈ P, ∑ₘ x⁻¹(m) z⁻¹(m) ≥ ∑ₘ y⁻¹(m) z⁻¹(m) }.
  -- Every `z ∈ S` lies in some `A(x)` (pick a maximizer of the linear
  -- functional `y ↦ ∑ₘ y⁻¹(m) z⁻¹(m)` over the finite set `P`).
  -- For fixed `x ∈ P` and `z ∈ A(x)`, with witnesses `i₁ < ⋯ < i_k` and
  -- `mⱼ = x_{iⱼ}`, the swap-stable inequalities (one per adjacent pair)
  -- force `z⁻¹(m₁) < z⁻¹(m₂) < ⋯ < z⁻¹(m_k)`. The number of `z ∈ S`
  -- placing `m₁,…,m_k` in this prescribed order is exactly `n!/k!`, so
  -- `|A(x)| ≤ n!/k!`. Summing, `|P| · n!/k! ≥ |S| = n!`, hence `|P| ≥ k!`.
  sorry

end Imc2023P5
