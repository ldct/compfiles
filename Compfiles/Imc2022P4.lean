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
  --
  -- Step 1. For each k ≥ 1, define a digraph G_k on strictly increasing
  --   k-tuples from [n], with an edge (a₁,…,a_k) → (a₂,…,a_{k+1}) for
  --   each strictly increasing (k+1)-tuple (a₁,…,a_{k+1}). The problem's
  --   constraint says exactly that m n = χ(G_3).
  --
  -- Step 2. Call an edge set admissible if it contains no directed path
  --   of length 2; let b(G) be the minimum number of admissible sets
  --   covering E(G). Lemma 1: an independent set in G_k is exactly an
  --   admissible edge set of G_{k-1}, so χ(G_k) = b(G_{k-1}).
  --
  -- Step 3. Lemma 2: for any digraph G,
  --     log₂ χ(G) ≤ b(G) ≤ 2 ⌈log₂ χ(G)⌉.
  --   Lower bound: from an admissible cover E₁,…,E_b, label v ↦
  --     {i : v has an outgoing edge in E_i} ⊆ [b]; endpoints of any
  --     edge get distinct labels, so χ(G) ≤ 2^b.
  --   Upper bound: from a proper k-colouring τ with r = ⌈log₂ k⌉, for
  --     each bit i form E_{i,+} = {vu : bit_i τv = 0, bit_i τu = 1} and
  --     E_{i,-} symmetrically. These 2r sets are admissible and cover E.
  --
  -- Step 4. χ(G_1) = n (vertices are points of [n], complete forward
  --   tournament), so b(G_1) = ⌈log₂ n⌉. Then χ(G_2) = b(G_1) =
  --   ⌈log₂ n⌉ and m = χ(G_3) = b(G_2) ∈ [⌈log₂ ⌈log₂ n⌉⌉,
  --   2⌈log₂ ⌈log₂ n⌉⌉].
  --
  -- Step 5. Translate ⌈log₂⌉ ↔ Real.log via Real.log x / Real.log 2,
  --   absorb constants into (1/100, 100) for n ≥ N.
  sorry

end Imc2022P4
