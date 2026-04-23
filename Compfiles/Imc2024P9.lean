/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2024, Problem 9

A matrix `A = (aᵢⱼ)` of size `m × n` is called *nice* if:

(i)   the set of all entries of `A` equals `{1, 2, …, 2t}` for some
      positive integer `t`;
(ii)  `aᵢⱼ ≤ aᵢ,ⱼ₊₁` and `aᵢⱼ ≤ aᵢ₊₁,ⱼ`;
(iii) if `aᵢⱼ = aₖₗ` then `i = k` or `j = ℓ`;
(iv)  for each `s = 1, …, 2t - 1`, there exist `i ≠ k` and `j ≠ ℓ`
      with `aᵢⱼ = s` and `aₖₗ = s + 1`.

Prove that the number of nice `m × n` matrices is even.
-/

namespace Imc2024P9

/-- `A : Fin m → Fin n → ℕ` is a nice matrix. -/
def IsNice {m n : ℕ} (A : Fin m → Fin n → ℕ) : Prop :=
  ∃ t : ℕ, 0 < t ∧
    -- (i) entries form {1, …, 2t}
    (∀ v, v ∈ Finset.Icc 1 (2 * t) ↔ ∃ i j, A i j = v) ∧
    -- (ii) row/column monotonicity
    (∀ i, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
        A i j ≤ A i ⟨j.val + 1, hj⟩) ∧
    (∀ i : Fin m, ∀ hi : i.val + 1 < m, ∀ j,
        A i j ≤ A ⟨i.val + 1, hi⟩ j) ∧
    -- (iii) each value in at most one row and one column
    (∀ i j k l, A i j = A k l → i = k ∨ j = l) ∧
    -- (iv) consecutive values in distinct row and distinct column
    (∀ s ∈ Finset.Icc 1 (2 * t - 1),
        ∃ i j k l, i ≠ k ∧ j ≠ l ∧ A i j = s ∧ A k l = s + 1)

/-- The (finite) set of nice `m × n` matrices, represented as functions
`Fin m → Fin n → ℕ` bounded by some large value. We use `Fintype` over
matrices with entries bounded by `2 * m * n` (which suffices since any
nice matrix uses entries `≤ 2t ≤ 2 · m · n`). -/
noncomputable def niceCount (m n : ℕ) : ℕ :=
  Nat.card {A : Fin m → Fin n → ℕ // IsNice A}

problem imc2024_p9 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Even (niceCount m n) := by
  -- TODO: Following the official solution (Young-tableau friendship-graph).
  -- Build a graph on nice matrices: A ~ B iff they differ by a single
  -- "local swap" that preserves niceness. Show the graph is 1-regular
  -- (each nice matrix has exactly one partner) via a bespoke argument,
  -- hence the count is even. The bespoke swap relies on identifying
  -- the "pivot" position s = 2t - 1 and swapping it with s - 1.
  sorry

end Imc2024P9
