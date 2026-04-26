/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2014, Problem 10

For every positive integer `n`, let `Dₙ` be the number of permutations
`(x₁, …, xₙ)` of `(1, …, n)` with `x_j ≠ j` for all `j`.
For `1 ≤ k ≤ n / 2`, let `Δ(n, k)` be the number of such derangements
additionally satisfying `x_i = k + i` for every `1 ≤ i ≤ k`.
Prove that

  `Δ(n, k) = ∑_{i = 0}^{k-1} (k-1 choose i) * D_{(n+1)-(k+i)} / (n - (k+i))`.

The equation is interpreted over the rationals (the divisions on the
right-hand side are exact since `(m - 1) ∣ D m` for all `m ≥ 1`).
-/

namespace Imc2014P10

open Equiv Function BigOperators Finset

/-- The number `D n` of derangements on `n` elements. -/
noncomputable def D (n : ℕ) : ℕ := numDerangements n

/--
The set of derangements `σ` of `Fin n` such that `σ ⟨i, _⟩ = ⟨k + i, _⟩` for
every `i < k`. (The hypothesis `2 * k ≤ n` ensures the indices are in range.)
-/
noncomputable def deltaSet (n k : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
    (fun σ => (∀ i : Fin n, σ i ≠ i) ∧
              (∀ i : Fin n, (i : ℕ) < k →
                ∃ h : k + (i : ℕ) < n, σ i = ⟨k + (i : ℕ), h⟩))

/-- The function `Δ n k` from the problem. -/
noncomputable def Δ (n k : ℕ) : ℕ := (deltaSet n k).card

snip begin

/-- For `n ≥ 2`, the recursion `D n = (n - 1) * (D (n - 1) + D (n - 2))`. -/
lemma D_recursion (n : ℕ) (hn : 2 ≤ n) :
    D n = (n - 1) * (D (n - 1) + D (n - 2)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  show numDerangements (m + 2) = _
  rw [numDerangements_add_two]
  have h1 : m + 2 - 1 = m + 1 := by omega
  have h2 : m + 2 - 2 = m := by omega
  rw [h1, h2]
  show (m + 1) * (numDerangements m + numDerangements (m + 1)) =
      (m + 1) * (D (m + 1) + D m)
  show (m + 1) * (numDerangements m + numDerangements (m + 1)) =
      (m + 1) * (numDerangements (m + 1) + numDerangements m)
  ring

snip end

problem imc2014_p10 (n k : ℕ) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    (Δ n k : ℚ) =
      ∑ i ∈ Finset.range k,
        (Nat.choose (k - 1) i : ℚ) *
          (D (n + 1 - (k + i)) : ℚ) / ((n - (k + i) : ℕ) : ℚ) := by
  sorry

-- TODO: Full proof of the recursion
--   Δ n k = Δ (n - 1) (k - 1) + Δ (n - 2) (k - 1)
-- followed by induction on `k`.
--
-- Combinatorial proof outline (following the official solution):
-- 1. Base case `k = 1`: by symmetry across the `n - 1` possible values of σ 0,
--    derangements with `σ 0 = 1` number exactly `D n / (n - 1)`.
--    Using `D n = (n - 1)(D (n - 1) + D (n - 2))` this equals
--    `D (n - 1) + D (n - 2)`, matching the formula at `k = 1`.
-- 2. Inductive step: case-split on whether `σ ⟨2k - 1, _⟩ = ⟨k - 1, _⟩`:
--    * If yes, removing positions `0` and `2k - 1` (and identifying
--      values `k - 1` and `2k - 1`) gives a derangement counted by
--      `Δ (n - 2) (k - 1)`.
--    * If no, removing position `0` (and identifying values `k` and `0`)
--      gives a derangement counted by `Δ (n - 1) (k - 1)`.
-- 3. Apply Pascal's rule `C(k-1, i) + C(k-1, i-1) = C(k, i)`.

end Imc2014P10
