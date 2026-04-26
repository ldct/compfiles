/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2025, Problem 5

For a positive integer `n`, let `[n] = {1, 2, …, n}`. Denote by `Sₙ` the set
of all bijections from `[n]` to `[n]`, and let `Tₙ` be the set of all maps
from `[n]` to `[n]`. Define the *order* `ord(τ)` of a map `τ ∈ Tₙ` as the
number of distinct maps in the set `{τ, τ∘τ, τ∘τ∘τ, …}` where `∘` denotes
composition. Finally, let

  `f(n) = max_{τ ∈ Sₙ} ord(τ)`  and  `g(n) = max_{τ ∈ Tₙ} ord(τ)`.

Prove that `g(n) < f(n) + n^0.501` for sufficiently large `n`.
-/

namespace Imc2025P5

/-- The order of a map `τ : [n] → [n]`: the number of distinct iterates
`{τ, τ², τ³, …}`. -/
noncomputable def ord {n : ℕ} (τ : Fin n → Fin n) : ℕ :=
  Nat.card {σ : Fin n → Fin n // ∃ k : ℕ, 0 < k ∧ σ = τ^[k]}

/-- `f(n) = max over permutations τ of [n] of ord(τ)`. -/
noncomputable def f (n : ℕ) : ℕ :=
  ⨆ τ : Equiv.Perm (Fin n), ord (τ : Fin n → Fin n)

/-- `g(n) = max over all maps τ: [n] → [n] of ord(τ)`. -/
noncomputable def g (n : ℕ) : ℕ :=
  ⨆ τ : Fin n → Fin n, ord τ

snip begin

/-- Any permutation `τ` has `ord τ ≤ f n`. The index type `Equiv.Perm (Fin n)` is
finite, so the range is bounded above. -/
lemma ord_le_f {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    ord (τ : Fin n → Fin n) ≤ f n := by
  classical
  refine le_ciSup (f := fun τ : Equiv.Perm (Fin n) => ord (τ : Fin n → Fin n)) ?_ τ
  exact Set.Finite.bddAbove (Set.toFinite _)

/-- Any map `τ : Fin n → Fin n` has `ord τ ≤ g n`. -/
lemma ord_le_g {n : ℕ} (τ : Fin n → Fin n) : ord τ ≤ g n := by
  classical
  refine le_ciSup (f := fun τ : Fin n → Fin n => ord τ) ?_ τ
  exact Set.Finite.bddAbove (Set.toFinite _)

snip end

problem imc2025_p5 :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (g n : ℝ) < f n + (n : ℝ) ^ (0.501 : ℝ) := by
  -- TODO: Full proof follows the official solution.
  -- For any τ : [n] → [n], let C(τ) = {x : ∃ k > 0, τ^k(x) = x} (the eventually
  -- periodic part). Then τ restricted to C(τ) is a permutation τ_c with some
  -- order N ≤ g(n). Let R = max_{x ∉ C(τ)} h(x), where h(x) is the minimal k
  -- with τ^k(x) ∈ C(τ). Then ord(τ) ≤ N + R.
  -- If R < n^0.501, done. Otherwise R ≥ n^0.501, so |C(τ)| ≤ n - n^0.501.
  -- By a PNT-style estimate (sum of primes ≤ x is ~ x²/(2 log x), much
  -- bigger than n for x = n^0.501), there exists a prime p < n^0.501 not
  -- dividing any cycle length of τ_c. Then we can build a permutation on
  -- [n] with order p · N, so p · N ≤ f(n), giving N ≤ f(n)/2.
  -- Hence ord(τ) ≤ f(n)/2 + n < f(n) for large n (using f(n) ≥ 2n + 2 for n ≥ 5,
  -- e.g., a (2,3,5,7,...) cycle decomposition).
  sorry

end Imc2025P5
