/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2014, Problem 2

Consider the sequence
`(a_n)_{n=1}^∞ = (1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 1, 2, 3, 4, 5, 1, ...)`.
Find all pairs `(α, β)` of positive real numbers such that
`lim_{n → ∞} (∑_{k=1}^n a_k) / n^α = β`.

Answer: `(α, β) = (3/2, √2 / 3)`.
-/

namespace Imc2014P2

open Filter Topology

/-- The "block index" of `n`: the smallest `m` with `n ≤ m*(m+1)/2`. The value
`a n` lies in block `m`, where the `m`-th block (`m ≥ 1`) consists of the values
`1, 2, …, m` placed at indices `m(m-1)/2 + 1, …, m(m+1)/2`. -/
def blockIdx (n : ℕ) : ℕ := Nat.find (p := fun m => n ≤ m * (m + 1) / 2)
  ⟨n, by
    rcases n.eq_zero_or_pos with h | h
    · simp [h]
    · have h2 : 2 * n ≤ n * (n + 1) := by nlinarith
      omega⟩

/-- The sequence `a_n`, defined for `n ≥ 1`. We extend `a 0 = 0`. -/
def a (n : ℕ) : ℕ := n - (blockIdx n) * (blockIdx n - 1) / 2

/-- Partial sum `S n = ∑_{k=1}^n a k`. -/
def S (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, a (k + 1)

/-- The set of valid `(α, β)` pairs. -/
noncomputable determine answer : Set (ℝ × ℝ) := {(3 / 2, Real.sqrt 2 / 3)}

problem imc2014_p2 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    Tendsto (fun n : ℕ => (S n : ℝ) / (n : ℝ) ^ α) atTop (𝓝 β) ↔
      (α, β) ∈ answer := by
  -- TODO: full proof. The argument:
  --   * Let T m = m(m+1)/2. Then a (T(m-1) + j) = j for 1 ≤ j ≤ m,
  --     and S (T m) = m(m+1)(m+2)/6.
  --   * S(T m) / (T m)^α ~ (m^3 / 6) / ((m^2/2)^α) = 2^{α-1}/3 · m^{3-2α},
  --     finite positive iff α = 3/2; then β = √2 / 3.
  --   * For arbitrary n with T(m-1) < n ≤ T m, sandwich between
  --     S(T(m-1))/(T m)^{3/2} and S(T m)/(T(m-1))^{3/2}; both → √2/3.
  sorry

end Imc2014P2
