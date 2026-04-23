/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Competition 2024, Problem 10

We say that a square-free positive integer `n` is *almost prime* if

  `n ∣ x^{d₁} + x^{d₂} + ⋯ + x^{dₖ} - k·x`

for all integers `x`, where `1 = d₁ < d₂ < ⋯ < dₖ = n` are all positive
divisors of `n`.

Suppose `r = 2^{2^m} + 1` is a Fermat prime, `p` is a prime divisor of
an almost prime `n`, and `p ≡ 1 (mod r)`. Show that `dᵢ ≡ 1 (mod r)`
for all `i`.
-/

namespace Imc2024P10

/-- The ordered list of positive divisors of `n`. -/
noncomputable def divisorsList (n : ℕ) : List ℕ :=
  n.divisors.sort (· ≤ ·)

/-- `n` is almost prime if it is square-free and the divisor-power
condition holds for all integer `x`. -/
def IsAlmostPrime (n : ℕ) : Prop :=
  0 < n ∧ Squarefree n ∧
    ∀ x : ℤ, (n : ℤ) ∣
      ((divisorsList n).map (fun d => x ^ d)).sum - (divisorsList n).length * x

problem imc2024_p10 (m : ℕ) (r : ℕ) (hr_def : r = 2 ^ (2 ^ m) + 1)
    (hr_prime : Nat.Prime r) (n : ℕ) (hn : IsAlmostPrime n)
    (p : ℕ) (hp : Nat.Prime p) (hpn : p ∣ n) (hpr : p % r = 1) :
    ∀ d ∈ n.divisors, d % r = 1 := by
  -- TODO: Following the official solution.
  -- Work in F_p. Since p ≡ 1 (mod r), F_p contains an element ω of
  -- order r. Apply the divisor condition with x = generator and analyze
  -- ω^d via multiplicative characters and cyclotomic identities. A
  -- multi-lemma argument using Kummer / Gauss sums mod r leads to
  -- d ≡ 1 (mod r) for every divisor d.
  sorry

end Imc2024P10
