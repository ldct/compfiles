/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory, .Combinatorics] }

/-!
# International Mathematical Competition 2016, Problem 5

Let `S_n` denote the set of permutations of the sequence `(1, 2, …, n)`.
For every permutation `π = (π_1, …, π_n) ∈ S_n`, let `inv(π)` be the
number of pairs `1 ≤ i < j ≤ n` with `π_i > π_j`. Denote by `f(n)` the
number of permutations `π ∈ S_n` for which `inv(π)` is divisible by
`n + 1`.

Prove that there exist infinitely many primes `p` such that
`f(p-1) > (p-1)!/p`, and infinitely many primes `p` such that
`f(p-1) < (p-1)!/p`.

The proof uses the generating function
`G_n(x) = ∑_{π ∈ S_n} x^{inv(π)} = ∏_{j=1}^n (1 + x + … + x^{j-1})`
and a roots-of-unity filter with `ε = e^{2πi/(n+1)}`. For `n = p-1`
prime, the values `G_{p-1}(ε^k)` for `1 ≤ k ≤ p-1` simplify to
`p / (1 - e^{2πik/p})^{p-1}`. The sign of `f(p-1) - (p-1)!/p` is then
controlled by an exponentially-dominant cosine factor whose sign is
`+` when `p ≡ 3 (mod 4)` and `-` when `p ≡ 1 (mod 4)`. Dirichlet's
theorem on primes in arithmetic progressions provides infinitely many
of each.
-/

namespace Imc2016P5

open Finset

/-- Number of inversions of a permutation `π ∈ S_n`: pairs `i < j` with
`π i > π j`. We use `Fin n → Fin n` (bijective) to model `S_n`; here
`π : Equiv.Perm (Fin n)`. -/
def inv (n : ℕ) (π : Equiv.Perm (Fin n)) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter
    (fun p => p.1 < p.2 ∧ π p.2 < π p.1)).card

/-- `f n` is the number of permutations `π` of `Fin n` whose inversion
count is divisible by `n + 1`. -/
def f (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
    (fun π => (n + 1) ∣ inv n π)).card

problem imc2016_p5 :
    (∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ p.Prime ∧ (p - 1).factorial < p * f (p - 1)) ∧
    (∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ p.Prime ∧ p * f (p - 1) < (p - 1).factorial) := by
  -- TODO: Generating function / roots-of-unity filter argument plus
  -- Dirichlet's theorem on primes ≡ 1, 3 (mod 4).
  sorry


end Imc2016P5
