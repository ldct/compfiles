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

snip begin

/-!
## Roadmap of the official solution

Three lemmas suffice. The "main argument" then derives the result from them.

* **Lemma 1.** If `n` is almost prime then `gcd(n, φ(n)) = 1`. The key step:
  for primes `p, q ∣ n` with `p ≡ 1 (mod q)`, look at the polynomial
  `F_n(x) = Σ x^{d_i} - k x` over `F_p`. Since `F_n` vanishes on `F_p`,
  bin divisors `d_i` by their residue mod `p-1`; the coefficients `h_i`
  (count of divisors with residue `i`) satisfy `p ∣ h_i` for `i ≠ 1`.
  Counting divisors mod `q` produces `2^{ω(n)-1} ≡ 0 (mod p)`, contradiction.

* **Lemma 2.** Let `q` prime, `h` coprime to `q-1` with order `ℓ` mod `q-1`.
  Then there exists `a ∈ F_q` with `a^{h^ℓ} = a` and the alternating sum
  `f(a) = a - a^h + a^{h²} - … + (-1)^{ℓ-1} a^{h^{ℓ-1}}` nonzero.

* **Lemma 3.** If `n` almost prime and `p, q ∣ n` primes, then
  `ord_{q-1}(p)` is odd. Proof: if `ℓ` even, take `a` from Lemma 2 with
  `q ↔ p`. Define `aᵢ₊₁ = -aᵢ^p`; since `ℓ` even, `a_ℓ = a₀`. Compute
  `Σᵢ Σ_{d ∣ n} aᵢ^d = 0` using the divisor-pairing through `p`, but
  also equals `k · f(a) ≠ 0`, contradiction.

* **Main argument.** With `r` Fermat prime and `p ∣ n` with `p ≡ 1 (mod r)`,
  for any prime `q ∣ n`: by Lemma 3, `ord_{p-1}(q) = ℓ` is odd.
  Since `r ∣ p - 1`, we get `q^ℓ ≡ 1 (mod r)`, hence `q ≡ 1 (mod r)`
  (using `gcd(ℓ, r-1) = 1` because `r-1 = 2^{2^m}` is a power of 2 and
  `ℓ` is odd).  Multiplicativity then yields `d ≡ 1 (mod r)` for every
  divisor `d` of `n`.
-/

/-- Lemma 1 (sketch placeholder): `gcd(n, φ(n)) = 1` for almost-prime `n`.
This implies in particular: if `p, q` are distinct primes dividing an
almost prime `n`, then `q ∤ p - 1`. -/
lemma lemma1_no_prime_divides_predecessor
    {n p q : ℕ} (_hn : IsAlmostPrime n)
    (_hp : Nat.Prime p) (_hq : Nat.Prime q) (_hpn : p ∣ n) (_hqn : q ∣ n)
    (_hpq : p ≠ q) : ¬ q ∣ (p - 1) := by
  -- TODO: F_p polynomial vanishing argument; bin divisors mod p-1
  -- and mod q; derive 2^{ω(n)-1} ≡ 0 (mod p).
  sorry

/-- Lemma 3 (sketch placeholder): for primes `p, q ∣ n` with `n` almost
prime, the multiplicative order of `p` modulo `q - 1` is odd. -/
lemma lemma3_order_is_odd
    {n p q : ℕ} (_hn : IsAlmostPrime n)
    (_hp : Nat.Prime p) (_hq : Nat.Prime q)
    (_hpn : p ∣ n) (_hqn : q ∣ n) (_hpq : p ≠ q) :
    Odd (Nat.find (show ∃ ℓ, 0 < ℓ ∧ p ^ ℓ % (q - 1) = 1 % (q - 1) from
      sorry)) := by
  -- TODO: Use Lemma 2 to produce `a ∈ F_q` with `f(a) ≠ 0`, then derive
  -- contradiction from divisor-pairing identity Σᵢ Σ_{d∣n} aᵢ^d = k f(a).
  sorry

snip end

problem imc2024_p10 (m : ℕ) (r : ℕ) (hr_def : r = 2 ^ (2 ^ m) + 1)
    (hr_prime : Nat.Prime r) (n : ℕ) (hn : IsAlmostPrime n)
    (p : ℕ) (hp : Nat.Prime p) (hpn : p ∣ n) (hpr : p % r = 1) :
    ∀ d ∈ n.divisors, d % r = 1 := by
  -- TODO: Following the official solution.
  --
  -- Strategy:
  -- (1) Reduce to: every prime `q ∣ n` satisfies `q ≡ 1 (mod r)`,
  --     using that the residues mod `r` are multiplicatively closed
  --     and `n` is squarefree.
  -- (2) For prime `q ∣ n`, let `ℓ = ord_{p-1}(q)`. By Lemma 3 (with
  --     roles of p,q swapped) `ℓ` is odd.
  -- (3) Since `r ∣ p - 1` (from `p ≡ 1 mod r`), we get
  --     `q^ℓ ≡ 1 (mod r)`. The order of `q` mod `r` divides
  --     `gcd(ℓ, r - 1)`. But `r - 1 = 2^{2^m}` is a power of 2 and
  --     `ℓ` is odd, so `gcd(ℓ, r - 1) = 1`, giving `q ≡ 1 (mod r)`.
  -- (4) Conclude for every divisor `d` of `n` by multiplicativity.
  sorry

end Imc2024P10
