/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .NumberTheory] }

/-!
# International Mathematical Competition 2018, Problem 5

Let `p < q` be primes. In a convex polygon `P₁ P₂ ⋯ P_{pq}` all interior
angles are equal and all side lengths are distinct positive integers.
Prove that
`P₁P₂ + P₂P₃ + ⋯ + P_k P_{k+1} ≥ (k³ + k) / 2`
for `1 ≤ k ≤ p`.

## Proof outline

Place the polygon in `ℂ` counterclockwise so that `P₂ - P₁` is a positive
real. Let `aᵢ = |P_{i+1} - P_i|` (so `a : Fin (p*q) → ℕ` is the sequence of
side lengths). Setting `ω = exp(2πi / (pq))`, the closure relation
`P_{pq+1} = P₁` becomes
  `f(ω) = 0`,  where  `f(x) = ∑_{i=0}^{pq-1} aᵢ xⁱ`.

The minimal polynomial of `ω` over `ℚ` is `Φ_{pq}(x)`, and Bezout in
`ℚ[x]` gives `Φ_{pq}(x) = gcd(Φ_q(x^p), Φ_p(x^q))`. Hence
  `f(x) = Φ_q(x^p) · u(x) + Φ_p(x^q) · v(x)`
with `deg u ≤ p - 1` and `deg v ≤ q - 1`. By the Chinese Remainder Theorem,
the natural map `(i, j) ↦ n` with `n ≡ i (mod p)` and `n ≡ j (mod q)` is a
bijection `Fin p × Fin q → Fin (pq)`. Writing `u(x) = ∑ uᵢ xⁱ` and
`v(x) = ∑ vⱼ xʲ`, one gets `a_{(i,j)} = uᵢ + vⱼ`.

Then for `k ≤ p`,
```
∑_{i<k} a_{(i,i)} = ∑_{i<k} (uᵢ + vᵢ)
                  = (1/k) ∑_{i,j<k} (uᵢ + vⱼ)
                  = (1/k) ∑_{i,j<k} a_{(i,j)}
                  ≥ (1/k) (1 + 2 + ⋯ + k²)
                  = (k³ + k) / 2,
```
using that the `a_{(i,j)}` are distinct positive integers (so the sum of
any `k²` of them is at least `1 + 2 + ⋯ + k²`).
-/

namespace Imc2018P5

open Complex Real

/-- An equiangular convex polygon with `n = p * q` integer sides.

We encode it directly via the closure relation in `ℂ` and the existence of
some starting point/orientation. The vertices are
`P_i = P₁ + ∑_{j<i-1} a_j · ω^j` with `ω = exp(2πi/(pq))`.

`a : Fin (p * q) → ℕ` gives the side lengths (so `aᵢ ≥ 1`). The polygon is
*equiangular* iff turning at each vertex by `2π/(pq)` is consistent, which
amounts to the closure condition `∑ aᵢ · ω^i = 0`. Distinctness of side
lengths is `Function.Injective a`. -/
structure EquiangularPolygon (p q : ℕ) where
  /-- Side lengths, indexed `0, …, pq - 1`. -/
  a : Fin (p * q) → ℕ
  /-- All side lengths are positive. -/
  pos : ∀ i, 1 ≤ a i
  /-- All side lengths are distinct. -/
  distinct : Function.Injective a
  /-- Closure: the polygon closes up.  In `ℂ`, with `ω = exp(2πi/(pq))`,
  `∑ aᵢ ω^i = 0`. -/
  closure : ∑ i : Fin (p * q),
              (a i : ℂ) * Complex.exp (2 * Real.pi * I * i.val / (p * q)) = 0

/-- For `1 ≤ k ≤ p` the partial sum `a₀ + a₁ + ⋯ + a_{k-1}` is at least
`(k³ + k) / 2`. -/
problem imc2018_p5 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (P : EquiangularPolygon p q) (k : ℕ) (hk1 : 1 ≤ k) (hkp : k ≤ p) :
    (k ^ 3 + k) / 2 ≤
      ∑ i : Fin k,
        P.a ⟨i.val, by
          have hk_le : k ≤ p * q := le_trans hkp (Nat.le_mul_of_pos_right p hq.pos)
          have hi : i.val < k := i.isLt
          omega⟩ := by
  -- TODO: full proof requires:
  --   (1) The closure relation `∑ aᵢ ω^i = 0` with `ω = exp(2πi/(pq))`
  --       and the fact that `Φ_{pq}` is the minimal polynomial of `ω` over `ℚ`.
  --   (2) Bezout in `ℚ[x]`:
  --         `Φ_{pq}(x) = gcd(Φ_q(x^p), Φ_p(x^q))`,
  --       hence `f(x) = Φ_q(x^p) · u(x) + Φ_p(x^q) · v(x)`
  --       with `deg u ≤ p - 1` and `deg v ≤ q - 1`.
  --   (3) The CRT bijection `Fin p × Fin q ≃ Fin (p * q)` via
  --       `(i, j) ↦ n` with `n ≡ i [mod p]` and `n ≡ j [mod q]`,
  --       giving `a_{(i,j)} = uᵢ + vⱼ`.
  --   (4) The averaging step:
  --         k · ∑_{i<k} a_{(i,i)}
  --             = ∑_{i,j<k} a_{(i,j)}
  --             ≥ 1 + 2 + ⋯ + k²
  --             = k²(k² + 1) / 2,
  --       so `∑_{i<k} a_{(i,i)} ≥ k(k² + 1) / 2 = (k³ + k) / 2`.
  --   (5) Reindexing: the partial sum `a₀ + ⋯ + a_{k-1}` along the diagonal
  --       (the first `k` "positions" under the CRT bijection) corresponds to
  --       the `(i, i)` entries because `0, 1, …, k - 1 < p ≤ q` and these
  --       are the `n` with `n ≡ n [mod p]` and `n ≡ n [mod q]`.
  sorry

end Imc2018P5
