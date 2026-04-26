/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2007, Problem 6
(IMC 2007, Day 1, Problem 6)

How many nonzero coefficients can a polynomial `P ∈ ℤ[X]` have if
`|P(z)| ≤ 2` for all complex `z` with `|z| = 1`?

Answer: at most 2.
-/

namespace Imc2007P6

open Polynomial Complex Finset

snip begin

/-- Sum of `n`-th roots of unity raised to an integer power: if `n ≥ 1` and
`n ∤ m`, the sum is zero; if `n ∣ m` (which includes `m = 0`), the sum is `n`. -/
lemma sum_primitive_root_pow {n : ℕ} (hn : 1 ≤ n) (w : ℂ) (hw : w ^ n = 1)
    (hwp : ∀ k, 0 < k → k < n → w ^ k ≠ 1) (m : ℕ) :
    ∑ k ∈ range n, (w ^ k) ^ m = if n ∣ m then (n : ℂ) else 0 := by
  by_cases hdiv : n ∣ m
  · rw [if_pos hdiv]
    obtain ⟨q, rfl⟩ := hdiv
    have h1 : ∀ k ∈ range n, (w ^ k) ^ (n * q) = 1 := by
      intro k _
      rw [← pow_mul, mul_comm k (n * q), mul_assoc, pow_mul, hw, one_pow]
    rw [sum_congr rfl h1]
    simp
  · rw [if_neg hdiv]
    -- sum of geometric series with ratio w^m ≠ 1
    have hwm_ne : w ^ m ≠ 1 := by
      intro hwm
      apply hdiv
      -- w has order dividing n, so if w^m = 1 then (order of w) ∣ m. But order is exactly n.
      -- Use orderOf.
      have horder : orderOf w = n := by
        apply orderOf_eq_of_pow_and_pow_div_prime (n := n) hn hw
        intros p hp hpd
        -- w^(n/p) ≠ 1 since p ≥ 2 so n/p < n and n/p > 0 (as p | n and p ≤ n, and n ≥ 1)
        have hp2 : 2 ≤ p := hp.two_le
        have hpos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hpd) (by omega)
        have hlt : n / p < n := Nat.div_lt_self (by omega) hp2
        exact hwp _ hpos hlt
      rw [← horder]
      exact orderOf_dvd_of_pow_eq_one hwm
    -- Now compute sum.
    have : ∀ k ∈ range n, (w ^ k) ^ m = (w ^ m) ^ k := by
      intros k _; rw [← pow_mul, ← pow_mul, mul_comm]
    rw [sum_congr rfl this]
    rw [geom_sum_eq hwm_ne n]
    rw [← pow_mul, mul_comm, pow_mul, hw, one_pow]
    simp

/-- Sum of geometric progression specialized to roots of unity: for `w` a primitive
`n`-th root of unity and `0 ≤ m < n` and `m ≠ 0`, the sum of `w^(k*m)` over `k` in
`range n` is zero. -/
lemma sum_roots_of_unity_zero {n : ℕ} (hn : 1 ≤ n) (w : ℂ) (hw : w ^ n = 1)
    (hwp : ∀ k, 0 < k → k < n → w ^ k ≠ 1) {m : ℕ} (hm : 0 < m) (hmn : m < n) :
    ∑ k ∈ range n, (w ^ k) ^ m = 0 := by
  rw [sum_primitive_root_pow hn w hw hwp m]
  rw [if_neg]
  intro hdiv
  have : n ≤ m := Nat.le_of_dvd hm hdiv
  omega

snip end

/-- IMC 2007 P6: Any integer polynomial with absolute value at most 2 on the
unit circle has at most 2 nonzero coefficients.

Proof sketch (not yet fully formalized):
Suppose `P` has ≥ 2 nonzero coefficients. Let `i = min P.support` and
`j = max P.support`; set `n = j - i ≥ 1`. Multiplying by `z^{-i}` (which has
modulus 1 on the unit circle), reduce to the case where the polynomial
`Q(z) = a_0 + a_1 z + ⋯ + a_n z^n` has `a_0 ≠ 0` and `a_n ≠ 0`. WLOG `a_0 > 0`
(else replace `Q` by `-Q`). Choose `w_k` such that `a_n w_k^n = |a_n|`; these
are `n` distinct unit-modulus complex numbers obtained by rotating the `n`-th
roots of unity by a fixed root of `z^n = ±1`. Then

  `(1/n) ∑_{k=0}^{n-1} Q(w_k) = a_0 + |a_n|`,

because every intermediate monomial `a_ℓ z^ℓ` with `1 ≤ ℓ ≤ n-1` sums to zero
over the `w_k`. Hence

  `2 ≥ (1/n) ∑ |Q(w_k)| ≥ |(1/n) ∑ Q(w_k)| = a_0 + |a_n| ≥ 1 + 1 = 2`,

so `a_0 = |a_n| = 1` and equality forces `Q(w_k) = 2` for every `k`, i.e., the
middle polynomial `a_1 z + ⋯ + a_{n-1} z^{n-1}` vanishes at `n` distinct points
`w_k` while having degree less than `n`. So the middle polynomial is zero, and
`Q(z) = 1 + a_n z^n` has exactly 2 nonzero coefficients, hence so does `P`. -/
problem imc2007_p6 (P : ℤ[X])
    (hP : ∀ z : ℂ, ‖z‖ = 1 → ‖(P.map (Int.castRingHom ℂ)).eval z‖ ≤ 2) :
    P.support.card ≤ 2 := by
  -- TODO: full formalization of the averaging-over-roots-of-unity argument.
  sorry

end Imc2007P6
