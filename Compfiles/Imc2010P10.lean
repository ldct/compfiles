/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2010, Problem 10
(Day 2, Problem 5)

Suppose that for `f : ℝ → ℝ` and reals `a < b`, `f(x) = 0` for all
`x ∈ (a, b)`. Prove that `f ≡ 0` if
  `∑_{k=0}^{p-1} f(y + k/p) = 0`
for every prime `p` and every `y ∈ ℝ`.

The proof, following the official solution, considers for each integer
`N > 1` the ideal
  `J_N = { ∑ c_k x^k ∈ ℝ[x] | ∀ x, ∑ c_k f(x + k/N) = 0 }`.
For each prime `p ∣ N` the polynomial `(x^N - 1)/(x^{N/p} - 1)` lies in
`J_N`. Their gcd is `Φ_N`, the `N`-th cyclotomic polynomial. Since
`liminf φ(N)/N = 0`, we may choose `N` with `φ(N)/N < b - a`, and the
recurrence given by `Φ_N` propagates the vanishing of `f` from `(a,b)`
to all of `ℝ`.
-/

namespace Imc2010P10

snip begin

/-- The hypothesis that all prime arithmetic-progression sums vanish. -/
def PrimeSumZero (f : ℝ → ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ y : ℝ, ∑ k ∈ Finset.range p, f (y + k / p) = 0

/-- The `p = 2` instance of `PrimeSumZero`: `f(y) + f(y + 1/2) = 0`. -/
lemma half_relation {f : ℝ → ℝ} (hsum : PrimeSumZero f) (y : ℝ) :
    f y + f (y + 1/2) = 0 := by
  have h := hsum 2 Nat.prime_two y
  simp [Finset.sum_range_succ] at h
  -- after simp: f y + f (y + 2⁻¹) = 0
  have eq : y + 1/2 = y + 2⁻¹ := by ring
  rw [eq]; exact h

snip end

problem imc2010_p10 (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hzero : ∀ x ∈ Set.Ioo a b, f x = 0)
    (hsum : ∀ p : ℕ, p.Prime → ∀ y : ℝ,
      ∑ k ∈ Finset.range p, f (y + k / p) = 0) :
    ∀ x, f x = 0 := by
  -- TODO: Full proof requires:
  -- (1) For each integer N > 1, define the ideal J_N ⊆ ℝ[x] of
  --     polynomials ∑ c_k x^k with ∑ c_k f(x + k/N) = 0 for all x.
  -- (2) Show (x^N - 1)/(x^{N/p} - 1) ∈ J_N for each prime p ∣ N.
  -- (3) Compute the gcd of these polynomials to be Φ_N.
  -- (4) Hence Φ_N ∈ J_N (degree φ(N)).
  -- (5) Since liminf φ(N)/N = 0, choose N with φ(N)/N < b - a.
  -- (6) Use the recurrence from Φ_N to propagate vanishing of f
  --     from (a, b) to all of ℝ.
  sorry

end Imc2010P10
