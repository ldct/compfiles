/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Competition 2010, Problem 4

Let `a, b` be integers and suppose `n` is a positive integer for which
  `ℤ ∖ { a x^n + b y^n | x, y ∈ ℤ }`
is finite. Prove that `n = 1`.
-/

namespace Imc2010P4

/-- The set of integers representable as `a x^n + b y^n`. -/
def repSet (a b : ℤ) (n : ℕ) : Set ℤ :=
  { m | ∃ x y : ℤ, m = a * x ^ n + b * y ^ n }

snip begin

/-- The trivial set `{0}` is contained in `repSet 0 0 n`; in fact `repSet 0 0 n = {0}`. -/
lemma repSet_zero_zero (n : ℕ) : repSet 0 0 n = {0} := by
  ext m
  simp only [repSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, y, h⟩
    simp at h
    exact h
  · intro hm
    exact ⟨0, 0, by simp [hm]⟩

/-- If `a = 0`, `repSet 0 b n = {b * y^n : y ∈ ℤ}`. -/
lemma repSet_zero_left (b : ℤ) (n : ℕ) :
    repSet 0 b n = { m | ∃ y : ℤ, m = b * y ^ n } := by
  ext m
  simp only [repSet, Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨_, y, h⟩
    exact ⟨y, by simpa using h⟩
  · rintro ⟨y, h⟩
    exact ⟨0, y, by simpa using h⟩

/-- If `b = 0`, `repSet a 0 n = {a * x^n : x ∈ ℤ}`. -/
lemma repSet_zero_right (a : ℤ) (n : ℕ) :
    repSet a 0 n = { m | ∃ x : ℤ, m = a * x ^ n } := by
  ext m
  simp only [repSet, Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, _, h⟩
    exact ⟨x, by simpa using h⟩
  · rintro ⟨x, h⟩
    exact ⟨x, 0, by simpa using h⟩

/-- For `n ≥ 2`, the complement of the representable set is infinite.

This is the key technical lemma. The official solution proceeds by choosing a prime `p ∣ n`,
WLOG `gcd(a, b) = 1`, and then analyzing residues:

* If `p = 2`: case-split on parities of `a, b`. If `b` is even, `a x² + b y²` takes at most 6
  residues mod 8. If both odd, `a x² + b y² ≡ x² ± y² (mod 4)` misses residue 3 (or 2).

* If `p ≥ 3`: `(x + kp)^p ≡ x^p (mod p²)`, so `p`-th powers take ≤ `p` residues mod `p²`,
  giving `a x^p + b y^p` at most `p²` residues mod `p²`. If strictly fewer, done. Otherwise
  one shows `p² ∣ a x^p + b y^p ⇒ p ∣ x, p ∣ y ⇒ p^p ∣ a x^p + b y^p`, so integers `≡ p² (mod p³)`
  are not representable.

We currently leave this as a TODO. -/
lemma complement_infinite_of_ge_two (a b : ℤ) (n : ℕ) (hn : 2 ≤ n) :
    ((repSet a b n)ᶜ : Set ℤ).Infinite := by
  sorry

snip end

problem imc2010_p4 (a b : ℤ) (n : ℕ) (hn : 1 ≤ n)
    (hfin : ((repSet a b n)ᶜ : Set ℤ).Finite) : n = 1 := by
  -- Suppose for contradiction n ≥ 2. Then the complement is infinite, contradicting hfin.
  by_contra hne
  have h2 : 2 ≤ n := by omega
  exact (complement_infinite_of_ge_two a b n h2) hfin

end Imc2010P4
