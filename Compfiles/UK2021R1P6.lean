/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2021, Round 1, Problem 6

Given that an integer n is the sum of two different powers of 2 and also the
sum of two different Mersenne primes, prove that n is the sum of two different
square numbers. (A Mersenne prime is a prime number which is one less than a
power of two.)
-/

namespace UK2021R1P6

/-- A Mersenne prime is a prime of the form `2^k − 1` for some `k`. -/
def IsMersennePrime (q : ℕ) : Prop :=
  q.Prime ∧ ∃ k : ℕ, q + 1 = 2 ^ k

problem uk2021_r1_p6 (n : ℕ)
    (hpow : ∃ a b : ℕ, a ≠ b ∧ n = 2 ^ a + 2 ^ b)
    (hmer : ∃ p q : ℕ, p ≠ q ∧ IsMersennePrime p ∧ IsMersennePrime q ∧ n = p + q) :
    ∃ x y : ℕ, x ≠ y ∧ n = x ^ 2 + y ^ 2 := by
  sorry

end UK2021R1P6
