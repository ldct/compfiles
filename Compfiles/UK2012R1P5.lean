/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2012, Round 1, Problem 5

Prove that the product of four consecutive positive integers cannot be equal to
the product of two consecutive positive integers.
-/

namespace UK2012R1P5

problem uk2012_r1_p5 :
    ∀ n m : ℕ, 0 < n → 0 < m →
      n * (n + 1) * (n + 2) * (n + 3) ≠ m * (m + 1) := by
  intro n m hn hm heq
  -- n(n+1)(n+2)(n+3) = (n²+3n)(n²+3n+2). Let A = n²+3n.
  -- Then 4·product + 4 = (2A+2)². And 4·m(m+1) + 1 = (2m+1)².
  -- So (2A+2)² = (2m+1)² + 3, impossible for n,m ≥ 1.
  set A : ℕ := n * n + 3 * n with hA_def
  have hAeq : n * (n + 1) * (n + 2) * (n + 3) = A * (A + 2) := by
    simp [hA_def]; ring
  rw [hAeq] at heq
  have hA_pos : 4 ≤ A := by
    have : 1 ≤ n := hn
    have h2 : n * n ≥ 1 * 1 := Nat.mul_le_mul this this
    simp [hA_def]; nlinarith
  -- 4·A(A+2) + 4 = (2A+2)².
  -- 4·m(m+1) + 1 = (2m+1)².
  -- Hence (2A+2)² - (2m+1)² = 3.
  have h1 : 4 * (A * (A + 2)) + 4 = (2 * A + 2)^2 := by ring
  have h2 : 4 * (m * (m + 1)) + 1 = (2 * m + 1)^2 := by ring
  have heqs : (2 * A + 2)^2 = (2 * m + 1)^2 + 3 := by
    have : 4 * (A * (A + 2)) + 4 = 4 * (m * (m + 1)) + 4 := by rw [heq]
    have : (2 * A + 2)^2 = 4 * (m * (m + 1)) + 4 := by linarith [h1]
    have : (2 * A + 2)^2 = (2 * m + 1)^2 + 3 := by linarith [h2]
    exact this
  -- Now (2A+2)² - (2m+1)² = 3 in ℕ.
  -- Lower bound: 2A+2 ≥ 10 > 2m+1 requires m ≤ 4 or so, but difference must be at least 2(2m+1) + 1.
  -- Work in ℤ to get factorization.
  have heqs_z : ((2 * A + 2 : ℕ) : ℤ)^2 - ((2 * m + 1 : ℕ) : ℤ)^2 = 3 := by
    have := heqs
    zify at this
    push_cast
    linarith
  have hfac : (((2 * A + 2 : ℕ) : ℤ) - ((2 * m + 1 : ℕ) : ℤ)) *
              (((2 * A + 2 : ℕ) : ℤ) + ((2 * m + 1 : ℕ) : ℤ)) = 3 := by linarith [heqs_z, sq (((2 * A + 2 : ℕ) : ℤ)), sq (((2 * m + 1 : ℕ) : ℤ))]
  -- The second factor ≥ (2*4+2) + (2*1+1) = 13. First factor * 13 ≤ 3 impossible.
  have hbig : ((2 * A + 2 : ℕ) : ℤ) + ((2 * m + 1 : ℕ) : ℤ) ≥ 13 := by
    push_cast
    have : (A : ℤ) ≥ 4 := by exact_mod_cast hA_pos
    have : (m : ℤ) ≥ 1 := by exact_mod_cast hm
    linarith
  have hpos_diff : ((2 * A + 2 : ℕ) : ℤ) - ((2 * m + 1 : ℕ) : ℤ) > 0 := by
    by_contra hle
    have hle : ((2 * A + 2 : ℕ) : ℤ) - ((2 * m + 1 : ℕ) : ℤ) ≤ 0 := le_of_not_gt hle
    -- If diff ≤ 0, then either = 0 (makes product 0) or < 0 (negative × positive = negative)
    rcases eq_or_lt_of_le hle with h0 | h0
    · rw [h0] at hfac; simp at hfac
    · have : (((2 * A + 2 : ℕ) : ℤ) - ((2 * m + 1 : ℕ) : ℤ)) *
             (((2 * A + 2 : ℕ) : ℤ) + ((2 * m + 1 : ℕ) : ℤ)) < 0 := by
        apply mul_neg_of_neg_of_pos h0
        linarith
      linarith
  -- diff ≥ 1, sum ≥ 13, product = 3. Contradiction.
  nlinarith [hfac, hbig, hpos_diff]

end UK2012R1P5
