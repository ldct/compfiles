/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Competition 2025, Problem 7

Let `ℤ>0` be the set of positive integers. Find all nonempty subsets
`M ⊆ ℤ>0` satisfying both of the following properties:

  (a) if `x ∈ M`, then `2x ∈ M`,
  (b) if `x, y ∈ M` and `x + y` is even, then `(x + y)/2 ∈ M`.

Answer: `M` is of the form `{(m + k) * d | k ∈ ℕ}` for some positive integer
`m` and positive *odd* integer `d`.
-/

namespace Imc2025P7

/-- The set of "nice" subsets — those of the form `{(m + k) * d | k ∈ ℕ}`
for some positive integer `m` and positive odd integer `d`. -/
determine answer : Set (Set ℕ) :=
  { M | ∃ m d : ℕ, 0 < m ∧ 0 < d ∧ Odd d ∧
    M = { x | ∃ k : ℕ, x = (m + k) * d } }

problem imc2025_p7 (M : Set ℕ) (hMsub : M ⊆ Set.Ioi 0) (hMne : M.Nonempty) :
    M ∈ answer ↔
    ((∀ x ∈ M, 2 * x ∈ M) ∧
     (∀ x ∈ M, ∀ y ∈ M, Even (x + y) → (x + y) / 2 ∈ M)) := by
  constructor
  · -- Forward direction: straightforward computation.
    rintro ⟨m, d, hm, hd, hdOdd, rfl⟩
    refine ⟨?_, ?_⟩
    · -- 2x ∈ M when x ∈ M.
      rintro x ⟨k, rfl⟩
      refine ⟨m + 2 * k, ?_⟩
      ring
    · -- (x + y) / 2 ∈ M when x, y ∈ M and x + y even.
      rintro x ⟨k, rfl⟩ y ⟨l, rfl⟩ heven
      obtain ⟨c, hc⟩ := hdOdd
      subst hc
      -- Now d = 2*c + 1.
      have hkl : Even (k + l) := by
        rcases Nat.even_or_odd (k + l) with he | ho
        · exact he
        · exfalso
          -- (m+k)(2c+1) + (m+l)(2c+1) = (2m+k+l)(2c+1)
          -- 2m+k+l is odd since 2m even and k+l odd; product of odd*odd is odd.
          have h2mkl_odd : Odd (2 * m + (k + l)) := by
            have h2m_even : Even (2 * m) := ⟨m, by ring⟩
            exact Even.add_odd h2m_even ho
          have hd_odd : Odd (2 * c + 1) := ⟨c, rfl⟩
          have hprod_odd : Odd ((2 * m + (k + l)) * (2 * c + 1)) := h2mkl_odd.mul hd_odd
          have heq : (m + k) * (2 * c + 1) + (m + l) * (2 * c + 1)
                   = (2 * m + (k + l)) * (2 * c + 1) := by ring
          rw [heq] at heven
          exact (Nat.not_even_iff_odd.mpr hprod_odd) heven
      obtain ⟨c', hc'⟩ := hkl
      refine ⟨c', ?_⟩
      show ((m + k) * (2 * c + 1) + (m + l) * (2 * c + 1)) / 2 = (m + c') * (2 * c + 1)
      rw [show (m + k) * (2 * c + 1) + (m + l) * (2 * c + 1)
           = (2 * m + (k + l)) * (2 * c + 1) from by ring]
      rw [show k + l = c' + c' from hc']
      rw [show 2 * m + (c' + c') = 2 * (m + c') from by ring]
      rw [show 2 * (m + c') * (2 * c + 1) = 2 * ((m + c') * (2 * c + 1)) from by ring]
      exact Nat.mul_div_cancel_left _ (by norm_num : (0 : ℕ) < 2)
  · -- Reverse direction: the official solution's argument.
    rintro ⟨hdouble, hhalf⟩
    -- Step 1: closure under addition. x + y = (2x + 2y)/2 ∈ M.
    have hadd : ∀ x ∈ M, ∀ y ∈ M, x + y ∈ M := by
      intro x hx y hy
      have h2x : 2 * x ∈ M := hdouble x hx
      have h2y : 2 * y ∈ M := hdouble y hy
      have heven : Even (2 * x + 2 * y) := ⟨x + y, by ring⟩
      have := hhalf _ h2x _ h2y heven
      convert this using 1
      omega
    -- Step 2: closure under multiplication by positive naturals.
    have hmul : ∀ n : ℕ, 0 < n → ∀ x ∈ M, n * x ∈ M := by
      intro n hn x hx
      induction n with
      | zero => exact absurd hn (by omega)
      | succ k ih =>
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk; simpa using hx
        · have : k * x ∈ M := ih hk
          have := hadd _ this _ hx
          convert this using 1; ring
    -- Step 3: M contains an odd number.
    -- Plan: from any x ∈ M, (x + 2x)/2 = 3x/2 ∈ M when x even; iterate to
    -- strip off factors of 2. Specifically, for each x ∈ M, the odd part of
    -- x times some power of 3 is in M. We show M contains some odd number.
    -- TODO: formalize remaining steps (gcd argument, descent, final AP form).
    -- The full remaining proof requires:
    --   (a) strong induction: if x ∈ M and x = 2^a * b with b odd, then b*3^a ∈ M
    --       (or some odd multiple of b lies in M),
    --   (b) defining d := gcd of M (over infinite set), showing d | every element,
    --   (c) showing M ⊆ d·ℕ>0 and finding a with a, a+d ∈ M,
    --   (d) descent step: a, a+d ∈ M, a > min M ⇒ a - d ∈ M,
    --   (e) ascent step: a-d, a ∈ M ⇒ a+d ∈ M,
    --   (f) assembling M = {(m + k)*d : k ∈ ℕ}.
    sorry

end Imc2025P7
