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
    -- TODO: Precise proof plan (following imc2025-day2-solutions P7):
    -- 1. Closure under addition: x + y = 2x + 2y both have the same parity;
    --    specifically (2x + 2y)/2 = x + y ∈ M, using (a) and (b).
    -- 2. Closure under multiplication by ℕ (by induction on the multiplier,
    --    using closure under addition).
    -- 3. Existence of an odd element: if x ∈ M, then (x + 2x)/2 = 3x/2 ∈ M
    --    (x + 2x = 3x, even iff x even); iterate to strip off factors of 2,
    --    showing M contains the odd part of some element, hence contains odd elements.
    -- 4. Let d = gcd of all members of M. Since M contains odd elements, d is odd.
    --    M ⊆ d ℕ_{>0}. By Bezout-like argument using closure under addition and
    --    existence of two elements with difference d (from the gcd structure),
    --    find a, a+d ∈ M with a > c := min M.
    -- 5. Key implication: (a, a+d ∈ M and c < a) ⇒ a - d ∈ M. Proof: pick
    --    largest x ∈ M with x < a; show x = a - d by checking (x+a+d)/2 is
    --    forced to be a, using M ⊆ dℤ.
    -- 6. Dual implication: (a - d, a ∈ M) ⇒ a + d ∈ M (similar argument using 2a ∈ M).
    -- 7. Conclude M = {c + kd : k ∈ ℕ, c + kd > 0}, which is the target form.
    -- Mathlib gaps: requires manually constructing a descent argument and
    -- manipulating gcd over infinite sets; no direct single-lemma formalization.
    sorry

end Imc2025P7
