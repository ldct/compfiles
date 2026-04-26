/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2018, Problem 9

Determine all pairs `P(x), Q(x)` of monic complex polynomials such that
`P ∣ Q² + 1` and `Q ∣ P² + 1`.

Answer: `(1, 1)` and `(P, P ± i)` for any monic nonconstant `P`.
-/

namespace Imc2018P9

open Polynomial

/-- The set of all pairs `(P, Q)` of monic complex polynomials with `P ∣ Q²+1` and
`Q ∣ P²+1`. The answer is: either both equal `1`, or `P` is a monic nonconstant
polynomial and `Q = P ± i`. -/
determine answer : Set (Polynomial ℂ × Polynomial ℂ) :=
  { pq | (pq.1 = 1 ∧ pq.2 = 1) ∨
         (1 ≤ pq.1.natDegree ∧ pq.2 = pq.1 + C Complex.I) ∨
         (1 ≤ pq.1.natDegree ∧ pq.2 = pq.1 - C Complex.I) }

snip begin

/-- The polynomial identity `P² + 1 = (P - i)(P + i)` over `ℂ`. -/
lemma sq_add_one_factor (P : Polynomial ℂ) :
    P ^ 2 + 1 = (P - C Complex.I) * (P + C Complex.I) := by
  have hCI2 : (C Complex.I) ^ 2 = -1 := by
    rw [← C_pow, Complex.I_sq, C_neg, C_1]
  have : (P - C Complex.I) * (P + C Complex.I) = P^2 - (C Complex.I)^2 := by ring
  rw [this, hCI2]
  ring

snip end

problem imc2018_p9 (P Q : Polynomial ℂ) (hP : P.Monic) (hQ : Q.Monic) :
    (P ∣ Q^2 + 1 ∧ Q ∣ P^2 + 1) ↔ (P, Q) ∈ answer := by
  constructor
  · -- Forward: hard direction (Vieta jumping descent).
    -- TODO: Show that `gcd(P, Q) = 1`, hence `PQ ∣ P² + Q² + 1`, then
    -- by induction on `natDegree P + natDegree Q` reduce to `deg P = deg Q`,
    -- whence `(P²+Q²+1) = 2PQ` (leading coefficient comparison), giving
    -- `(P-Q)² = -1` and `Q = P ± i`.
    sorry
  · -- Backward: each case in `answer` satisfies the divisibility.
    rintro (⟨hP1, hQ1⟩ | ⟨hPdeg, hQeq⟩ | ⟨hPdeg, hQeq⟩)
    · -- P = Q = 1.
      simp only at hP1 hQ1
      subst hP1; subst hQ1
      exact ⟨one_dvd _, one_dvd _⟩
    · -- Q = P + i.
      simp only at hQeq
      have hCI2 : (C Complex.I) ^ 2 = -1 := by
        rw [← C_pow, Complex.I_sq, C_neg, C_1]
      refine ⟨?_, ?_⟩
      · -- P ∣ Q² + 1 = (P+i)² + 1 = P² + 2iP = P(P + 2i).
        rw [hQeq]
        refine ⟨P + 2 * C Complex.I, ?_⟩
        have : (P + C Complex.I)^2 + 1 = P * (P + 2 * C Complex.I) + ((C Complex.I)^2 + 1) := by
          ring
        rw [this, hCI2]
        ring
      · -- Q ∣ P² + 1 = (P-i)(P+i) = (Q - 2i)·Q. So Q ∣ P²+1.
        rw [hQeq]
        refine ⟨P - C Complex.I, ?_⟩
        rw [sq_add_one_factor]
        ring
    · -- Q = P - i.
      simp only at hQeq
      have hCI2 : (C Complex.I) ^ 2 = -1 := by
        rw [← C_pow, Complex.I_sq, C_neg, C_1]
      refine ⟨?_, ?_⟩
      · -- P ∣ Q² + 1 = (P-i)² + 1 = P² - 2iP = P(P - 2i).
        rw [hQeq]
        refine ⟨P - 2 * C Complex.I, ?_⟩
        have : (P - C Complex.I)^2 + 1 = P * (P - 2 * C Complex.I) + ((C Complex.I)^2 + 1) := by
          ring
        rw [this, hCI2]
        ring
      · -- Q ∣ P² + 1 = (P-i)(P+i) = Q·(P + i).
        rw [hQeq]
        refine ⟨P + C Complex.I, ?_⟩
        rw [sq_add_one_factor]

end Imc2018P9
