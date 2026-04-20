/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2020, Round 1, Problem 1

Show that there are at least three prime numbers p less than 200 for which
p + 2, p + 6, p + 8 and p + 12 are all prime. Show also that there is only
one prime number q for which q + 2, q + 6, q + 8, q + 12 and q + 14 are all
prime.
-/

namespace UK2020R1P1

/-- The unique prime q with q, q + 2, q + 6, q + 8, q + 12, q + 14 all prime
    is q = 5 (giving 5, 7, 11, 13, 17, 19). -/
determine solution_value : ℕ := 5

/-- Part (a): at least three primes p < 200 with p, p + 2, p + 6, p + 8, p + 12
    all prime. Part (b): the unique such prime with the extra condition
    p + 14 also prime is solution_value = 5. -/
problem uk2020_r1_p1 :
    (∃ S : Finset ℕ, S.card ≥ 3 ∧
      ∀ p ∈ S, p < 200 ∧ p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧
                 (p + 8).Prime ∧ (p + 12).Prime) ∧
    { q : ℕ | q.Prime ∧ (q + 2).Prime ∧ (q + 6).Prime ∧ (q + 8).Prime ∧
              (q + 12).Prime ∧ (q + 14).Prime } = { solution_value } := by
  refine ⟨?_, ?_⟩
  · -- Witness: {5, 11, 101}.
    refine ⟨{5, 11, 101}, by decide, ?_⟩
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl <;> refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · ext q
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, solution_value]
    constructor
    · rintro ⟨hq, hq2, hq6, hq8, hq12, hq14⟩
      -- Mod 5 analysis: q, q+2, q+6, q+8, q+12, q+14 cover residues 0,2,1,3,2,4 mod 5
      -- i.e., q mod 5 + {0,2,1,3,2,4} covers all of {0,1,2,3,4} mod 5 (since {0,1,2,3,4} ⊂ {0,2,1,3,2,4} mod 5).
      -- So one of them is ≡ 0 mod 5, hence = 5 (since all are prime).
      -- If q = 5, done. Otherwise q+2=5 ⇒ q=3, but q+6=9 not prime.
      -- q+6=5 ⇒ q=-1 impossible. q+8=5 ⇒ q=-3 impossible. q+12=5 ⇒ q=-7 impossible. q+14=5 ⇒ q=-9 impossible.
      -- Actually need to also check q = 5 case directly.
      by_contra hne
      -- q ≠ 5. We'll derive contradiction.
      -- Consider q mod 5.
      have : q % 5 = 0 ∨ q % 5 = 1 ∨ q % 5 = 2 ∨ q % 5 = 3 ∨ q % 5 = 4 := by omega
      rcases this with h | h | h | h | h
      · -- q ≡ 0 mod 5 and q prime → q = 5. Contradiction with hne.
        have : 5 ∣ q := Nat.dvd_of_mod_eq_zero h
        have := hq.eq_one_or_self_of_dvd 5 this
        omega
      · -- q ≡ 1 mod 5 → q+14 ≡ 0 mod 5. So 5 | q+14, and q+14 prime → q+14 = 5. But q ≥ 2, q+14 ≥ 16 > 5.
        have : 5 ∣ q + 14 := by omega
        have := hq14.eq_one_or_self_of_dvd 5 this
        have : 2 ≤ q := hq.two_le
        omega
      · -- q ≡ 2 mod 5 → q+8 ≡ 0 mod 5 or q+12 ≡ 0. q+8 ≡ 10 ≡ 0.
        have : 5 ∣ q + 8 := by omega
        have := hq8.eq_one_or_self_of_dvd 5 this
        have : 2 ≤ q := hq.two_le
        omega
      · -- q ≡ 3 mod 5 → q+2 ≡ 0. 5 | q+2. So q+2 = 5, i.e. q = 3.
        -- But q = 3 → q+6 = 9 = 3² not prime. Contradiction.
        have h5 : 5 ∣ q + 2 := by omega
        have hq25 := hq2.eq_one_or_self_of_dvd 5 h5
        have : 2 ≤ q := hq.two_le
        have hq3 : q = 3 := by omega
        subst hq3
        exact absurd hq6 (by decide)
      · -- q ≡ 4 mod 5 → q+6 ≡ 0.
        have : 5 ∣ q + 6 := by omega
        have := hq6.eq_one_or_self_of_dvd 5 this
        have : 2 ≤ q := hq.two_le
        omega
    · rintro rfl
      refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

end UK2020R1P1
