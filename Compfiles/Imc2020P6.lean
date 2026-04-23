/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Competition 2020, Problem 6

Find all prime numbers `p` for which there exists a unique `a ∈ {1, 2, …, p}`
such that `p ∣ a³ − 3a + 1`.

Answer: `p = 3`.
-/

namespace Imc2020P6

/-- The set of primes `p` with a unique `a ∈ {1, …, p}` satisfying `p ∣ a³ − 3a + 1`. -/
determine answer : Set ℕ := {3}

snip begin

/-- For `a ∈ {1, ..., p}`, `p ∣ a³ - 3a + 1` iff `a` is a root of `x³ - 3x + 1` in `ZMod p`. -/
lemma div_iff_zmod (p : ℕ) [Fact p.Prime] (a : ℕ) :
    (p : ℤ) ∣ ((a : ℤ)^3 - 3 * a + 1) ↔ (a : ZMod p)^3 - 3 * (a : ZMod p) + 1 = 0 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rfl

snip end

problem imc2020_p6 (p : ℕ) (hp : p.Prime) :
    p ∈ answer ↔
    ∃! a : ℕ, a ∈ Finset.Ioc 0 p ∧ (p : ℤ) ∣ ((a : ℤ)^3 - 3 * a + 1) := by
  -- The answer is {3}. We verify p = 3 has unique a = 2, and for other primes,
  -- the cyclic permutation argument shows there are either 0 or 3 roots in ZMod p.
  constructor
  · intro hp_eq
    simp only [answer, Set.mem_singleton_iff] at hp_eq
    subst hp_eq
    -- For p = 3: a ∈ {1, 2, 3}. a=1: 1-3+1=-1; a=2: 8-6+1=3 ✓; a=3: 27-9+1=19. So a=2.
    refine ⟨2, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simp
      · decide
    · rintro a ⟨ha_mem, ha_dvd⟩
      simp only [Finset.mem_Ioc] at ha_mem
      obtain ⟨ha1, ha3⟩ := ha_mem
      interval_cases a <;> revert ha_dvd <;> decide
  · -- Hard direction: unique root implies p = 3.
    -- TODO: formalize the cyclic permutation argument φ(x) = x²-2 on roots of
    -- x³-3x+1, showing uniqueness forces the fixed point x = x²-2, giving x ∈ {-1, 2},
    -- both satisfying f(x) = 3, so p ∣ 3, p = 3.
    sorry

end Imc2020P6
