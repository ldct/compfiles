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
    -- Strategy: if a is a root, then φ(a) = a² - 2 is also a root (identity
    -- below). Uniqueness forces a = a² - 2, giving a ∈ {-1, 2}. Both give f(a) = 3,
    -- so p ∣ 3, hence p = 3.
    rintro ⟨a, ⟨ha_mem, ha_dvd⟩, huniq⟩
    simp only [Finset.mem_Ioc] at ha_mem
    obtain ⟨ha1, ha3⟩ := ha_mem
    -- Root in ZMod p
    have hzp : Fact p.Prime := ⟨hp⟩
    have ha_zm : (a : ZMod p)^3 - 3 * (a : ZMod p) + 1 = 0 :=
      (div_iff_zmod p a).mp ha_dvd
    -- Let b = a² - 2 in ZMod p. Then b is also a root:
    -- (a²-2)³ - 3(a²-2) + 1 = (a+1)² · (a³-3a+1)
    have hkey : ∀ x : ZMod p,
        (x^2 - 2)^3 - 3 * (x^2 - 2) + 1 = (x^3 - 3*x - 1) * (x^3 - 3*x + 1) := by
      intro x; ring
    -- So b = a² - 2 is a root in ZMod p.
    -- Pick a natural number representative b' ∈ {1, ..., p} of b.
    -- Actually, we can use the fact that (a+1)² * f(a) = 0 in ZMod p, so
    -- ((a²-2) as a ZMod p element) is a root. Now we want to convert this back
    -- to a witness in {1, ..., p}.
    -- Define b_nat := ZMod.val (a² - 2 : ZMod p) if that's nonzero, else p.
    set bzm : ZMod p := (a : ZMod p)^2 - 2 with hbzm
    have hb_root : bzm^3 - 3 * bzm + 1 = 0 := by
      rw [hbzm, hkey, ha_zm, mul_zero]
    -- Construct a natural number b' in {1, ..., p} with (b' : ZMod p) = bzm
    set b' : ℕ := if bzm = 0 then p else bzm.val with hb'def
    have hb'_mem : b' ∈ Finset.Ioc 0 p := by
      rw [Finset.mem_Ioc]
      refine ⟨?_, ?_⟩
      · simp only [hb'def]
        split_ifs with h
        · exact hp.pos
        · exact Nat.pos_of_ne_zero (fun hz => h (by rw [← ZMod.val_eq_zero]; exact hz))
      · simp only [hb'def]
        split_ifs with h
        · exact le_refl _
        · exact Nat.le_of_lt (ZMod.val_lt _)
    have hbcast : (b' : ZMod p) = bzm := by
      simp only [hb'def]
      split_ifs with h
      · simp [h]
      · exact ZMod.natCast_zmod_val _
    have hb'_dvd : (p : ℤ) ∣ ((b' : ℤ)^3 - 3 * b' + 1) := by
      rw [div_iff_zmod]
      push_cast
      rw [hbcast]
      exact hb_root
    -- By uniqueness, b' = a.
    have hb'_eq_a : b' = a := huniq b' ⟨hb'_mem, hb'_dvd⟩
    -- So (b' : ZMod p) = (a : ZMod p), i.e., bzm = a_zmod (with some casting care).
    have ha_eq_b : bzm = (a : ZMod p) := by
      simp only [hb'def] at hb'_eq_a
      split_ifs at hb'_eq_a with h
      · -- bzm = 0 and p = a, so a ≥ p + 1... but a ≤ p, so a = p, so a ≡ 0 mod p
        subst hb'_eq_a
        -- bzm = 0 means (a : ZMod p) = a^2 - 2 when bzm = 0 means 0 = a^2 - 2 in ZMod p
        -- but here bzm = 0 so a^2 - 2 = 0 in ZMod p
        -- Also a = p means (a : ZMod p) = 0
        rw [h]
        have : (p : ZMod p) = 0 := by simp
        push_cast
        exact this.symm
      · -- bzm.val = a
        rw [← hb'_eq_a]
        rw [ZMod.natCast_zmod_val]
    -- So (a : ZMod p)^2 - 2 = (a : ZMod p), i.e., (a+1)(a-2) = 0 in ZMod p.
    have h_quad : ((a : ZMod p) + 1) * ((a : ZMod p) - 2) = 0 := by
      have : (a : ZMod p)^2 - 2 - (a : ZMod p) = 0 := by
        rw [sub_eq_zero]; exact ha_eq_b
      have : (a : ZMod p)^2 - (a : ZMod p) - 2 = 0 := by linear_combination this
      linear_combination this
    -- Hence a ≡ -1 or a ≡ 2 in ZMod p.
    rcases mul_eq_zero.mp h_quad with h | h
    · -- a ≡ -1 (mod p), so f(a) = f(-1) = -1 + 3 + 1 = 3, but we also know f(a) ≡ 0,
      -- so 3 ≡ 0 (mod p), i.e., p ∣ 3.
      have ha_neg : (a : ZMod p) = -1 := by linear_combination h
      have h3zm : (3 : ZMod p) = 0 := by
        have hz := ha_zm
        rw [ha_neg] at hz
        linear_combination hz
      have h3int : ((3 : ℤ) : ZMod p) = 0 := by push_cast; exact h3zm
      have hpdvd3 : (p : ℤ) ∣ (3 : ℤ) := by
        rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h3int
      have hp3 : p ∣ 3 := by exact_mod_cast hpdvd3
      have hp_le : p ≤ 3 := Nat.le_of_dvd (by norm_num) hp3
      have hp_ge : 2 ≤ p := hp.two_le
      -- p ∈ {2, 3}. Show p = 3 by excluding p = 2.
      have hp_ne_2 : p ≠ 2 := by
        intro hp2
        subst hp2
        interval_cases a
        · revert ha_dvd; decide
        · revert ha_dvd; decide
      show p = 3
      omega
    · have ha_pos : (a : ZMod p) = 2 := by linear_combination h
      have h3zm : (3 : ZMod p) = 0 := by
        have hz := ha_zm
        rw [ha_pos] at hz
        linear_combination hz
      have h3int : ((3 : ℤ) : ZMod p) = 0 := by push_cast; exact h3zm
      have hpdvd3 : (p : ℤ) ∣ (3 : ℤ) := by
        rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h3int
      have hp3 : p ∣ 3 := by exact_mod_cast hpdvd3
      have hp_le : p ≤ 3 := Nat.le_of_dvd (by norm_num) hp3
      have hp_ge : 2 ≤ p := hp.two_le
      -- p ∈ {2, 3}. Show p = 3 by excluding p = 2.
      have hp_ne_2 : p ≠ 2 := by
        intro hp2
        subst hp2
        interval_cases a
        · revert ha_dvd; decide
        · revert ha_dvd; decide
      show p = 3
      omega

end Imc2020P6
