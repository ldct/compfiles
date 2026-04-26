/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2016, Problem 8

Let `n` be a positive integer, and denote by `ZMod n` the ring of integers
modulo `n`. Suppose that there exists a function `f : ZMod n → ZMod n`
satisfying:
  (i)   `f x ≠ x`,
  (ii)  `f (f x) = x`,
  (iii) `f (f (f (x+1) + 1) + 1) = x` for all `x ∈ ZMod n`.
Prove that `n ≡ 2 (mod 4)`.

## Solution sketch

Conditions (i) and (ii) say that `f` is a fixed-point-free involution on
`ZMod n`. In particular `n` is even and `f` is a product of `n/2`
transpositions, hence `sign f = (-1)^(n/2)`.

Let `s` be the shift `x ↦ x + 1` and `g = f ∘ s`, so `g x = f (x+1)`.
Condition (iii) says `g ∘ g ∘ g = id`, i.e. `g^3 = 1`. Since `3` is prime,
every cycle of `g` has length `1` or `3`, so all cycles have odd length and
`sign g = 1`.

Hence `sign f * sign s = sign g = 1`, so `sign f = sign s = (-1)^(n-1)`.
Combining, `(-1)^(n/2) = (-1)^(n-1)`. With `n` even, we get `n/2` odd, i.e.
`n ≡ 2 (mod 4)`.
-/

namespace Imc2016P8

open Equiv Equiv.Perm

snip begin

/-- Promote `f : ZMod n → ZMod n` with `f ∘ f = id` to a permutation. -/
def fPerm {n : ℕ} (f : ZMod n → ZMod n)
    (hff : ∀ x, f (f x) = x) : Perm (ZMod n) :=
  ⟨f, f, hff, hff⟩

@[simp] lemma fPerm_apply {n : ℕ} (f : ZMod n → ZMod n)
    (hff : ∀ x, f (f x) = x) (x : ZMod n) : fPerm f hff x = f x := rfl

/-- The shift permutation `s x = x + 1` on `ZMod n`. -/
def shift (n : ℕ) : Perm (ZMod n) := Equiv.addLeft (1 : ZMod n)

@[simp] lemma shift_apply (n : ℕ) (x : ZMod n) : shift n x = 1 + x := rfl

/-- Sign of the shift permutation on `ZMod (n+1)`. -/
lemma sign_shift_succ (n : ℕ) :
    Perm.sign (shift (n + 1)) = (-1) ^ n := by
  -- `ZMod (n+1) = Fin (n+1)` definitionally. Show `shift (n+1) = finRotate (n+1)`.
  have hext : shift (n + 1) = finRotate (n + 1) := by
    apply Equiv.ext
    intro (x : Fin (n + 1))
    show (1 : Fin (n + 1)) + x = (finRotate (n + 1)) x
    simp [add_comm]
  have h := sign_finRotate n
  rw [← hext] at h
  exact h

snip end

problem imc2016_p8 (n : ℕ) (hn : 0 < n) (f : ZMod n → ZMod n)
    (hi : ∀ x, f x ≠ x)
    (hii : ∀ x, f (f x) = x)
    (hiii : ∀ x, f (f (f (x + 1) + 1) + 1) = x) :
    n % 4 = 2 := by
  haveI : NeZero n := ⟨hn.ne'⟩
  -- Set up permutations.
  set F : Perm (ZMod n) := fPerm f hii with hF_def
  set s : Perm (ZMod n) := shift n with hs_def
  set g : Perm (ZMod n) := F * s with hg_def
  -- Step 1: F is a fixed-point-free involution.
  have hF2 : F ^ 2 = 1 := by
    ext x
    simp [pow_two, Perm.mul_apply, hF_def, fPerm_apply, hii]
  have hFfix : ∀ x, F x ≠ x := fun x => by
    show f x ≠ x
    exact hi x
  -- Step 2: g satisfies g^3 = 1.
  have hgx : ∀ x, g x = f (x + 1) := by
    intro x
    show (F * s) x = _
    simp [hF_def, hs_def, fPerm_apply, shift_apply, add_comm]
  have hg3 : g ^ 3 = 1 := by
    ext x
    have h1 : (g ^ 3) x = g (g (g x)) := by
      rw [show (3 : ℕ) = 1 + 1 + 1 from rfl]
      rw [pow_succ, pow_succ, pow_one]
      simp [Perm.mul_apply]
    rw [h1, Perm.one_apply, hgx, hgx, hgx]
    exact hiii x
  -- Step 3: n is even.
  have hcardZ : Fintype.card (ZMod n) = n := ZMod.card n
  have hfixZero : Fintype.card (Function.fixedPoints F) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun ⟨x, hx⟩ => hFfix x hx⟩
  have heven : Even n := by
    have hct : F.cycleType = Multiset.replicate F.cycleType.card 2 :=
      cycleType_of_pow_prime_eq_one (p := 2) hF2
    have hsupp : F.support = Finset.univ := by
      ext x
      simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
      exact hFfix x
    have hsum : F.cycleType.sum = n := by
      rw [Equiv.Perm.sum_cycleType, hsupp, Finset.card_univ, hcardZ]
    rw [hct, Multiset.sum_replicate, smul_eq_mul] at hsum
    exact ⟨F.cycleType.card, by omega⟩
  -- Step 4: sign g = 1 (since g^3 = 1, cycleType is replicate of 3, all odd cycles).
  have hsign_g_eq : Perm.sign g = 1 := by
    have hgct : g.cycleType = Multiset.replicate g.cycleType.card 3 :=
      cycleType_of_pow_prime_eq_one (p := 3) hg3
    rw [sign_of_cycleType_eq_replicate (by norm_num : (0 : ℕ) < 3) hgct]
    rw [if_pos ⟨1, rfl⟩]
  -- Step 5: sign s = -1 (n ≥ 1 even, so n - 1 odd).
  have hsign_s : Perm.sign s = -1 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [hs_def, sign_shift_succ]
    -- m + 1 even, so m odd.
    have hm_odd : Odd m := by
      rcases heven with ⟨k, hk⟩
      refine ⟨k - 1, ?_⟩
      omega
    exact hm_odd.neg_one_pow
  -- Step 6: sign F * sign s = sign g = 1, so sign F = -1 (since sign s = -1).
  have hsign_F : Perm.sign F = -1 := by
    have hprod : Perm.sign F * Perm.sign s = 1 := by
      have : Perm.sign g = Perm.sign F * Perm.sign s := by rw [hg_def, map_mul]
      rw [hsign_g_eq] at this
      exact this.symm
    rw [hsign_s] at hprod
    -- sign F * (-1) = 1, so sign F = -1.
    have h2 : Perm.sign F * (-1) * (-1) = 1 * (-1) := by rw [hprod]
    have h3 : Perm.sign F = -1 := by
      rw [show (Perm.sign F : ℤˣ) * (-1) * (-1) = Perm.sign F by
        rw [mul_assoc]; norm_num] at h2
      simpa using h2
    exact h3
  -- Step 7: sign F = (-1)^(n/2) by sign_of_pow_two_eq_one.
  have hsignF_formula : Perm.sign F = (-1 : ℤˣ) ^ ((Fintype.card (ZMod n) -
      Fintype.card (Function.fixedPoints F)) / 2) := sign_of_pow_two_eq_one hF2
  rw [hcardZ, hfixZero, Nat.sub_zero] at hsignF_formula
  rw [hsign_F] at hsignF_formula
  -- (-1) = (-1)^(n/2) means n/2 is odd.
  have hn2_odd : Odd (n / 2) := by
    by_contra h
    rw [Nat.not_odd_iff_even] at h
    have hh : ((-1 : ℤˣ)) ^ (n / 2) = 1 := h.neg_one_pow
    rw [hh] at hsignF_formula
    exact absurd hsignF_formula (by decide)
  -- n is even and n/2 is odd, so n ≡ 2 mod 4.
  obtain ⟨j, hj⟩ := hn2_odd
  obtain ⟨k, hk⟩ := heven
  have : n = 2 * (n / 2) := by omega
  omega

end Imc2016P8
