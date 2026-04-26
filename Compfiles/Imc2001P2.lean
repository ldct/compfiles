/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2001, Problem 2
(IMC 2001, Day 1, Problem 2)

Let `r, s, t` be pairwise coprime positive integers, and let `a, b` be elements
of a commutative group with `a^r = b^s = (ab)^t = e`. Prove that `a = b = e`.
-/

namespace Imc2001P2

snip begin

/-- If `x^m = 1` and `x^n = 1` with `gcd(m, n) = 1`, then `x = 1`. -/
lemma eq_one_of_pow_eq_one_of_coprime {G : Type*} [Group G] {x : G} {m n : ℕ}
    (hm : x ^ m = 1) (hn : x ^ n = 1) (hcop : Nat.Coprime m n) : x = 1 := by
  have hdm : orderOf x ∣ m := orderOf_dvd_of_pow_eq_one hm
  have hdn : orderOf x ∣ n := orderOf_dvd_of_pow_eq_one hn
  have hdvd : orderOf x ∣ Nat.gcd m n := Nat.dvd_gcd hdm hdn
  rw [hcop] at hdvd
  have : orderOf x = 1 := Nat.dvd_one.mp hdvd
  exact orderOf_eq_one_iff.mp this

snip end

problem imc2001_p2 {G : Type*} [CommGroup G] (a b : G) (r s t : ℕ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (hrs : Nat.Coprime r s) (hrt : Nat.Coprime r t) (hst : Nat.Coprime s t)
    (har : a ^ r = 1) (hbs : b ^ s = 1) (habt : (a * b) ^ t = 1) :
    a = 1 ∧ b = 1 := by
  -- From commutativity: (a*b)^t = a^t * b^t = 1
  have hab_eq : a ^ t * b ^ t = 1 := by
    rw [← mul_pow]; exact habt
  -- a^(t*s) = 1: since a^t * b^t = 1, multiply both sides by themselves appropriately.
  -- (a^t * b^t)^s = 1, so a^(ts) * b^(ts) = 1, and b^(ts) = (b^s)^t = 1, so a^(ts) = 1.
  have hats : a ^ (t * s) = 1 := by
    have h1 : a ^ (t * s) * b ^ (t * s) = 1 := by
      have : (a ^ t * b ^ t) ^ s = 1 ^ s := by rw [hab_eq]
      rw [mul_pow, ← pow_mul, ← pow_mul, one_pow] at this
      exact this
    have h2 : b ^ (t * s) = 1 := by
      rw [mul_comm, pow_mul, hbs, one_pow]
    rw [h2, mul_one] at h1
    exact h1
  have hrts : Nat.Coprime r (t * s) := Nat.Coprime.mul_right hrt hrs
  have ha : a = 1 := eq_one_of_pow_eq_one_of_coprime har hats hrts
  -- Symmetric for b
  have hbtr : b ^ (t * r) = 1 := by
    have h1 : a ^ (t * r) * b ^ (t * r) = 1 := by
      have : (a ^ t * b ^ t) ^ r = 1 ^ r := by rw [hab_eq]
      rw [mul_pow, ← pow_mul, ← pow_mul, one_pow] at this
      exact this
    have h2 : a ^ (t * r) = 1 := by
      rw [mul_comm, pow_mul, har, one_pow]
    rw [h2, one_mul] at h1
    exact h1
  have hstr : Nat.Coprime s (t * r) := Nat.Coprime.mul_right hst hrs.symm
  have hb : b = 1 := eq_one_of_pow_eq_one_of_coprime hbs hbtr hstr
  exact ⟨ha, hb⟩

end Imc2001P2
