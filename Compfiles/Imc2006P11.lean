/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory, .Algebra] }

/-!
# International Mathematical Competition 2006, Problem 11

(Also listed as Day 2, Problem 5.)

Prove there are infinitely many coprime pairs `(m, n)` of positive integers
for which `(x + m)^3 = n * x` has three distinct integer roots.

## Proof sketch

For each integer `p ≥ 2`, take
* `m = p^2 + p = p(p+1)`,
* `n = (p^2 + p + 1)^3`.

Then `gcd(m, n) = 1` because `gcd(p(p+1), p(p+1) + 1) = 1`,
and the three distinct integer roots are `p^3`, `1` and `-(p+1)^3`.
-/

namespace Imc2006P11

snip begin

/-- The triple of integer roots of `(x + m)^3 = n*x` for the construction with parameter `p`. -/
def roots (p : ℤ) : Finset ℤ := {p^3, 1, -(p+1)^3}

lemma roots_distinct {p : ℤ} (hp : 2 ≤ p) : (roots p).card = 3 := by
  have hp3 : (8 : ℤ) ≤ p^3 := by nlinarith [sq_nonneg p, sq_nonneg (p - 2)]
  have hpp3 : (27 : ℤ) ≤ (p+1)^3 := by nlinarith [sq_nonneg (p + 1), sq_nonneg (p - 2)]
  have h1 : p^3 ≠ 1 := by intro h; linarith
  have h2 : p^3 ≠ -(p+1)^3 := by intro h; linarith
  have h3 : (1 : ℤ) ≠ -(p+1)^3 := by intro h; linarith
  simp [roots, Finset.card_insert_of_notMem, h1, h2, h3]

/-- The polynomial identity: `(x + m)^3 - n*x = (x - p^3)(x - 1)(x + (p+1)^3)`
where `m = p(p+1)` and `n = (p^2 + p + 1)^3`. -/
lemma poly_identity (p x : ℤ) :
    (x + (p^2 + p))^3 - (p^2 + p + 1)^3 * x =
      (x - p^3) * (x - 1) * (x - (-(p+1)^3)) := by
  ring

lemma is_root (p x : ℤ) (hx : x ∈ roots p) :
    (x + (p^2 + p))^3 = (p^2 + p + 1)^3 * x := by
  have h := poly_identity p x
  simp [roots] at hx
  rcases hx with hx | hx | hx
  · subst hx; linarith [h]
  · subst hx; linarith [h]
  · subst hx; linarith [h]

/-- Coprimality: `gcd(p(p+1), (p^2+p+1)^3) = 1`. -/
lemma coprime_mn (p : ℕ) :
    Nat.Coprime (p^2 + p) ((p^2 + p + 1)^3) := by
  have h : Nat.Coprime (p^2 + p) (p^2 + p + 1) := by
    rw [Nat.coprime_self_add_right]
    exact Nat.coprime_one_right _
  exact h.pow_right 3

/-- For `p ≥ 2`, the `m` value is positive. -/
lemma m_pos {p : ℕ} (hp : 2 ≤ p) : 0 < p^2 + p := by
  have : 0 < p := by omega
  positivity

/-- The `n` value is always positive. -/
lemma n_pos (p : ℕ) : 0 < (p^2 + p + 1)^3 := by positivity

/-- The size of the parameter `p` controls how big the resulting `m` is, so we get
infinitely many distinct pairs. -/
lemma m_ge (p : ℕ) : p ≤ p^2 + p := by nlinarith

snip end

/-- We say `(m, n)` is "good" if it is a pair of coprime positive integers such that
`(x + m)^3 = n * x` has three distinct integer roots. -/
def Good (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ Nat.Coprime m n ∧
    ∃ S : Finset ℤ, S.card = 3 ∧
      ∀ x ∈ S, (x + (m : ℤ))^3 = (n : ℤ) * x

problem imc2006_p11 :
    ∀ N : ℕ, ∃ m n : ℕ, m ≥ N ∧ Good m n := by
  intro N
  -- Choose p ≥ max 2 N. Then m = p^2 + p ≥ p ≥ N.
  refine ⟨(max 2 N)^2 + max 2 N, (max 2 N ^ 2 + max 2 N + 1)^3, ?_, ?_⟩
  · -- m ≥ N
    have h1 : N ≤ max 2 N := le_max_right _ _
    have h2 : max 2 N ≤ (max 2 N)^2 + max 2 N := Imc2006P11.m_ge _
    exact le_trans h1 h2
  · set p := max 2 N with hp_def
    have hp : 2 ≤ p := le_max_left _ _
    refine ⟨Imc2006P11.m_pos hp, Imc2006P11.n_pos p, Imc2006P11.coprime_mn p, ?_⟩
    refine ⟨Imc2006P11.roots (p : ℤ), ?_, ?_⟩
    · have : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
      exact Imc2006P11.roots_distinct this
    · intro x hx
      have hroot := Imc2006P11.is_root (p : ℤ) x hx
      -- We need to match `(x + (p^2 + p : ℕ))^3 = (p^2 + p + 1 : ℕ)^3 * x`
      -- vs the integer version `(x + ((p:ℤ)^2 + p))^3 = ((p:ℤ)^2 + p + 1)^3 * x`.
      push_cast
      ring_nf
      ring_nf at hroot
      linarith

end Imc2006P11
