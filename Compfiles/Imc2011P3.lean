/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory, .Algebra] }

/-!
# International Mathematical Competition 2011, Problem 3

Let `p` be a prime number. Call a positive integer `n` *interesting* if
`x^n - 1 = (x^p - x + 1) f(x) + p g(x)`
for some polynomials `f` and `g` with integer coefficients.

(a) Prove that `p^p - 1` is interesting.
(b) For which `p` is `p^p - 1` the minimal interesting number?

Answer: `p ∈ {2, 3}`.

## Solution sketch

Reformulate: `n` is interesting iff `x^n - 1` is divisible by `x^p - x + 1`
in `𝔽_p[x]`. Working modulo `x^p - x + 1` in `𝔽_p[x]`:

(a) `x^p ≡ x - 1`, so `x^(p^k) ≡ x - k`, hence `x^(p^p) ≡ x`. Since
`gcd(x^p - x + 1, x) = 1`, we get `x^(p^p - 1) ≡ 1`.

(b) If `p > 3`, then `2(1 + p + … + p^(p-1)) = 2(p^p - 1)/(p - 1)` is also
interesting and strictly less than `p^p - 1`. For `p = 2, 3` one checks
divisors of `p^p - 1` directly.
-/

namespace Imc2011P3

open Polynomial

/-- A positive integer `n` is *interesting* (with respect to a prime `p`) if
`x^n - 1 = (x^p - x + 1) f(x) + p g(x)` for some `f, g ∈ ℤ[x]`. -/
def Interesting (p n : ℕ) : Prop :=
  ∃ f g : ℤ[X], (X : ℤ[X])^n - 1 = (X^p - X + 1) * f + (p : ℤ[X]) * g

snip begin

/-- If `n` is interesting, then in `(ZMod p)[X]`, `(X^p - X + 1)` divides `X^n - 1`. -/
lemma interesting_imp_dvd_zmod {p n : ℕ} [Fact p.Prime] (h : Interesting p n) :
    ((X : (ZMod p)[X])^p - X + 1) ∣ ((X : (ZMod p)[X])^n - 1) := by
  obtain ⟨f, g, hfg⟩ := h
  have hfg' := congrArg (Polynomial.map (Int.castRingHom (ZMod p))) hfg
  simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
             Polynomial.map_X, Polynomial.map_one, Polynomial.map_natCast] at hfg'
  have hp_zero : ((p : ℕ) : (ZMod p)[X]) = 0 := by
    rw [show ((p : ℕ) : (ZMod p)[X]) = C ((p : ℕ) : (ZMod p)) from rfl,
        ZMod.natCast_self, C_0]
  rw [hp_zero, zero_mul, add_zero] at hfg'
  exact ⟨f.map (Int.castRingHom (ZMod p)), hfg'⟩

/-- Conversely, divisibility in `(ZMod p)[X]` implies `n` is interesting. -/
lemma dvd_zmod_imp_interesting {p n : ℕ} [hp : Fact p.Prime]
    (h : ((X : (ZMod p)[X])^p - X + 1) ∣ ((X : (ZMod p)[X])^n - 1)) :
    Interesting p n := by
  obtain ⟨q, hq⟩ := h
  -- Lift q to ℤ[X].
  have hsurj : Function.Surjective (Int.castRingHom (ZMod p)) := by
    intro a
    refine ⟨(a.val : ℤ), ?_⟩
    simp [Int.castRingHom]
  obtain ⟨q', hq'⟩ := Polynomial.map_surjective (Int.castRingHom (ZMod p)) hsurj q
  -- Define h := X^n - 1 - (X^p - X + 1) * q' ∈ ℤ[X], then map to ZMod p is 0.
  set h : ℤ[X] := (X : ℤ[X])^n - 1 - (X^p - X + 1) * q' with hh
  have hmap_zero : h.map (Int.castRingHom (ZMod p)) = 0 := by
    simp only [h, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_add,
               Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
    rw [hq']
    rw [hq]
    ring
  -- Since map sends h to 0, every coeff of h is divisible by p.
  -- Hence h = p * g for some g ∈ ℤ[X].
  have : ∀ k, (p : ℤ) ∣ h.coeff k := by
    intro k
    have hk : (h.coeff k : ZMod p) = 0 := by
      have := congrArg (fun r => r.coeff k) hmap_zero
      simp [Polynomial.coeff_map, Int.castRingHom] at this
      exact this
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hk
  -- Choose g coefficient-wise.
  -- Define g via its coefficients: g.coeff k = h.coeff k / p
  classical
  let g : ℤ[X] := ∑ k ∈ h.support, Polynomial.monomial k (h.coeff k / p)
  have hp_ne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hg_coeff : ∀ k, g.coeff k = h.coeff k / p := by
    intro k
    simp only [g, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
    by_cases hk : k ∈ h.support
    · rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hbk
        rw [if_neg hbk]
      · intro hk'
        exact absurd hk hk'
    · rw [Finset.sum_eq_zero]
      · rw [Polynomial.notMem_support_iff.mp hk]
        simp
      · intro b hb
        rw [if_neg]
        rintro rfl
        exact hk hb
  refine ⟨q', g, ?_⟩
  apply Polynomial.ext
  intro k
  have hk_div : (p : ℤ) ∣ h.coeff k := this k
  obtain ⟨m, hm⟩ := hk_div
  have hg_k : g.coeff k = m := by
    rw [hg_coeff k, hm]
    exact Int.mul_ediv_cancel_left m hp_ne
  -- Goal: (X^n - 1).coeff k = ((X^p - X + 1) * q' + (p : ℤ[X]) * g).coeff k
  -- We have h.coeff k = (X^n - 1).coeff k - ((X^p - X + 1) * q').coeff k = p * m
  -- and (p : ℤ[X]) * g has coeff k = p * g.coeff k = p * m.
  show ((X : ℤ[X])^n - 1).coeff k = ((X^p - X + 1) * q' + (p : ℤ[X]) * g).coeff k
  rw [Polynomial.coeff_add]
  have h_coeff_k : h.coeff k = ((X : ℤ[X])^n - 1).coeff k - ((X^p - X + 1) * q').coeff k := by
    show (((X : ℤ[X])^n - 1) - (X^p - X + 1) * q').coeff k = _
    rw [Polynomial.coeff_sub]
  have hpg_coeff : (((p : ℤ[X])) * g).coeff k = (p : ℤ) * g.coeff k := by
    rw [show ((p : ℕ) : ℤ[X]) = C ((p : ℕ) : ℤ) from rfl,
        Polynomial.coeff_C_mul]
  rw [hpg_coeff, hg_k, ← hm]
  linarith [h_coeff_k]

/-- `n` is interesting iff `(X^p - X + 1) ∣ (X^n - 1)` in `(ZMod p)[X]`. -/
lemma interesting_iff_dvd_zmod (p n : ℕ) [Fact p.Prime] :
    Interesting p n ↔
    ((X : (ZMod p)[X])^p - X + 1) ∣ ((X : (ZMod p)[X])^n - 1) :=
  ⟨interesting_imp_dvd_zmod, dvd_zmod_imp_interesting⟩

/-- For prime `p`, `(X^p - X + 1) ∣ X^(p^k) - X + k` in `(ZMod p)[X]`. -/
lemma dvd_X_pow_p_pow_sub {p : ℕ} [hp : Fact p.Prime] (k : ℕ) :
    ((X : (ZMod p)[X])^p - X + 1) ∣
    ((X : (ZMod p)[X])^(p^k) - X + ((k : ℕ) : (ZMod p)[X])) := by
  haveI : CharP ((ZMod p)[X]) p := Polynomial.charP
  induction k with
  | zero => simp
  | succ k ih =>
    set Q : (ZMod p)[X] := X^p - X + 1 with hQ
    -- (k : (ZMod p)[X])^p = k, since (k : ZMod p)^p = (k : ZMod p) (Fermat).
    have hk_pth : (((k : ℕ) : (ZMod p)[X]))^p = ((k : ℕ) : (ZMod p)[X]) := by
      rw [show (((k : ℕ) : (ZMod p)[X])) = C ((k : ℕ) : (ZMod p)) from rfl]
      rw [← C_pow]
      congr 1
      exact ZMod.pow_card _
    -- Set u := X^(p^k) - X + k.
    set u : (ZMod p)[X] := X^(p^k) - X + ((k : ℕ) : (ZMod p)[X]) with hu
    -- ih : Q ∣ u
    -- Q ∣ u^p, so Q ∣ X^(p^(k+1)) - (X-k)^p when expanded.
    have h_up : Q ∣ u^p := by
      have hp_ne : p ≠ 0 := hp.out.ne_zero
      exact ih.pow hp_ne
    -- u^p = (X^(p^k))^p - 2*(...) ... actually we need a cleaner identity.
    -- Frobenius (char p): u^p = (X^(p^k))^p - X^p + k^p = X^(p^(k+1)) - X^p + k.
    have hu_pow : u^p = (X : (ZMod p)[X])^(p^(k+1)) - X^p + ((k : ℕ) : (ZMod p)[X]) := by
      rw [hu]
      -- (a - b + c)^p in char p
      have : ((X : (ZMod p)[X])^(p^k) - X + ((k : ℕ) : (ZMod p)[X]))^p =
             ((X : (ZMod p)[X])^(p^k))^p - X^p + (((k : ℕ) : (ZMod p)[X]))^p := by
        have e1 : ((X : (ZMod p)[X])^(p^k) - X + ((k : ℕ) : (ZMod p)[X])) =
                  ((X : (ZMod p)[X])^(p^k) - X) + ((k : ℕ) : (ZMod p)[X]) := by ring
        rw [e1, add_pow_char]
        rw [sub_pow_char]
      rw [this, hk_pth]
      rw [show ((X : (ZMod p)[X])^(p^k))^p = X^(p^(k+1)) from by
        rw [← pow_mul, ← pow_succ]]
    -- Now: target = u^p + Q.
    -- target := X^(p^(k+1)) - X + (k+1)
    --        = (X^(p^(k+1)) - X^p + k) + (X^p - X + 1)
    --        = u^p + Q.
    have hgoal_eq :
        (X : (ZMod p)[X])^(p^(k+1)) - X + ((k+1 : ℕ) : (ZMod p)[X]) = u^p + Q := by
      rw [hu_pow]
      push_cast
      ring
    rw [hgoal_eq]
    exact dvd_add h_up (dvd_refl _)

/-- The polynomial `X^p - X + 1` is coprime to `X` in `(ZMod p)[X]`. -/
lemma isCoprime_X_pow_sub_X_add_one_X (p : ℕ) [hp : Fact p.Prime] (hp2 : 1 ≤ p) :
    IsCoprime (X : (ZMod p)[X]) ((X : (ZMod p)[X])^p - X + 1) := by
  refine ⟨-(X : (ZMod p)[X])^(p - 1) + 1, 1, ?_⟩
  have hp_pred : (X : (ZMod p)[X])^(p - 1) * X = X^p := by
    rw [← pow_succ, Nat.sub_add_cancel hp2]
  linear_combination (-1 : (ZMod p)[X]) * hp_pred

snip end

/-- The set of primes `p` for which `p^p - 1` is the minimal interesting number. -/
determine answer : Set ℕ := {2, 3}

problem imc2011_p3_a (p : ℕ) (hp : p.Prime) :
    Interesting p (p^p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [interesting_iff_dvd_zmod]
  -- We want: Q := X^p - X + 1 divides X^(p^p - 1) - 1.
  -- Step 1: Q ∣ X^(p^p) - X + p = X^(p^p) - X (since p = 0 in ZMod p).
  have h1 : ((X : (ZMod p)[X])^p - X + 1) ∣
            ((X : (ZMod p)[X])^(p^p) - X + ((p : ℕ) : (ZMod p)[X])) :=
    dvd_X_pow_p_pow_sub p
  have hp_zero : ((p : ℕ) : (ZMod p)[X]) = 0 := by
    rw [show ((p : ℕ) : (ZMod p)[X]) = C ((p : ℕ) : (ZMod p)) from rfl,
        ZMod.natCast_self, C_0]
  rw [hp_zero, add_zero] at h1
  -- Step 2: X^(p^p) - X = X * (X^(p^p - 1) - 1), assuming p^p ≥ 1.
  have hpp_pos : 1 ≤ p^p := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne_zero)
  have h_factor : (X : (ZMod p)[X])^(p^p) - X = X * (X^(p^p - 1) - 1) := by
    have hXmul : (X : (ZMod p)[X]) * X^(p^p - 1) = X^(p^p) := by
      rw [← pow_succ']
      congr 1
      omega
    linear_combination -hXmul
  rw [h_factor] at h1
  -- Step 3: Q is coprime to X.
  have hcop : IsCoprime (X : (ZMod p)[X]) ((X : (ZMod p)[X])^p - X + 1) :=
    isCoprime_X_pow_sub_X_add_one_X p hp.one_lt.le
  -- From Q ∣ X * (...) and gcd(Q, X) = 1, get Q ∣ (...).
  exact hcop.symm.dvd_of_dvd_mul_left h1

problem imc2011_p3_b (p : ℕ) (hp : p.Prime) :
    p ∈ answer ↔
    (Interesting p (p^p - 1) ∧
     ∀ n, 0 < n → n < p^p - 1 → ¬ Interesting p n) := by
  sorry

end Imc2011P3
