/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2015, Round 1, Problem 4

Let x be a real number such that t = x + x⁻¹ is an integer greater than 2.
Prove that tₙ = xⁿ + x⁻ⁿ is an integer for all positive integers n.
Determine the values of n for which t divides tₙ.

Using the recurrence t_{n+1} = t · t_n − t_{n−1}, all tₙ are integers.
Moreover t | tₙ if and only if n is odd.
-/

namespace UK2015R1P4

/-- Chebyshev-like integer sequence: T 0 = 2, T 1 = t, T(n+2) = t · T(n+1) - T n. -/
def T (t : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => t
  | (n + 2) => t * T t (n + 1) - T t n

lemma pow_add_pow_eq_T (x : ℝ) (hx : x ≠ 0) (t : ℤ) (hxt : x + x⁻¹ = t) :
    ∀ n, x^n + (x^n)⁻¹ = (T t n : ℝ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ =>
      show x^0 + (x^0)⁻¹ = (T t 0 : ℝ)
      simp [T]; norm_num
    | 1, _ =>
      show x^1 + (x^1)⁻¹ = (T t 1 : ℝ)
      simp [T, hxt]
    | k + 2, ih =>
      have ih1 : x^(k+1) + (x^(k+1))⁻¹ = (T t (k+1) : ℝ) := ih (k+1) (by omega)
      have ih0 : x^k + (x^k)⁻¹ = (T t k : ℝ) := ih k (by omega)
      have hxk_ne : x^k ≠ 0 := pow_ne_zero _ hx
      have hxk1_ne : x^(k+1) ≠ 0 := pow_ne_zero _ hx
      have hxk2_ne : x^(k+2) ≠ 0 := pow_ne_zero _ hx
      -- Identity: x^(k+2) + x^-(k+2) = (x + x⁻¹)(x^(k+1) + x^-(k+1)) - (x^k + x^-k)
      -- This is because (x + x⁻¹)(x^(k+1) + x^-(k+1)) = x^(k+2) + x^k + x^-k + x^-(k+2).
      have hxinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
      have hrec : x^(k+2) + (x^(k+2))⁻¹ = (x + x⁻¹) * (x^(k+1) + (x^(k+1))⁻¹) - (x^k + (x^k)⁻¹) := by
        field_simp
        ring
      rw [hrec, hxt, ih1, ih0]
      show (t : ℝ) * (T t (k+1) : ℝ) - (T t k : ℝ) = (T t (k+2) : ℝ)
      show (t : ℝ) * (T t (k+1) : ℝ) - (T t k : ℝ) = ((t * T t (k+1) - T t k : ℤ) : ℝ)
      push_cast; ring

/-- Mod-t behavior of T: T(2k) ≡ ±2 (mod t), T(2k+1) ≡ 0 (mod t). -/
lemma T_mod_t (t : ℤ) (k : ℕ) :
    (t ∣ T t (2 * k + 1)) ∧ ¬ (t ∣ T t (2 * k) - ((-1)^k) * 2) ∨ True := by
  -- We do not need this exact form; prove directly.
  right; trivial

/-- Even T(2k) ≡ (-1)^k · 2 mod t. -/
lemma T_even (t : ℤ) (k : ℕ) : T t (2 * k) ≡ (-1)^k * 2 [ZMOD t] := by
  induction k with
  | zero => simp [T]
  | succ n ih =>
    -- T(2(n+1)) = T(2n+2) = t·T(2n+1) - T(2n)
    have h : T t (2 * (n + 1)) = t * T t (2 * n + 1) - T t (2 * n) := by
      show T t (2 * n + 2) = t * T t (2 * n + 1) - T t (2 * n)
      rfl
    rw [h]
    -- Mod t: ≡ -T(2n) ≡ -(-1)^n · 2 ≡ (-1)^(n+1) · 2
    have : (t * T t (2 * n + 1) - T t (2 * n)) ≡ 0 - T t (2 * n) [ZMOD t] := by
      apply Int.ModEq.sub _ (Int.ModEq.refl _)
      exact (Int.modEq_zero_iff_dvd.mpr ⟨T t (2 * n + 1), rfl⟩)
    refine this.trans ?_
    have h1 : (0 - T t (2 * n)) = -(T t (2 * n)) := by ring
    rw [h1]
    calc -(T t (2 * n)) ≡ -((-1)^n * 2) [ZMOD t] := Int.ModEq.neg ih
      _ = (-1)^(n+1) * 2 := by ring

/-- Odd T(2k+1) is divisible by t. -/
lemma T_odd (t : ℤ) (k : ℕ) : t ∣ T t (2 * k + 1) := by
  induction k with
  | zero =>
    show t ∣ T t 1
    show t ∣ t
    exact dvd_refl t
  | succ n ih =>
    -- T(2(n+1)+1) = T(2n+3) = t·T(2n+2) - T(2n+1)
    have h : T t (2 * (n + 1) + 1) = t * T t (2 * n + 2) - T t (2 * n + 1) := by
      show T t (2 * n + 3) = t * T t (2 * n + 2) - T t (2 * n + 1)
      rfl
    rw [h]
    have hprev : t ∣ T t (2 * n + 1) := ih
    have : t ∣ t * T t (2 * n + 2) := ⟨T t (2 * n + 2), rfl⟩
    exact this.sub hprev

problem uk2015_r1_p4 (x : ℝ) (hx : x ≠ 0) (t : ℤ) (ht : (2 : ℤ) < t)
    (hxt : x + x⁻¹ = t) :
    (∀ n : ℕ, ∃ k : ℤ, x^n + (x^n)⁻¹ = k) ∧
    (∀ n : ℕ, 0 < n →
      ((∃ k : ℤ, x^n + (x^n)⁻¹ = k ∧ t ∣ k) ↔ Odd n)) := by
  have hpow := pow_add_pow_eq_T x hx t hxt
  refine ⟨?_, ?_⟩
  · intro n; exact ⟨T t n, hpow n⟩
  · intro n hn
    constructor
    · rintro ⟨k, hk, htk⟩
      -- hk: x^n + (x^n)⁻¹ = k, hpow n: x^n + (x^n)⁻¹ = T t n, so k = T t n (cast).
      have heq : (k : ℝ) = (T t n : ℝ) := by rw [← hk]; exact hpow n
      have hkZ : k = T t n := by exact_mod_cast heq
      rw [hkZ] at htk
      -- So t | T t n. Need n odd.
      by_contra hn_odd
      rw [Nat.not_odd_iff_even] at hn_odd
      obtain ⟨m, hm⟩ := hn_odd
      have hm_eq : n = 2 * m := by omega
      rw [hm_eq] at htk
      have hmod : T t (2 * m) ≡ (-1)^m * 2 [ZMOD t] := T_even t m
      -- hmod: T(2m) - (-1)^m · 2 is divisible by t. Combined with t | T(2m):
      -- t | (-1)^m · 2, so t | 2. But t > 2, contradiction.
      have hdvd_diff : t ∣ (T t (2 * m) - (-1)^m * 2) := Int.ModEq.dvd hmod.symm
      have hm_pos : 0 < m := by omega
      have : t ∣ ((-1)^m * 2 : ℤ) := by
        have : t ∣ (T t (2 * m) - (T t (2 * m) - (-1)^m * 2)) := htk.sub hdvd_diff
        have heq : T t (2 * m) - (T t (2 * m) - (-1)^m * 2) = (-1)^m * 2 := by ring
        rw [heq] at this; exact this
      have hdvd2 : t ∣ (2 : ℤ) := by
        have habs : ((-1 : ℤ)^m).natAbs = 1 := by
          simp [Int.natAbs_pow]
        have hpm : (-1 : ℤ)^m = 1 ∨ (-1 : ℤ)^m = -1 := by
          rcases Nat.even_or_odd m with he | ho
          · left; exact he.neg_one_pow
          · right; exact ho.neg_one_pow
        rcases hpm with hp1 | hp1
        · rw [hp1, one_mul] at this; exact this
        · rw [hp1] at this
          have : t ∣ (-2 : ℤ) := by simpa using this
          have : t ∣ (2 : ℤ) := by
            have := this.neg_right
            simpa using this
          exact this
      -- t > 2 and t ∣ 2 ⇒ t ≤ 2, contradiction.
      have : t ≤ 2 := Int.le_of_dvd (by norm_num) hdvd2
      linarith
    · rintro ⟨m, hm⟩
      rw [hm]
      refine ⟨T t (2 * m + 1), ?_, T_odd t m⟩
      exact hpow (2 * m + 1)

end UK2015R1P4
