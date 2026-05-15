/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Competition 2012, Problem 8 (Day 2, Problem 3)

Is the set of positive integers `n` such that `n! + 1` divides `(2012 n)!`
finite or infinite?

Answer: finite.

Sketch: If `n! + 1 ∣ (2012 n)!`, then since `(n!)^2012 ∣ (2012 n)!` (the
multinomial / `prod_factorial_dvd_factorial_sum`) and `gcd(n!+1, n!) = 1`,
we get `(n!+1) · (n!)^2012 ∣ (2012 n)!`. Hence `(n!)^2013 < (2012 n)!`.
But `(n!)^2013` eventually exceeds `(2012 n)!`, so only finitely many `n`
can satisfy the divisibility.
-/

namespace Imc2012P8

set_option exponentiation.threshold 5000000

open Nat

/-- The set of positive integers `n` for which `n! + 1` divides `(2012 n)!`. -/
def S : Set ℕ := {n : ℕ | n.factorial + 1 ∣ (2012 * n).factorial}

determine answer : Prop := S.Finite

-- snip begin

/-- The constant function `n` on `Finset.range 2012`. -/
private def f (n : ℕ) : Fin 2012 → ℕ := fun _ => n

private lemma sum_f (n : ℕ) :
    ∑ _i : Fin 2012, n = 2012 * n := by
  simp [Finset.sum_const, Finset.card_univ, mul_comm]

private lemma prod_f (n : ℕ) :
    ∏ _i : Fin 2012, n.factorial = n.factorial ^ 2012 := by
  simp [Finset.prod_const, Finset.card_univ]

/-- `(n!)^2012 ∣ (2012 n)!`. -/
lemma pow_factorial_dvd (n : ℕ) :
    n.factorial ^ 2012 ∣ (2012 * n).factorial := by
  have h := Nat.prod_factorial_dvd_factorial_sum (Finset.univ : Finset (Fin 2012))
    (fun _ => n)
  simpa [prod_f, sum_f] using h

/-- `n! + 1` and `n!` are coprime. -/
lemma coprime_factorial_succ (n : ℕ) : Nat.Coprime (n.factorial + 1) n.factorial := by
  -- gcd(n!+1, n!) divides (n!+1) - n! = 1
  show Nat.gcd (n.factorial + 1) n.factorial = 1
  rw [Nat.gcd_comm]
  -- gcd(n!, n!+1) = gcd(n!, 1) = 1
  have : Nat.gcd n.factorial (n.factorial + 1) = Nat.gcd n.factorial 1 := by
    conv_lhs => rw [show n.factorial + 1 = 1 + n.factorial from by ring]
    rw [Nat.gcd_add_self_right]
  rw [this]
  exact Nat.gcd_one_right _

/-- `n! + 1` and `(n!)^2012` are coprime. -/
lemma coprime_pow (n : ℕ) :
    Nat.Coprime (n.factorial + 1) (n.factorial ^ 2012) :=
  (coprime_factorial_succ n).pow_right 2012

/-- If `n! + 1 ∣ (2012 n)!`, then `(n!+1)·(n!)^2012 ∣ (2012 n)!`. -/
lemma combined_dvd {n : ℕ} (hn : n.factorial + 1 ∣ (2012 * n).factorial) :
    (n.factorial + 1) * n.factorial ^ 2012 ∣ (2012 * n).factorial :=
  (coprime_pow n).mul_dvd_of_dvd_of_dvd hn (pow_factorial_dvd n)

/-- Hence `(n!)^2013 < (2012 n)!` for any `n` in `S`. -/
lemma pow_2013_lt {n : ℕ} (hn : n.factorial + 1 ∣ (2012 * n).factorial) :
    n.factorial ^ 2013 < (2012 * n).factorial := by
  have hcomb := combined_dvd hn
  -- `(n!+1)*(n!)^2012` divides `(2012 n)!`, so it's ≤ it.
  have hpos : 0 < (2012 * n).factorial := Nat.factorial_pos _
  have hle : (n.factorial + 1) * n.factorial ^ 2012 ≤ (2012 * n).factorial :=
    Nat.le_of_dvd hpos hcomb
  -- And `(n!)^2013 = n! * (n!)^2012 < (n!+1) * (n!)^2012`.
  have hpow_pos : 0 < n.factorial ^ 2012 := pow_pos (Nat.factorial_pos _) _
  have hlt : n.factorial * n.factorial ^ 2012 < (n.factorial + 1) * n.factorial ^ 2012 := by
    exact (Nat.mul_lt_mul_right hpow_pos).mpr (Nat.lt_succ_self _)
  calc n.factorial ^ 2013
      = n.factorial * n.factorial ^ 2012 := by ring
    _ < (n.factorial + 1) * n.factorial ^ 2012 := hlt
    _ ≤ (2012 * n).factorial := hle

/-- Iteratively bound `(k n)! ≤ 2^(c k * n) * (n!)^k` for some constant `c k`.
Specifically, by repeatedly using `Nat.choose_le_two_pow`, we get that
`(k n)! ≤ 2^((k(k+1)/2 - 1) * n) * (n!)^k`.

We just need *existence* of such a bound for `k = 2012`. -/
lemma factorial_mul_le (n : ℕ) :
    ∀ k : ℕ, (k * n).factorial ≤ 2 ^ (k * (k + 1) * n) * n.factorial ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    -- ((k+1)n)! = choose ((k+1)n) n * (k n)! * n!
    have hchoose : ((k + 1) * n).factorial =
        Nat.choose ((k + 1) * n) n * (k * n).factorial * n.factorial := by
      have key := Nat.add_choose_mul_factorial_mul_factorial (k * n) n
      rw [show (k + 1) * n = k * n + n from by ring]
      linarith [key]
    rw [hchoose]
    -- Bound choose ≤ 2^((k+1)n)
    have hch : Nat.choose ((k + 1) * n) n ≤ 2 ^ ((k + 1) * n) := Nat.choose_le_two_pow _ _
    calc Nat.choose ((k + 1) * n) n * (k * n).factorial * n.factorial
        ≤ 2 ^ ((k + 1) * n) * (k * n).factorial * n.factorial := by
          gcongr
      _ ≤ 2 ^ ((k + 1) * n) * (2 ^ (k * (k + 1) * n) * n.factorial ^ k) * n.factorial := by
          gcongr
      _ = 2 ^ ((k + 1) * n + k * (k + 1) * n) * n.factorial ^ (k + 1) := by
          rw [pow_succ, pow_add]
          ring
      _ ≤ 2 ^ ((k + 1) * (k + 2) * n) * n.factorial ^ (k + 1) := by
          apply Nat.mul_le_mul_right
          apply Nat.pow_le_pow_right (by norm_num : 1 ≤ 2)
          have heq : (k + 1) * n + k * (k + 1) * n = (k + 1) * (k + 1) * n := by ring
          rw [heq]
          have h1 : (k + 1) * (k + 1) ≤ (k + 1) * (k + 2) :=
            Nat.mul_le_mul_left _ (by omega)
          exact Nat.mul_le_mul_right _ h1

/-- Specialization: `(2012 n)! ≤ 2^(C·n) · (n!)^2012` for `C = 2012·2013`. -/
lemma factorial_2012_mul_le (n : ℕ) :
    (2012 * n).factorial ≤ 2 ^ (2012 * 2013 * n) * n.factorial ^ 2012 :=
  factorial_mul_le n 2012

/-- If `n ∈ S`, then `n! ≤ 2^(2012·2013·n)`. -/
lemma factorial_le_pow_of_mem {n : ℕ} (hn : n.factorial + 1 ∣ (2012 * n).factorial) :
    n.factorial < 2 ^ (2012 * 2013 * n) + 1 := by
  -- (n!+1)(n!)^2012 ≤ (2012n)! ≤ 2^(2012*2013*n) (n!)^2012
  -- Divide both sides by (n!)^2012:  n! + 1 ≤ 2^(2012*2013*n).
  have h1 : (n.factorial + 1) * n.factorial ^ 2012 ≤ (2012 * n).factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _) (combined_dvd hn)
  have h2 : (2012 * n).factorial ≤ 2 ^ (2012 * 2013 * n) * n.factorial ^ 2012 :=
    factorial_2012_mul_le n
  have h3 : (n.factorial + 1) * n.factorial ^ 2012 ≤
            2 ^ (2012 * 2013 * n) * n.factorial ^ 2012 := h1.trans h2
  have hpos : 0 < n.factorial ^ 2012 := pow_pos (Nat.factorial_pos _) _
  have h4 : n.factorial + 1 ≤ 2 ^ (2012 * 2013 * n) := by
    exact Nat.le_of_mul_le_mul_right h3 hpos
  omega

/-- Existence of `N` such that for `n ≥ N`, `2^(2012·2013·n) < n!`. -/
lemma exists_pow_lt_factorial :
    ∃ N : ℕ, ∀ n ≥ N, 2 ^ (2012 * 2013 * n) + 1 ≤ n.factorial := by
  -- Use `tendsto_pow_div_factorial_atTop`: `a^n/n! → 0`.
  -- So eventually `2 * a^n ≤ n!`, where `a = 2^(2012*2013)`.
  have h := FloorSemiring.tendsto_pow_div_factorial_atTop
    ((2 : ℝ) ^ (2012 * 2013))
  -- Since this tends to 0, eventually < 1/2.
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN_lt⟩ := h (1 / 2) (by norm_num)
  refine ⟨N + 1, ?_⟩
  intro n hn
  have hnN : N ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hfact_pos : 0 < n.factorial := Nat.factorial_pos _
  have hreal_dist := hN_lt n hnN
  -- |x - 0| < 1/2 means x < 1/2 (and x > -1/2)
  have hreal : ((2 : ℝ) ^ (2012 * 2013)) ^ n / n.factorial < 1 / 2 := by
    have hd : |((2 : ℝ) ^ (2012 * 2013)) ^ n / n.factorial - 0| < 1 / 2 := by
      have := hreal_dist
      rw [Real.dist_eq] at this
      exact this
    have := abs_lt.mp hd
    linarith [this.2]
  -- So a^n < n!/2, hence 2 a^n < n!, hence 2 a^n + 1 ≤ n!. But we want a^n + 1 ≤ n!.
  -- Actually 2 a^n + 1 > a^n + 1, but only need a^n + 1 ≤ n! which follows.
  have hreal' : ((2 : ℝ) ^ (2012 * 2013)) ^ n < (n.factorial : ℝ) / 2 := by
    have hfp : (0 : ℝ) < n.factorial := by exact_mod_cast hfact_pos
    have hlt2 : ((2 : ℝ) ^ (2012 * 2013)) ^ n / n.factorial < 1 / 2 := hreal
    rw [div_lt_iff₀ hfp] at hlt2
    -- hlt2 : (2^(2012*2013))^n < 1/2 * n!
    -- want: (2^(2012*2013))^n < n! / 2
    have : (1 / 2 : ℝ) * n.factorial = (n.factorial : ℝ) / 2 := by ring
    linarith [this]
  -- 2 * 2^(2012*2013*n) ≤ n!  in ℝ, hence in ℕ
  have hkey : 2 * 2 ^ (2012 * 2013 * n) ≤ n.factorial := by
    have heq : ((2 : ℝ) ^ (2012 * 2013)) ^ n = (2 : ℝ) ^ (2012 * 2013 * n) := by
      rw [← pow_mul]
    rw [heq] at hreal'
    have hfp : (0 : ℝ) < n.factorial := by exact_mod_cast hfact_pos
    have hreal'' : 2 * (2 : ℝ) ^ (2012 * 2013 * n) ≤ n.factorial := by linarith
    have hcast : ((2 * 2 ^ (2012 * 2013 * n) : ℕ) : ℝ) ≤ (n.factorial : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hcast
  -- 2 * a^n = a^n + a^n ≥ a^n + 1 since a^n ≥ 1
  have hpow_ge_one : 1 ≤ 2 ^ (2012 * 2013 * n) := Nat.one_le_two_pow
  omega

/-- The set `S` of positive integers `n` with `n!+1 ∣ (2012 n)!` is finite. -/
lemma S_finite : S.Finite := by
  obtain ⟨N, hN⟩ := exists_pow_lt_factorial
  apply Set.Finite.subset (Set.finite_Iio N)
  intro n hn
  by_contra hge
  rw [Set.mem_Iio] at hge
  have hge' : N ≤ n := Nat.le_of_not_lt hge
  have h1 : n.factorial < 2 ^ (2012 * 2013 * n) + 1 := factorial_le_pow_of_mem hn
  have h2 : 2 ^ (2012 * 2013 * n) + 1 ≤ n.factorial := hN n hge'
  exact absurd (Nat.lt_of_lt_of_le h1 h2) (lt_irrefl _)

-- snip end

problem imc2012_p8 : answer := S_finite

end Imc2012P8
