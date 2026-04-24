/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2008, Problem 7
(IMC 2008, Day 2, Problem 1)

Let `n, k` be positive integers. Suppose that the polynomial
`X^(2k) - X^k + 1` divides `X^(2n) + X^n + 1` in `ℤ[X]`.
Prove that the polynomial `X^(2k) + X^k + 1` also divides
`X^(2n) + X^n + 1` in `ℤ[X]`.

## Proof sketch

Set `A(X) = X^(2k) - X^k + 1`, `B(X) = X^(2k) + X^k + 1`, `f(X) = X^(2n) + X^n + 1`.

Consider the primitive `6k`-th root of unity `ζ = exp(iπ/(3k))`. Then
`ζ^k = exp(iπ/3)` is a primitive `6`-th root of unity, satisfying
`(ζ^k)^2 - ζ^k + 1 = 0`, so `ζ` is a root of `A`. Since `A ∣ f` in `ℤ[X]`,
we get `f(ζ) = 0`. Writing `α = πn/(3k)`:
`f(ζ) = e^(2iα) + e^(iα) + 1 = e^(iα)(2 cos α + 1) = 0`.
Thus `cos(πn/(3k)) = -1/2`, so `πn/(3k) = ±2π/3 + 2πm` for some integer `m`,
giving `n ≡ ±2k (mod 6k)`.

In each of the two resulting cases, a direct polynomial computation shows
`B ∣ f`.
-/

namespace Imc2008P7

open Polynomial

snip begin

/-- The algebraic identity
`(X^{2k} - X^k + 1)(X^{2k} + X^k + 1) = X^{4k} + X^{2k} + 1`. -/
lemma A_mul_B (k : ℕ) :
    ((X : ℤ[X])^(2*k) - X^k + 1) * (X^(2*k) + X^k + 1) =
      X^(4*k) + X^(2*k) + 1 := by
  have hpow4 : (X : ℤ[X])^(2*k) * X^(2*k) = X^(4*k) := by
    rw [← pow_add]; congr 1; ring
  have hpow2 : (X : ℤ[X])^k * X^k = X^(2*k) := by
    rw [← pow_add]; congr 1; ring
  linear_combination hpow4 + hpow2

/-- `X^{2k} + X^k + 1` divides `X^{3k} - 1` in `ℤ[X]`. -/
lemma B_dvd_X3k_sub_one (k : ℕ) :
    ((X : ℤ[X])^(2*k) + X^k + 1) ∣ (X^(3*k) - 1) := by
  refine ⟨X^k - 1, ?_⟩
  have hp1 : (X : ℤ[X])^(3*k) = X^(2*k) * X^k := by
    rw [← pow_add]; congr 1; ring
  have hp2 : (X : ℤ[X])^(2*k) = X^k * X^k := by
    rw [← pow_add]; congr 1; ring
  linear_combination (X^k + 1) * hp2 - hp1

/-- `X^{2k} - X^k + 1` divides `X^{3k} + 1` in `ℤ[X]`. -/
lemma A_dvd_X3k_add_one (k : ℕ) :
    ((X : ℤ[X])^(2*k) - X^k + 1) ∣ (X^(3*k) + 1) := by
  refine ⟨X^k + 1, ?_⟩
  have hp1 : (X : ℤ[X])^(3*k) = X^(2*k) * X^k := by
    rw [← pow_add]; congr 1; ring
  have hp2 : (X : ℤ[X])^(2*k) = X^k * X^k := by
    rw [← pow_add]; congr 1; ring
  linear_combination (X^k + 1) * hp2 - hp1

/-- `X^m - 1` divides `X^(b + m*q) - X^b` in any commutative ring. -/
lemma Xm_sub_one_dvd_pow_sub_pow {R : Type*} [CommRing R] (m b q : ℕ) :
    ((X : R[X])^m - 1) ∣ (X^(b + m*q) - X^b) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have heq : (X : R[X])^(b + m * (q + 1)) - X^b =
        (X^(b + m * q) - X^b) + X^(b + m*q) * (X^m - 1) := by
      have : b + m * (q + 1) = (b + m * q) + m := by ring
      rw [this, pow_add]
      ring
    rw [heq]
    exact dvd_add ih (dvd_mul_left _ _)

/-- Main case helper: when `n = 2k + 6k*m`, show `B ∣ f`. -/
lemma B_dvd_f_case_a (n k m : ℕ) (hn : n = 2*k + 6*k*m) :
    ((X : ℤ[X])^(2*k) + X^k + 1) ∣ (X^(2*n) + X^n + 1) := by
  set B := (X : ℤ[X])^(2*k) + X^k + 1 with hB_def
  have hB3k : B ∣ (X : ℤ[X])^(3*k) - 1 := B_dvd_X3k_sub_one k
  -- 2n - k = 3k + 12km = 3k(1+4m). So X^(3k) - 1 divides X^(2n) - X^k.
  have h2nk : 2*n = k + 3*k*(1 + 4*m) := by rw [hn]; ring
  have h2ndvd : ((X : ℤ[X])^(3*k) - 1) ∣ (X^(2*n) - X^k) := by
    rw [show 2*n = k + 3*k*(1+4*m) from h2nk]
    exact Xm_sub_one_dvd_pow_sub_pow (R := ℤ) (3*k) k (1+4*m)
  have hB_2n : B ∣ (X : ℤ[X])^(2*n) - X^k := dvd_trans hB3k h2ndvd
  -- n - 2k = 6km = 3k(2m). So X^(3k) - 1 divides X^n - X^(2k).
  have hnk : n = 2*k + 3*k*(2*m) := by rw [hn]; ring
  have hndvd : ((X : ℤ[X])^(3*k) - 1) ∣ (X^n - X^(2*k)) := by
    rw [show n = 2*k + 3*k*(2*m) from hnk]
    exact Xm_sub_one_dvd_pow_sub_pow (R := ℤ) (3*k) (2*k) (2*m)
  have hB_n : B ∣ (X : ℤ[X])^n - X^(2*k) := dvd_trans hB3k hndvd
  have hsum : (X : ℤ[X])^(2*n) + X^n + 1 =
      ((X^(2*n) - X^k) + (X^n - X^(2*k))) + B := by
    rw [hB_def]; ring
  rw [hsum]
  exact dvd_add (dvd_add hB_2n hB_n) dvd_rfl

/-- Other case: when `n = 4k + 6k*m`, show `B ∣ f`. -/
lemma B_dvd_f_case_b (n k m : ℕ) (hn : n = 4*k + 6*k*m) :
    ((X : ℤ[X])^(2*k) + X^k + 1) ∣ (X^(2*n) + X^n + 1) := by
  set B := (X : ℤ[X])^(2*k) + X^k + 1 with hB_def
  have hB3k : B ∣ (X : ℤ[X])^(3*k) - 1 := B_dvd_X3k_sub_one k
  have hnk : n = k + 3*k*(1 + 2*m) := by rw [hn]; ring
  have h2nk : 2*n = 2*k + 3*k*(2 + 4*m) := by rw [hn]; ring
  have hndvd : ((X : ℤ[X])^(3*k) - 1) ∣ (X^n - X^k) := by
    rw [hnk]; exact Xm_sub_one_dvd_pow_sub_pow (R := ℤ) (3*k) k (1 + 2*m)
  have h2ndvd : ((X : ℤ[X])^(3*k) - 1) ∣ (X^(2*n) - X^(2*k)) := by
    rw [h2nk]; exact Xm_sub_one_dvd_pow_sub_pow (R := ℤ) (3*k) (2*k) (2 + 4*m)
  have hB_n : B ∣ (X : ℤ[X])^n - X^k := dvd_trans hB3k hndvd
  have hB_2n : B ∣ (X : ℤ[X])^(2*n) - X^(2*k) := dvd_trans hB3k h2ndvd
  have hsum : (X : ℤ[X])^(2*n) + X^n + 1 =
      ((X^(2*n) - X^(2*k)) + (X^n - X^k)) + B := by
    rw [hB_def]; ring
  rw [hsum]
  exact dvd_add (dvd_add hB_2n hB_n) dvd_rfl

/-- The number `ω = exp(iπ/3)` satisfies `ω^2 - ω + 1 = 0`, since `ω^3 = -1`. -/
lemma omega_poly_zero : (Complex.exp (Complex.I * Real.pi / 3))^2
    - Complex.exp (Complex.I * Real.pi / 3) + 1 = 0 := by
  set ω := Complex.exp (Complex.I * Real.pi / 3) with hω_def
  -- ω^3 = exp(iπ) = -1.
  have hω3 : ω^3 = -1 := by
    rw [hω_def, ← Complex.exp_nat_mul]
    rw [show (3 : ℕ) * (Complex.I * (Real.pi : ℂ) / 3) = Real.pi * Complex.I from by
      push_cast; ring]
    exact Complex.exp_pi_mul_I
  -- So ω^3 + 1 = 0, i.e., (ω + 1)(ω^2 - ω + 1) = 0.
  have hfactor : (ω + 1) * (ω^2 - ω + 1) = 0 := by
    have : (ω + 1) * (ω^2 - ω + 1) = ω^3 + 1 := by ring
    rw [this, hω3]; ring
  have hωp1 : ω + 1 ≠ 0 := by
    intro h
    -- If ω + 1 = 0, then ω = -1, so ω^2 = 1 and ω - 1 = -2.
    -- Use the real part: Re(ω) = cos(π/3) = 1/2, but Re(-1) = -1.
    have hω_eq : ω = -1 := by linear_combination h
    have hRe : ω.re = 1/2 := by
      rw [hω_def]
      rw [Complex.exp_re]
      have hrewrite : Complex.I * (Real.pi : ℂ) / 3 = ((Real.pi / 3 : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [hrewrite]
      simp [Real.cos_pi_div_three]
    rw [hω_eq] at hRe
    simp at hRe
    linarith
  rcases mul_eq_zero.mp hfactor with h | h
  · exact absurd h hωp1
  · linear_combination h

/-- Evaluating the divisibility in `ℂ`: if `A ∣ f` in `ℤ[X]`, then
`f(ζ) = 0` for `ζ = exp(iπ/(3k))`. -/
lemma f_eval_zero (n k : ℕ) (hk : 0 < k)
    (hdvd : ((X : ℤ[X])^(2*k) - X^k + 1) ∣ (X^(2*n) + X^n + 1)) :
    let ζ : ℂ := Complex.exp (Complex.I * Real.pi / (3 * k))
    ζ^(2*n) + ζ^n + 1 = 0 := by
  intro ζ
  -- Cast divisibility to ℂ[X].
  have hdvdC : ((X : ℂ[X])^(2*k) - X^k + 1) ∣ (X^(2*n) + X^n + 1) := by
    have := (Polynomial.map_dvd (Int.castRingHom ℂ)) hdvd
    simpa [Polynomial.map_pow, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_one,
      Polynomial.map_X] using this
  have hζk : ζ^k = Complex.exp (Complex.I * Real.pi / 3) := by
    show (Complex.exp (Complex.I * Real.pi / (3 * k)))^k =
         Complex.exp (Complex.I * Real.pi / 3)
    rw [← Complex.exp_nat_mul]
    congr 1
    have hk_ne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    field_simp
  -- ζ is a root of A.
  have hζ_A : ((X : ℂ[X])^(2*k) - X^k + 1).eval ζ = 0 := by
    simp only [eval_add, eval_sub, eval_pow, eval_X, eval_one]
    rw [show (2*k : ℕ) = k + k from by ring, pow_add, hζk]
    have := omega_poly_zero
    linear_combination this
  -- From A ∣ f and A(ζ) = 0, conclude f(ζ) = 0.
  obtain ⟨q, hq⟩ := hdvdC
  have hf_eval : ((X : ℂ[X])^(2*n) + X^n + 1).eval ζ = 0 := by
    rw [hq]
    simp only [eval_mul, hζ_A, zero_mul]
  simpa [eval_add, eval_pow, eval_X, eval_one] using hf_eval

/-- Helper: `ζ^(2n) + ζ^n + 1 = 0` for `ζ = exp(iπ/(3k))` implies `cos(πn/(3k)) = -1/2`. -/
lemma cos_val_of_eval_zero (n k : ℕ) (hk : 0 < k)
    (h : let ζ : ℂ := Complex.exp (Complex.I * Real.pi / (3 * k))
         ζ^(2*n) + ζ^n + 1 = 0) :
    Real.cos (Real.pi * n / (3 * k)) = -(1/2) := by
  simp only at h
  set α : ℝ := Real.pi * n / (3 * k) with hα_def
  have hk_ne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hζn : (Complex.exp (Complex.I * Real.pi / (3 * k)))^n = Complex.exp (Complex.I * α) := by
    rw [← Complex.exp_nat_mul, hα_def]
    congr 1
    push_cast
    field_simp
  have hζ2n : (Complex.exp (Complex.I * Real.pi / (3 * k)))^(2*n)
      = Complex.exp (Complex.I * (2*α)) := by
    rw [← Complex.exp_nat_mul, hα_def]
    congr 1
    push_cast
    field_simp
  rw [hζn, hζ2n] at h
  -- e^(2iα) + e^(iα) + 1 = e^(iα) * (2 cos α + 1).
  set u := Complex.exp (Complex.I * α) with hu_def
  have hu_ne : u ≠ 0 := Complex.exp_ne_zero _
  have hu_sq : Complex.exp (Complex.I * (2*α)) = u^2 := by
    rw [hu_def, show (Complex.I * (2*α) : ℂ) = Complex.I * α + Complex.I * α from by ring,
        Complex.exp_add]
    ring
  rw [hu_sq] at h
  -- Express cos α via complex exponentials.
  -- u + u⁻¹ = 2 cos α.
  have h1 : u = Complex.cos α + Complex.sin α * Complex.I := by
    rw [hu_def, show (Complex.I * α : ℂ) = α * Complex.I from by ring]
    exact Complex.exp_mul_I (α : ℂ)
  have h2 : u⁻¹ = Complex.cos α - Complex.sin α * Complex.I := by
    have hu_inv : u⁻¹ = Complex.exp (-(Complex.I * α)) := by rw [← Complex.exp_neg]
    rw [hu_inv, show (-(Complex.I * α) : ℂ) = -(α : ℂ) * Complex.I from by ring]
    rw [Complex.exp_mul_I]
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  have hcos_real : Complex.cos (α : ℂ) = (Real.cos α : ℂ) := by
    rw [← Complex.ofReal_cos]
  have hcos_formula : u + u⁻¹ = 2 * (Real.cos α : ℂ) := by
    rw [h2, ← hcos_real]
    rw [show u = Complex.cos α + Complex.sin α * Complex.I from h1]
    ring
  -- u * (u + 1 + u^{-1}) = u^2 + u + 1. So u^2 + u + 1 = 0 implies u + 1 + u^{-1} = 0.
  have hring : u * (u + 1 + u⁻¹) = u^2 + u + 1 := by field_simp
  rw [← hring] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd h1 hu_ne
  · -- h1 : u + 1 + u⁻¹ = 0.
    have huu : u + u⁻¹ = -1 := by linear_combination h1
    -- Combine with hcos_formula: 2 * cos α = -1 as ℂ.
    have : (2 * (Real.cos α : ℂ) : ℂ) = (-1 : ℂ) := by
      rw [← hcos_formula, huu]
    have hreal : 2 * Real.cos α = -1 := by exact_mod_cast this
    linarith

/-- The key step: from `A ∣ f`, derive that `n ≡ ±2k (mod 6k)`. -/
lemma n_mod_6k_of_A_dvd_f (n k : ℕ) (hk : 0 < k)
    (hdvd : ((X : ℤ[X])^(2*k) - X^k + 1) ∣ (X^(2*n) + X^n + 1)) :
    (∃ m : ℕ, n = 2*k + 6*k*m) ∨ (∃ m : ℕ, n = 4*k + 6*k*m) := by
  have hfeval := f_eval_zero n k hk hdvd
  have hcos := cos_val_of_eval_zero n k hk hfeval
  -- cos(πn/(3k)) = -1/2 = cos(2π/3).
  have hcos23 : Real.cos (2 * Real.pi / 3) = -(1/2) := by
    rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 from by ring]
    rw [Real.cos_pi_sub, Real.cos_pi_div_three]
  have hcos_eq : Real.cos (Real.pi * n / (3 * k)) = Real.cos (2 * Real.pi / 3) := by
    rw [hcos23, hcos]
  have hangle := Real.Angle.cos_eq_iff_coe_eq_or_eq_neg.mp hcos_eq
  rcases hangle with h1 | h1
  · -- (πn/(3k) : Angle) = (2π/3 : Angle).
    rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub] at h1
    obtain ⟨m, hm⟩ := h1
    have hπ : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    -- hm : Real.pi * n / (3 * k) - 2 * π / 3 = 2 * π * m.
    have h3k : (3 * (k : ℝ)) ≠ 0 := by positivity
    have hn_eq : (n : ℝ) = 2*k + 6*k*m := by
      -- Multiply both sides of hm by 3k.
      have h1 : (Real.pi * (n : ℝ) / (3 * k) - 2 * Real.pi / 3) * (3 * k) = 2 * Real.pi * m * (3 * k) := by
        rw [hm]
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
      field_simp at h1
      linarith
    -- Now show m ≥ 0.
    have hm_nn : 0 ≤ m := by
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
      by_contra hneg
      push Not at hneg
      have hmi : (m : ℝ) ≤ -1 := by
        have : m ≤ -1 := by linarith
        exact_mod_cast this
      have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      have hk6 : (0 : ℝ) < 6 * k := by positivity
      nlinarith
    lift m to ℕ using hm_nn with m'
    left
    refine ⟨m', ?_⟩
    have : (n : ℝ) = 2*k + 6*k*(m' : ℝ) := by push_cast at hn_eq; exact_mod_cast hn_eq
    exact_mod_cast this
  · -- (π*n/(3k) : Angle) = -(2π/3 : Angle).
    rw [← Real.Angle.coe_neg, Real.Angle.angle_eq_iff_two_pi_dvd_sub] at h1
    obtain ⟨m, hm⟩ := h1
    have hπ : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    -- hm : π*n/(3k) - (-2π/3) = 2π*m.
    have h3k : (3 * (k : ℝ)) ≠ 0 := by positivity
    have hn_eq : (n : ℝ) = -2*k + 6*k*m := by
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
      have h1 : (Real.pi * (n : ℝ) / (3 * k) - (-(2 * Real.pi / 3))) * (3 * k) = 2 * Real.pi * m * (3 * k) := by
        rw [hm]
      field_simp at h1
      linarith
    -- Rewrite as n = 4k + 6k(m-1).
    have hn_eq' : (n : ℝ) = 4*k + 6*k*(m - 1) := by
      rw [hn_eq]; ring
    -- m ≥ 1 since n ≥ 0 and n = -2k + 6km.
    have hm_pos : 1 ≤ m := by
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
      by_contra hneg
      push Not at hneg
      have hm_le : (m : ℝ) ≤ 0 := by
        have : m ≤ 0 := by omega
        exact_mod_cast this
      have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      have hk6 : (0 : ℝ) < 6 * k := by positivity
      nlinarith
    have hm_minus_nn : 0 ≤ m - 1 := by linarith
    obtain ⟨m', hm'⟩ : ∃ m' : ℕ, (m' : ℤ) = m - 1 :=
      ⟨(m - 1).toNat, Int.toNat_of_nonneg hm_minus_nn⟩
    right
    refine ⟨m', ?_⟩
    have hm'R : (m' : ℝ) = (m : ℝ) - 1 := by
      have := congr_arg (fun (x : ℤ) => (x : ℝ)) hm'
      push_cast at this
      exact this
    have : (n : ℝ) = 4*k + 6*k*(m' : ℝ) := by
      rw [hn_eq', hm'R]
    exact_mod_cast this

snip end

problem imc2008_p7 (n k : ℕ) (_hn : 0 < n) (hk : 0 < k)
    (hdvd : ((X : ℤ[X])^(2*k) - X^k + 1) ∣ (X^(2*n) + X^n + 1)) :
    ((X : ℤ[X])^(2*k) + X^k + 1) ∣ (X^(2*n) + X^n + 1) := by
  rcases n_mod_6k_of_A_dvd_f n k hk hdvd with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact B_dvd_f_case_a n k m hm
  · exact B_dvd_f_case_b n k m hm

end Imc2008P7
