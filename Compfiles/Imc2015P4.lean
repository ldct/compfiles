/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory, .Algebra] }

/-!
# International Mathematical Competition 2015, Problem 4

Determine whether or not there exist 15 integers `m₁, …, m₁₅` such that
`∑ k, m k · arctan k = arctan 16`.

Answer: No.

Solution sketch (Gauss integers / Fermat prime argument):

If such integers `m_k` exist, apply `exp(i · _)` to both sides. Using
`exp(i arctan k) = (1 + k i)/√(1 + k²)`, we obtain
`∏ ((1 + k i)/√(1+k²))^(m_k) = (1 + 16 i)/√257`.
Rearranging gives `z * √257 = (1 + 16 i) * √N` in `ℂ`, where
`z := ∏ (1 + k i)^(m_k) ∈ ℚ[i]` and `N := ∏ (1 + k²)^(m_k) ∈ ℚ₊`.
Taking real parts: `z.re * √257 = √N`, so `257 * z.re² = N`.

Splitting `m_k = u_k - v_k` into positive and negative parts, let
`P := ∏ (1+ki)^(u_k)`, `Q := ∏ (1+ki)^(v_k)` (Gaussian integers), and let
`W := P · conj Q ∈ ℤ[i]`. Then `z · Nminus = W` where `Nminus := |Q|² ∈ ℤ₊`.
Taking real parts and multiplying `257 * z.re² = N` by `Nminus²`:

  `257 * W.re² = Nplus · Nminus = ∏ (1+k²)^(u_k + v_k) = ∏ (1+k²)^(|m_k|)`.

Since `W.re ∈ ℤ`, we get `257 ∣ ∏ (1+k²)^(|m_k|)`. By primality of `257`, we'd need
`257 ∣ 1 + k²` for some `k ∈ [1,15]`, but `1 + k² ≤ 226 < 257`. Contradiction.

This file provides a complete Lean 4/Mathlib formalization of the problem and
solution.
-/

namespace Imc2015P4

open scoped Real
open Complex

-- snip begin

/-- `exp(i · arctan k) = (1 + k * i) / √(1 + k²)` as a complex number,
for any real `k`. -/
lemma exp_I_arctan (k : ℝ) :
    Complex.exp ((Real.arctan k : ℂ) * I) =
      (1 + k * I) / (Real.sqrt (1 + k ^ 2) : ℂ) := by
  have hpos : 0 < Real.sqrt (1 + k ^ 2) := by
    apply Real.sqrt_pos.mpr; positivity
  have hne : (Real.sqrt (1 + k ^ 2) : ℂ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  rw [Complex.exp_mul_I]
  have hc : Complex.cos ((Real.arctan k : ℝ) : ℂ) = ((1 / Real.sqrt (1 + k ^ 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cos]
    exact_mod_cast Real.cos_arctan k
  have hs : Complex.sin ((Real.arctan k : ℝ) : ℂ) = ((k / Real.sqrt (1 + k ^ 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sin]
    exact_mod_cast Real.sin_arctan k
  rw [hc, hs]
  push_cast
  field_simp

/-- `257` is prime. -/
lemma prime_257 : Nat.Prime 257 := by norm_num

/-- For `k ∈ [1, 15]`, we have `1 + k² < 257`. -/
lemma one_add_sq_lt {k : ℕ} (hk : k ≤ 15) : 1 + k ^ 2 < 257 := by
  have : k ^ 2 ≤ 15 ^ 2 := Nat.pow_le_pow_left hk 2
  omega

/-- For `k ∈ [1, 15]`, `257 ∤ (1 + k²)` in ℕ. -/
lemma not_dvd_one_add_sq {k : ℕ} (hk : k ≤ 15) : ¬ (257 ∣ (1 + k ^ 2 : ℕ)) := by
  intro h
  have h1 : 1 + k ^ 2 < 257 := one_add_sq_lt hk
  have hpos : 0 < 1 + k ^ 2 := by positivity
  have := Nat.le_of_dvd hpos h
  omega

-- snip end

/-- The answer: no such integers exist. -/
determine answer : Prop := False

problem imc2015_p4 :
    answer ↔ ∃ m : Fin 15 → ℤ,
      ∑ k : Fin 15, (m k : ℝ) * Real.arctan ((k : ℕ) + 1) = Real.arctan 16 := by
  show False ↔ _
  refine ⟨False.elim, ?_⟩
  rintro ⟨m, hm⟩
  -- Step 1: Apply `exp(i · )` to the equation `∑ m_k arctan(k+1) = arctan 16`.
  have hexp_eq : Complex.exp (I * ((∑ k : Fin 15, (m k : ℝ) * Real.arctan ((k : ℕ) + 1) : ℝ) : ℂ)) =
      Complex.exp (I * ((Real.arctan 16 : ℝ) : ℂ)) := by
    rw [hm]
  -- Step 2: Expand LHS using `exp` of a sum, and `exp(i arctan k) = (1+ki)/√(1+k²)`.
  set z : ℂ := ∏ k : Fin 15, ((1 + ((k : ℕ) + 1 : ℝ) * I : ℂ) ^ (m k)) with hz_def
  set N : ℝ := ∏ k : Fin 15, (1 + ((k : ℕ) + 1 : ℝ) ^ 2) ^ (m k) with hN_def
  have hN_pos : 0 < N := by
    apply Finset.prod_pos
    intro k _
    apply zpow_pos
    positivity
  have hsqrtN_pos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN_pos
  have hsqrtN_ne : (Real.sqrt N : ℂ) ≠ 0 := by exact_mod_cast hsqrtN_pos.ne'
  have hsqrt257_pos : (0 : ℝ) < Real.sqrt 257 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt257_ne : (Real.sqrt 257 : ℂ) ≠ 0 := by exact_mod_cast hsqrt257_pos.ne'
  -- Compute LHS as z / √N.
  have hLHS : Complex.exp (I * ((∑ k : Fin 15, (m k : ℝ) * Real.arctan ((k : ℕ) + 1) : ℝ) : ℂ)) =
      z / (Real.sqrt N : ℂ) := by
    rw [show ((∑ k : Fin 15, (m k : ℝ) * Real.arctan ((k : ℕ) + 1) : ℝ) : ℂ) =
        (∑ k : Fin 15, ((m k : ℂ)) * (((Real.arctan ((k : ℕ) + 1) : ℝ) : ℂ))) from by
      push_cast; rfl]
    rw [Finset.mul_sum]
    rw [Complex.exp_sum]
    have h1 : ∀ k : Fin 15,
        Complex.exp (I * ((m k : ℂ) * ((Real.arctan ((k : ℕ) + 1) : ℝ) : ℂ))) =
        ((1 + ((k : ℕ) + 1 : ℝ) * I : ℂ) ^ (m k)) /
          ((Real.sqrt (1 + ((k : ℕ) + 1 : ℝ) ^ 2) : ℝ) : ℂ) ^ (m k) := by
      intro k
      have heq : I * ((m k : ℂ) * ((Real.arctan ((k : ℕ) + 1) : ℝ) : ℂ)) =
          (m k : ℂ) * (((Real.arctan ((k : ℕ) + 1) : ℝ) : ℂ) * I) := by ring
      rw [heq, Complex.exp_int_mul, exp_I_arctan, div_zpow]
    rw [Finset.prod_congr rfl (fun k _ => h1 k)]
    have key_sqrt : ((Real.sqrt N : ℝ) : ℂ) =
        ∏ k : Fin 15, ((Real.sqrt (1 + ((k : ℕ) + 1 : ℝ) ^ 2) : ℝ) : ℂ) ^ (m k) := by
      have key : Real.sqrt N =
          ∏ k : Fin 15, (Real.sqrt (1 + ((k : ℕ) + 1 : ℝ) ^ 2)) ^ (m k) := by
        rw [hN_def]
        rw [show (∏ k : Fin 15, (1 + ((k : ℕ) + 1 : ℝ) ^ 2) ^ (m k)) =
              (∏ k : Fin 15, (Real.sqrt (1 + ((k : ℕ) + 1 : ℝ) ^ 2)) ^ (m k)) ^ 2 by
          rw [← Finset.prod_pow]
          apply Finset.prod_congr rfl
          intro k _
          have hpos : (0 : ℝ) ≤ 1 + ((k : ℕ) + 1 : ℝ) ^ 2 := by positivity
          have h_sq : (Real.sqrt (1 + ((k : ℕ) + 1 : ℝ) ^ 2)) ^ 2 =
              1 + ((k : ℕ) + 1 : ℝ) ^ 2 := Real.sq_sqrt hpos
          rw [show ((Real.sqrt (1 + ((k : ℕ) + 1 : ℝ) ^ 2)) ^ (m k)) ^ 2 =
              ((Real.sqrt (1 + ((k : ℕ) + 1 : ℝ) ^ 2)) ^ 2) ^ (m k) from by
            rw [show ((Real.sqrt (1 + ((k : ℕ) + 1 : ℝ) ^ 2)) ^ (m k)) ^ 2 =
                (Real.sqrt (1 + ((k : ℕ) + 1 : ℝ) ^ 2)) ^ (m k * 2) by
              rw [zpow_mul]; rfl]
            rw [show (m k : ℤ) * 2 = 2 * m k by ring, zpow_mul]
            rfl]
          rw [h_sq]]
        rw [Real.sqrt_sq]
        apply Finset.prod_nonneg
        intro k _
        apply zpow_nonneg
        exact Real.sqrt_nonneg _
      rw [key]
      push_cast
      rfl
    rw [show z / (Real.sqrt N : ℂ) =
        (∏ k : Fin 15, ((1 + ((k : ℕ) + 1 : ℝ) * I : ℂ) ^ (m k))) /
          (∏ k : Fin 15, ((Real.sqrt (1 + ((k : ℕ) + 1 : ℝ) ^ 2) : ℝ) : ℂ) ^ (m k)) from by
      rw [hz_def, key_sqrt]]
    rw [← Finset.prod_div_distrib]
  -- Compute RHS = (1 + 16 i)/√257.
  have hRHS : Complex.exp (I * ((Real.arctan 16 : ℝ) : ℂ)) =
      (1 + 16 * I) / (Real.sqrt 257 : ℂ) := by
    rw [show I * ((Real.arctan 16 : ℝ) : ℂ) = ((Real.arctan 16 : ℝ) : ℂ) * I from by ring]
    rw [exp_I_arctan]
    norm_num
  rw [hLHS, hRHS] at hexp_eq
  -- So z / √N = (1 + 16i) / √257.
  -- Clear denominators: z * √257 = (1+16i) * √N.
  have hz_cross : z * (Real.sqrt 257 : ℂ) = (1 + 16 * I) * (Real.sqrt N : ℂ) := by
    rw [div_eq_div_iff hsqrtN_ne hsqrt257_ne] at hexp_eq
    linear_combination hexp_eq
  -- Take real and imaginary parts. z.re * √257 = √N and z.im * √257 = 16 √N.
  have hz_re : z.re * Real.sqrt 257 = Real.sqrt N := by
    have := congr_arg Complex.re hz_cross
    simp [Complex.mul_re, Complex.mul_im] at this
    linarith [this]
  have hz_im : z.im * Real.sqrt 257 = 16 * Real.sqrt N := by
    have := congr_arg Complex.im hz_cross
    simp [Complex.mul_re, Complex.mul_im] at this
    linarith [this]
  -- From these: z.im = 16 * z.re, and 257 * z.re² = N.
  have hz_re_sq : (257 : ℝ) * z.re ^ 2 = N := by
    have h1 : (z.re * Real.sqrt 257) ^ 2 = Real.sqrt N ^ 2 := by
      rw [hz_re]
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 257),
        Real.sq_sqrt hN_pos.le] at h1
    linarith
  -- Step: Show 257 divides a product of small integer factors, contradiction.
  -- Helper: A complex number is a "Gaussian integer" if re and im are integers.
  let isGI : ℂ → Prop := fun w => ∃ a b : ℤ, w = (a : ℂ) + (b : ℂ) * I
  have isGI_one : isGI 1 := ⟨1, 0, by simp⟩
  have isGI_mul : ∀ {x y : ℂ}, isGI x → isGI y → isGI (x * y) := by
    rintro x y ⟨a, b, hx⟩ ⟨c, d, hy⟩
    refine ⟨a * c - b * d, a * d + b * c, ?_⟩
    rw [hx, hy]
    push_cast
    have hI : I * I = -1 := Complex.I_mul_I
    ring_nf
    linear_combination (b * d : ℂ) * hI
  have isGI_pow : ∀ {x : ℂ} (n : ℕ), isGI x → isGI (x ^ n) := by
    intro x n hx
    induction n with
    | zero => simpa using isGI_one
    | succ n ih => rw [pow_succ]; exact isGI_mul ih hx
  have isGI_conj : ∀ {x : ℂ}, isGI x → isGI ((starRingEnd ℂ) x) := by
    rintro x ⟨a, b, hx⟩
    refine ⟨a, -b, ?_⟩
    rw [hx]
    push_cast
    simp [Complex.conj_I]
  have isGI_factor : ∀ k : Fin 15, isGI ((1 + ((k : ℕ) + 1 : ℝ) * I : ℂ)) := by
    intro k
    refine ⟨1, ((k : ℕ) + 1 : ℤ), ?_⟩
    push_cast
    ring
  have isGI_prod : ∀ (f : Fin 15 → ℂ),
      (∀ i, isGI (f i)) → isGI (∏ i : Fin 15, f i) := by
    intro f hall
    induction (Finset.univ : Finset (Fin 15)) using Finset.induction_on with
    | empty => simpa using isGI_one
    | @insert a t hat ih => rw [Finset.prod_insert hat]; exact isGI_mul (hall a) ih
  -- Define u, v as ℕ-valued exponents for positive/negative parts of m.
  -- P := ∏ (1+(k+1)i)^u_k, Q := ∏ (1+(k+1)i)^v_k, both Gaussian integers.
  have hP_isGI : isGI (∏ k : Fin 15, ((1 + ((k : ℕ) + 1 : ℝ) * I : ℂ) ^ (m k).toNat)) :=
    isGI_prod _ (fun k => isGI_pow _ (isGI_factor k))
  have hQ_isGI : isGI (∏ k : Fin 15, ((1 + ((k : ℕ) + 1 : ℝ) * I : ℂ) ^ (-(m k)).toNat)) :=
    isGI_prod _ (fun k => isGI_pow _ (isGI_factor k))
  have hW_isGI : isGI ((∏ k : Fin 15, ((1 + ((k : ℕ) + 1 : ℝ) * I : ℂ) ^ (m k).toNat)) *
      (starRingEnd ℂ) (∏ k : Fin 15, ((1 + ((k : ℕ) + 1 : ℝ) * I : ℂ) ^ (-(m k)).toNat))) :=
    isGI_mul hP_isGI (isGI_conj hQ_isGI)
  obtain ⟨wa, wb, hW_rep⟩ := hW_isGI
  -- Name the big expressions for clarity.
  -- Let B := ∏ (1 + (k+1)²)^v_k (a positive ℕ).
  -- Then z * B = W (the Gaussian integer above).
  -- Let Nplus := ∏ (1 + (k+1)²)^u_k, Nminus := B. Then 257 * W.re² = Nplus * Nminus.
  have hm_split : ∀ k : Fin 15, (m k : ℤ) = ((m k).toNat : ℤ) - ((-(m k)).toNat : ℤ) := by
    intro k; omega
  have hfactor_ne : ∀ k : Fin 15, ((1 + ((k : ℕ) + 1 : ℝ) * I : ℂ)) ≠ 0 := by
    intro k h
    have h1 := congr_arg Complex.im h
    simp [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
          Complex.ofReal_re, Complex.ofReal_im, Complex.one_im] at h1
    -- h1 : ((k : ℕ) + 1 : ℝ) = 0, impossible.
    have : ((k : ℕ) + 1 : ℝ) > 0 := by positivity
    linarith
  -- Prove z * Q = P.
  have hzQ : z * (∏ k : Fin 15, ((1 + ((k : ℕ) + 1 : ℝ) * I : ℂ) ^ (-(m k)).toNat)) =
      (∏ k : Fin 15, ((1 + ((k : ℕ) + 1 : ℝ) * I : ℂ) ^ (m k).toNat)) := by
    rw [hz_def, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k _
    rw [show ((1 + ((k : ℕ) + 1 : ℝ) * I : ℂ) ^ ((-(m k)).toNat) : ℂ) =
        ((1 + ((k : ℕ) + 1 : ℝ) * I : ℂ) ^ ((-(m k)).toNat : ℤ) : ℂ) by push_cast; rfl]
    rw [← zpow_add₀ (hfactor_ne k)]
    rw [show ((1 + ((k : ℕ) + 1 : ℝ) * I : ℂ) ^ ((m k).toNat) : ℂ) =
        ((1 + ((k : ℕ) + 1 : ℝ) * I : ℂ) ^ ((m k).toNat : ℤ) : ℂ) by push_cast; rfl]
    congr 1
    have := hm_split k
    omega
  -- Compute |Q|² = Nminus = ∏ (1+(k+1)²)^v_k as a positive natural.
  have hQ_normSq : Complex.normSq (∏ k : Fin 15,
      ((1 + ((k : ℕ) + 1 : ℝ) * I : ℂ) ^ (-(m k)).toNat)) =
      ∏ k : Fin 15, ((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℝ) ^ (-(m k)).toNat := by
    rw [show Complex.normSq (∏ k : Fin 15,
          ((1 + ((k : ℕ) + 1 : ℝ) * I : ℂ) ^ (-(m k)).toNat)) =
        ∏ k : Fin 15, Complex.normSq (((1 + ((k : ℕ) + 1 : ℝ) * I : ℂ) ^ (-(m k)).toNat)) from
      map_prod Complex.normSq.toMonoidHom _ _]
    apply Finset.prod_congr rfl
    intro k _
    rw [map_pow]
    congr 1
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
          Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
    push_cast
    ring
  -- Use mul_conj: z * (Q * conj Q) = z * |Q|². But first we need z * Q = P.
  -- z * Q * conj Q = P * conj Q = W (our Gaussian integer).
  -- z * |Q|² = P * conj Q.
  -- Same product expressed cleanly as a ℂ value coming from real coercion.
  have hzW : z * ((∏ k : Fin 15, ((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℂ) ^ (-(m k)).toNat)) =
      (wa : ℂ) + (wb : ℂ) * I := by
    rw [← hW_rep]
    have h_cast : (∏ k : Fin 15, ((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℂ) ^ (-(m k)).toNat) =
        (Complex.normSq (∏ k : Fin 15,
          ((1 + ((k : ℕ) + 1 : ℝ) * I : ℂ) ^ (-(m k)).toNat)) : ℂ) := by
      rw [show (Complex.normSq (∏ k : Fin 15,
            ((1 + ((k : ℕ) + 1 : ℝ) * I : ℂ) ^ (-(m k)).toNat)) : ℝ) =
          (∏ k : Fin 15, ((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℝ) ^ (-(m k)).toNat) from hQ_normSq]
      push_cast
      rfl
    rw [h_cast]
    rw [show (Complex.normSq (∏ k : Fin 15,
          ((1 + ((k : ℕ) + 1 : ℝ) * I : ℂ) ^ (-(m k)).toNat)) : ℂ) =
        (∏ k : Fin 15, ((1 + ((k : ℕ) + 1 : ℝ) * I : ℂ) ^ (-(m k)).toNat)) *
          (starRingEnd ℂ) (∏ k : Fin 15,
            ((1 + ((k : ℕ) + 1 : ℝ) * I : ℂ) ^ (-(m k)).toNat)) from (mul_conj _).symm]
    rw [← mul_assoc, hzQ]
  have hWre_eq : z.re * ((∏ k : Fin 15, ((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℝ) ^ (-(m k)).toNat)) =
      (wa : ℝ) := by
    have hh := congr_arg Complex.re hzW
    have hprod_eq : (∏ k : Fin 15,
        ((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℂ) ^ (-(m k)).toNat) =
        ((∏ k : Fin 15, ((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℝ) ^ (-(m k)).toNat : ℝ) : ℂ) := by
      push_cast
      rfl
    have hprod_re : (∏ k : Fin 15,
        ((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℂ) ^ (-(m k)).toNat).re =
        ∏ k : Fin 15, ((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℝ) ^ (-(m k)).toNat := by
      rw [hprod_eq, Complex.ofReal_re]
    have hprod_im : (∏ k : Fin 15,
        ((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℂ) ^ (-(m k)).toNat).im = 0 := by
      rw [hprod_eq, Complex.ofReal_im]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.add_re, Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
          mul_zero, sub_zero, zero_mul, add_zero, hprod_re, hprod_im] at hh
    linarith
  -- 257 * z.re² * B² = N * B² = (Nplus/Nminus) * B² = Nplus * Nminus = ∏ (1+(k+1)²)^(|m_k|).
  -- We prove 257 * wa² = ∏ (1+(k+1)²)^((m k).toNat + (-(m k)).toNat).
  have hfinal : (257 : ℤ) * wa ^ 2 =
      ∏ k : Fin 15, ((1 + ((k : ℕ) + 1) ^ 2 : ℤ)) ^ ((m k).toNat + (-(m k)).toNat) := by
    -- From 257 * z.re² = N, multiply by Nminus² and use N * Nminus = Nplus.
    have hN_mul : N * (∏ k : Fin 15, ((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℝ) ^ (-(m k)).toNat) =
        (∏ k : Fin 15, ((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℝ) ^ ((m k).toNat)) := by
      rw [hN_def]
      rw [show (∏ k : Fin 15, (1 + ((k : ℕ) + 1 : ℝ) ^ 2) ^ (m k)) *
            (∏ k : Fin 15, ((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℝ) ^ (-(m k)).toNat) =
          ∏ k : Fin 15, ((1 + ((k : ℕ) + 1 : ℝ) ^ 2) ^ (m k) *
            (((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℝ) ^ (-(m k)).toNat)) from Finset.prod_mul_distrib.symm]
      apply Finset.prod_congr rfl
      intro k _
      have hpos : (0 : ℝ) < 1 + ((k : ℕ) + 1 : ℝ) ^ 2 := by positivity
      have hcast : (((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℝ)) = 1 + ((k : ℕ) + 1 : ℝ) ^ 2 := by
        push_cast; ring
      rw [hcast]
      rw [show ((1 + ((k : ℕ) + 1 : ℝ) ^ 2) ^ ((-(m k)).toNat) : ℝ) =
          ((1 + ((k : ℕ) + 1 : ℝ) ^ 2) ^ ((-(m k)).toNat : ℤ) : ℝ) by push_cast; rfl]
      rw [show ((1 + ((k : ℕ) + 1 : ℝ) ^ 2) ^ ((m k).toNat) : ℝ) =
          ((1 + ((k : ℕ) + 1 : ℝ) ^ 2) ^ ((m k).toNat : ℤ) : ℝ) by push_cast; rfl]
      rw [← zpow_add₀ hpos.ne']
      congr 1
      have := hm_split k
      omega
    -- Now we have: 257 * z.re² * B² = Nplus * B after using hN_mul
    -- Also z.re * B = wa, so z.re² * B² = wa².
    have h_wa_sq : z.re ^ 2 *
        (∏ k : Fin 15, ((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℝ) ^ (-(m k)).toNat) ^ 2 =
        (wa : ℝ) ^ 2 := by
      rw [show z.re ^ 2 *
          (∏ k : Fin 15, ((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℝ) ^ (-(m k)).toNat) ^ 2 =
          (z.re * ∏ k : Fin 15,
            ((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℝ) ^ (-(m k)).toNat) ^ 2 by ring]
      rw [hWre_eq]
    have h_real : (257 : ℝ) * (wa : ℝ) ^ 2 =
        ∏ k : Fin 15, ((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℝ) ^ ((m k).toNat + (-(m k)).toNat) := by
      calc (257 : ℝ) * (wa : ℝ) ^ 2
          = (257 : ℝ) * (z.re ^ 2 *
              (∏ k : Fin 15, ((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℝ) ^ (-(m k)).toNat) ^ 2) := by
            rw [h_wa_sq]
        _ = (257 * z.re ^ 2) *
              (∏ k : Fin 15, ((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℝ) ^ (-(m k)).toNat) ^ 2 := by ring
        _ = N * (∏ k : Fin 15, ((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℝ) ^ (-(m k)).toNat) ^ 2 := by
            rw [hz_re_sq]
        _ = (N * (∏ k : Fin 15, ((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℝ) ^ (-(m k)).toNat)) *
              (∏ k : Fin 15, ((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℝ) ^ (-(m k)).toNat) := by ring
        _ = (∏ k : Fin 15, ((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℝ) ^ ((m k).toNat)) *
              (∏ k : Fin 15, ((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℝ) ^ (-(m k)).toNat) := by
            rw [hN_mul]
        _ = ∏ k : Fin 15,
              ((1 + ((k : ℕ) + 1) ^ 2 : ℕ) : ℝ) ^ ((m k).toNat + (-(m k)).toNat) := by
            rw [← Finset.prod_mul_distrib]
            apply Finset.prod_congr rfl
            intro k _
            rw [← pow_add]
    exact_mod_cast h_real
  -- Now 257 | Nplus * Nminus (as ℤ hence ℕ).
  have hfinal_nat : (257 : ℕ) ∣
      ∏ k : Fin 15, ((1 + ((k : ℕ) + 1) ^ 2 : ℕ)) ^ ((m k).toNat + (-(m k)).toNat) := by
    have h1 : (257 : ℤ) ∣
        ∏ k : Fin 15, ((1 + ((k : ℕ) + 1) ^ 2 : ℤ)) ^ ((m k).toNat + (-(m k)).toNat) :=
      ⟨wa ^ 2, by linarith [hfinal]⟩
    have h2 : (∏ k : Fin 15, ((1 + ((k : ℕ) + 1) ^ 2 : ℤ)) ^ ((m k).toNat + (-(m k)).toNat)) =
        ((∏ k : Fin 15, ((1 + ((k : ℕ) + 1) ^ 2 : ℕ)) ^ ((m k).toNat + (-(m k)).toNat) : ℕ) : ℤ) := by
      push_cast; rfl
    rw [h2] at h1
    exact_mod_cast h1
  -- 257 prime, so divides some factor.
  have hp_prime_nat : Nat.Prime 257 := prime_257
  have hp_prime : Prime (257 : ℕ) := hp_prime_nat.prime
  rw [Prime.dvd_finset_prod_iff hp_prime] at hfinal_nat
  obtain ⟨k, _, hdvd_k⟩ := hfinal_nat
  -- Now 257 | (1 + (k+1)²)^(expo). By primality, 257 | 1 + (k+1)² or the power is 0.
  by_cases h_exp : (m k).toNat + (-(m k)).toNat = 0
  · rw [h_exp, pow_zero] at hdvd_k
    exact absurd (Nat.le_of_dvd Nat.one_pos hdvd_k) (by norm_num)
  · rw [Prime.dvd_pow_iff_dvd hp_prime h_exp] at hdvd_k
    have hk15 : (k : ℕ) + 1 ≤ 15 := by
      have : (k : ℕ) < 15 := k.isLt
      omega
    exact not_dvd_one_add_sq hk15 hdvd_k

end Imc2015P4
