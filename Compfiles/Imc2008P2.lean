/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2008, Problem 2

Let `V` be the real vector space of all real polynomials in one variable, and
let `P : V → ℝ` be a linear map. Suppose that for all `f, g ∈ V`,
`P(fg) = 0` implies `P(f) = 0` or `P(g) = 0`. Prove that there exist
`x₀, c ∈ ℝ` such that `P(f) = c · f(x₀)` for all `f`.
-/

namespace Imc2008P2

open Polynomial

snip begin

/-- Shift-by-`b` ring homomorphism `ℝ[X] → ℝ[X]`, sending `f(X)` to `f(X+b)`. -/
noncomputable def shift (b : ℝ) (f : ℝ[X]) : ℝ[X] := f.comp (X + C b)

lemma shift_eval (b : ℝ) (f : ℝ[X]) (x : ℝ) : (shift b f).eval x = f.eval (x + b) := by
  unfold shift; rw [eval_comp]; simp

lemma shift_X (b : ℝ) : shift b X = X + C b := by
  unfold shift; rw [X_comp]

lemma shift_one (b : ℝ) : shift b 1 = 1 := by
  unfold shift; rw [one_comp]

lemma shift_mul (b : ℝ) (f g : ℝ[X]) : shift b (f * g) = shift b f * shift b g := by
  unfold shift; rw [mul_comp]

lemma shift_add (b : ℝ) (f g : ℝ[X]) : shift b (f + g) = shift b f + shift b g := by
  unfold shift; rw [add_comp]

lemma shift_C (b : ℝ) (r : ℝ) : shift b (C r) = C r := by
  unfold shift; rw [C_comp]

lemma shift_smul (b : ℝ) (r : ℝ) (f : ℝ[X]) : shift b (r • f) = r • shift b f := by
  rw [show (r • f : ℝ[X]) = C r * f from by rw [smul_eq_C_mul]]
  rw [shift_mul, shift_C, smul_eq_C_mul]

/-- The composition of a linear map `P : ℝ[X] → ℝ` with the shift is still linear. -/
noncomputable def Pshift (P : ℝ[X] →ₗ[ℝ] ℝ) (b : ℝ) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun f := P (shift b f)
  map_add' f g := by show P (shift b (f + g)) = _; rw [shift_add]; exact map_add _ _ _
  map_smul' r f := by
    show P (shift b (r • f)) = r • P (shift b f)
    rw [shift_smul]; exact map_smul _ _ _

lemma Pshift_apply (P : ℝ[X] →ₗ[ℝ] ℝ) (b : ℝ) (f : ℝ[X]) :
    Pshift P b f = P (shift b f) := rfl

/-- Expansion of `(X + 1)^m` as a sum: `(X+1)^m = ∑_j C(m,j) • X^j`. -/
lemma Xplus1_pow (m : ℕ) : ((X + 1 : ℝ[X]) ^ m) = ∑ j ∈ Finset.range (m + 1),
    ((m.choose j : ℝ)) • X ^ j := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro j _
  rw [one_pow, mul_one]
  -- X^j * (choose m j : ℝ[X]) = (choose m j : ℝ) • X^j
  rw [show (((m.choose j) : ℕ) : ℝ[X]) = C ((m.choose j) : ℝ) from by norm_cast]
  rw [mul_comm, ← smul_eq_C_mul]

/-- Induction step: given `Q(1) = 1`, `Q(X) = 0`, `Q(X^k) = 0` for `1 ≤ k < n`,
and the prime-kernel property, we have `Q(X^n) = 0` for `n ≥ 2`. -/
lemma induction_step (Q : ℝ[X] →ₗ[ℝ] ℝ) (hQ1 : Q 1 = 1) (hQX : Q X = 0)
    (hprime : ∀ f g : ℝ[X], Q (f * g) = 0 → Q f = 0 ∨ Q g = 0)
    (n : ℕ) (hn : 2 ≤ n)
    (hih : ∀ k : ℕ, 1 ≤ k → k < n → Q (X ^ k) = 0) :
    Q (X ^ n) = 0 := by
  set e : ℝ := - Q (X ^ n) with he_def
  -- Q((X+1)^{n-1}) = 1: only the j=0 term (= X^0 = 1) survives; Q of other X^j is 0.
  have hQ_Xplus1_pow : Q ((X + 1) ^ (n - 1)) = 1 := by
    rw [Xplus1_pow, map_sum]
    rw [Finset.sum_eq_single 0]
    · rw [map_smul, pow_zero, hQ1, Nat.choose_zero_right, smul_eq_mul, mul_one]; push_cast; rfl
    · intro j hj hj0
      rw [map_smul]
      rw [Finset.mem_range] at hj
      have hj1 : 1 ≤ j := by omega
      have hjlt : j < n := by omega
      rw [hih j hj1 hjlt, smul_zero]
    · intro h; exfalso; apply h; rw [Finset.mem_range]; omega
  -- Q(X * (X+1)^{n-1}) = Q(X^n): only the j = n-1 term has X^n, with coefficient C(n-1,n-1) = 1.
  have hQ_X_mul : Q (X * (X + 1) ^ (n - 1)) = Q (X ^ n) := by
    have hexp : (X * (X + 1 : ℝ[X]) ^ (n - 1)) = ∑ j ∈ Finset.range n,
        (((n - 1).choose j : ℝ)) • X ^ (j + 1) := by
      have hrange : n - 1 + 1 = n := by omega
      rw [Xplus1_pow (n - 1), hrange, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_smul_comm]
      rw [show X * X ^ j = X ^ (j + 1) from by ring]
    rw [hexp, map_sum]
    rw [Finset.sum_eq_single (n - 1)]
    · have hnm1 : (n - 1) + 1 = n := by omega
      rw [hnm1, Nat.choose_self, map_smul, smul_eq_mul]; push_cast; rw [one_mul]
    · intro j hj hj_ne
      rw [map_smul]
      rw [Finset.mem_range] at hj
      have hj1_le : j + 1 < n := by omega
      have hjp1 : 1 ≤ j + 1 := by omega
      rw [hih (j + 1) hjp1 hj1_le, smul_zero]
    · intro h; exfalso; apply h; rw [Finset.mem_range]; omega
  -- Q((X+e)(X+1)^{n-1}) = Q(X^n) + e * Q((X+1)^{n-1}) = Q(X^n) + e = 0.
  have hQ_big : Q ((X + C e) * (X + 1) ^ (n - 1)) = 0 := by
    have hsplit : (X + C e : ℝ[X]) * (X + 1) ^ (n - 1) =
        X * (X + 1) ^ (n - 1) + C e * (X + 1) ^ (n - 1) := by ring
    rw [hsplit, map_add]
    have h1 : Q (C e * (X + 1) ^ (n - 1)) = e * Q ((X + 1) ^ (n - 1)) := by
      rw [show (C e * (X + 1 : ℝ[X]) ^ (n - 1)) = e • (X + 1) ^ (n - 1) from by
        rw [smul_eq_C_mul]]
      rw [map_smul, smul_eq_mul]
    rw [hQ_X_mul, h1, hQ_Xplus1_pow, mul_one]
    rw [he_def]; ring
  -- Apply prime property.
  rcases hprime _ _ hQ_big with hQXe | hQpow
  · -- Q(X + C e) = 0, i.e., Q X + e * Q 1 = 0 + e = e. So e = 0, i.e., Q(X^n) = 0.
    have h_split : Q (X + C e) = Q X + e * Q 1 := by
      rw [show (X + C e : ℝ[X]) = X + e • (1 : ℝ[X]) from by
        rw [show e • (1 : ℝ[X]) = C e from by rw [smul_eq_C_mul, mul_one]]]
      rw [map_add, map_smul, smul_eq_mul]
    rw [hQX, hQ1, zero_add, mul_one] at h_split
    rw [h_split] at hQXe
    rw [he_def] at hQXe; linarith
  · -- Q((X+1)^{n-1}) = 0, contradicting hQ_Xplus1_pow = 1.
    rw [hQpow] at hQ_Xplus1_pow; norm_num at hQ_Xplus1_pow

/-- If `Q : ℝ[X] → ℝ` is linear with `Q(1) = 1`, `Q(X) = 0`, and the prime-kernel property,
then `Q(f) = f.eval 0` for all `f`. -/
lemma Q_eq_eval_zero (Q : ℝ[X] →ₗ[ℝ] ℝ) (hQ1 : Q 1 = 1) (hQX : Q X = 0)
    (hprime : ∀ f g : ℝ[X], Q (f * g) = 0 → Q f = 0 ∨ Q g = 0) (f : ℝ[X]) :
    Q f = f.eval 0 := by
  -- Strong induction: Q(X^k) = 0 for all k ≥ 1.
  have hQXk : ∀ k : ℕ, 1 ≤ k → Q (X ^ k) = 0 := by
    intro k hk
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      match k, hk with
      | 1, _ => simpa using hQX
      | (k + 2), _ =>
        apply induction_step Q hQ1 hQX hprime (k + 2) (by omega)
        intro j hj1 hjlt
        exact ih j hjlt hj1
  -- Q(f) = coeff f 0, by induction on polynomials.
  have hQf : Q f = f.coeff 0 := by
    induction f using Polynomial.induction_on' with
    | add p q ihp ihq =>
      rw [map_add, ihp, ihq, coeff_add]
    | monomial n r =>
      -- Q(monomial n r) = r * Q(X^n). Handle n = 0 and n ≥ 1 separately.
      have h_mon : ((monomial n) r : ℝ[X]) = r • X ^ n := by
        rw [← C_mul_X_pow_eq_monomial, smul_eq_C_mul]
      rw [h_mon, map_smul, smul_eq_mul]
      rw [show ((r • X ^ n : ℝ[X])).coeff 0 = r * (X ^ n : ℝ[X]).coeff 0 from by
        rw [smul_eq_C_mul, coeff_C_mul]]
      by_cases hn : n = 0
      · subst hn
        rw [pow_zero, hQ1, mul_one, coeff_one_zero, mul_one]
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        rw [hQXk n hn1, mul_zero, coeff_X_pow, if_neg (Ne.symm hn), mul_zero]
  rw [hQf, ← coeff_zero_eq_eval_zero]

snip end

problem imc2008_p2 (P : ℝ[X] →ₗ[ℝ] ℝ)
    (hprime : ∀ f g : ℝ[X], P (f * g) = 0 → P f = 0 ∨ P g = 0) :
    ∃ (x₀ c : ℝ), ∀ f : ℝ[X], P f = c * f.eval x₀ := by
  -- Case: P is identically zero.
  by_cases hP0 : ∀ f : ℝ[X], P f = 0
  · refine ⟨0, 0, ?_⟩
    intro f; rw [hP0 f]; ring
  push Not at hP0
  obtain ⟨f₀, hf₀⟩ := hP0
  -- P(f₀²) ≠ 0: otherwise prime gives P(f₀) = 0, contradicting hf₀.
  have hf₀sq : P (f₀ * f₀) ≠ 0 := by
    intro h
    rcases hprime _ _ h with h1 | h2
    · exact hf₀ h1
    · exact hf₀ h2
  -- Let a := P(f₀²) / P(f₀).
  set a : ℝ := P (f₀ * f₀) / P f₀ with ha_def
  have ha_ne : a ≠ 0 := div_ne_zero hf₀sq hf₀
  -- P (f₀ * (f₀ - a • 1)) = P(f₀*f₀) - a*P(f₀) = P(f₀²) - P(f₀²) = 0.
  have hkey : P (f₀ * (f₀ - a • 1)) = 0 := by
    rw [mul_sub, map_sub]
    rw [show f₀ * (a • 1 : ℝ[X]) = a • f₀ from by rw [smul_eq_C_mul, smul_eq_C_mul, mul_one]; ring]
    rw [map_smul, smul_eq_mul]
    rw [ha_def]; field_simp; ring
  -- Prime: either P f₀ = 0 (no) or P (f₀ - a • 1) = 0.
  rcases hprime _ _ hkey with hP_f₀ | hP_f₀_sub
  · exact absurd hP_f₀ hf₀
  -- P(f₀ - a • 1) = P(f₀) - a * P(1) = 0, so P(f₀) = a * P(1).
  have hP1_eq : a * P 1 = P f₀ := by
    rw [map_sub, map_smul, smul_eq_mul] at hP_f₀_sub
    linarith
  have hP1 : P 1 ≠ 0 := by
    intro h; rw [h, mul_zero] at hP1_eq
    exact hf₀ hP1_eq.symm
  -- Define P' = (P 1)⁻¹ • P, so P'(1) = 1.
  set P' : ℝ[X] →ₗ[ℝ] ℝ := (P 1)⁻¹ • P with hP'_def
  have hP'1 : P' 1 = 1 := by
    show (P 1)⁻¹ * P 1 = 1
    rw [inv_mul_cancel₀ hP1]
  have hP'apply : ∀ f, P' f = (P 1)⁻¹ * P f := fun _ => rfl
  -- P' preserves the prime property.
  have hP'prime : ∀ f g : ℝ[X], P' (f * g) = 0 → P' f = 0 ∨ P' g = 0 := by
    intro f g hfg
    rw [hP'apply] at hfg
    have hinv : (P 1)⁻¹ ≠ 0 := inv_ne_zero hP1
    have hPfg : P (f * g) = 0 := by
      rcases mul_eq_zero.mp hfg with h | h
      · exact absurd h hinv
      · exact h
    rcases hprime f g hPfg with hf | hg
    · left; rw [hP'apply, hf]; ring
    · right; rw [hP'apply, hg]; ring
  -- Let b = -P'(X). Then Q(f) = P'(shift b f). Q(1) = 1, Q(X) = 0.
  set b : ℝ := - P' X with hb_def
  set Q : ℝ[X] →ₗ[ℝ] ℝ := Pshift P' b with hQ_def
  have hQ1 : Q 1 = 1 := by
    rw [hQ_def, Pshift_apply, shift_one, hP'1]
  have hQX : Q X = 0 := by
    rw [hQ_def, Pshift_apply, shift_X]
    rw [show (X + C b : ℝ[X]) = X + b • (1 : ℝ[X]) from by
      rw [show b • (1 : ℝ[X]) = C b from by rw [smul_eq_C_mul, mul_one]]]
    rw [map_add, map_smul, hP'1, smul_eq_mul, mul_one]
    rw [hb_def]; linarith
  have hQprime : ∀ f g : ℝ[X], Q (f * g) = 0 → Q f = 0 ∨ Q g = 0 := by
    intro f g hfg
    rw [hQ_def, Pshift_apply, shift_mul] at hfg
    rcases hP'prime _ _ hfg with h1 | h2
    · left; rw [hQ_def, Pshift_apply]; exact h1
    · right; rw [hQ_def, Pshift_apply]; exact h2
  -- Use Q f = f.eval 0, specialized to shift (-b) f, to deduce P'(f) = f.eval(-b).
  refine ⟨-b, P 1, ?_⟩
  intro f
  have hP'f : P' f = f.eval (-b) := by
    have hshift_inv : shift b (shift (-b) f) = f := by
      unfold shift
      rw [Polynomial.comp_assoc]
      have hcan : (X + C (-b) : ℝ[X]).comp (X + C b) = X := by
        rw [add_comp, X_comp, C_comp]
        have hneg : C (-b) = -C b := by rw [C_neg]
        rw [hneg]; ring
      rw [hcan, comp_X]
    have h1 : Q (shift (-b) f) = P' f := by
      rw [hQ_def, Pshift_apply, hshift_inv]
    have h2 : Q (shift (-b) f) = f.eval (-b) := by
      rw [Q_eq_eval_zero Q hQ1 hQX hQprime]
      rw [shift_eval]; congr 1; ring
    linarith
  -- P(f) = P(1) * P'(f) = P(1) * f.eval (-b).
  have hPfP' : P f = P 1 * P' f := by
    rw [hP'apply, ← mul_assoc, mul_inv_cancel₀ hP1, one_mul]
  rw [hPfP', hP'f]

end Imc2008P2
