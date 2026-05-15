/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2000, Problem 12

For `m × m` real matrices, define `e^A = ∑_{n ≥ 0} A^n/n!`.
Prove that for every real polynomial `p` and every pair of `m × m` real
matrices `A, B`, the matrix `p(e^{AB})` is nilpotent if and only if
`p(e^{BA})` is.

## Proof outline

The key algebraic identity is `A · e^{BA} = e^{AB} · A` (since
`(AB)^n · A = A · (BA)^n` for every `n`, and both series converge in
any submultiplicative matrix norm). More generally, for any polynomial
`r : ℝ[X]`, we have `r(e^{AB}) · A = A · r(e^{BA})`.

Writing `p(y) - p(1) = (y - 1) · r(y)` as polynomials, we obtain
  `p(e^{AB}) - p(1) · I = A · C`,
  `p(e^{BA}) - p(1) · I = C · A`,
where `C := B · S(AB) · r(e^{AB})` and `S(X) := ∑_{n ≥ 0} X^n / (n+1)!`
(so `e^{X} = I + X · S(X)`). By `Matrix.charpoly_mul_comm`, `A · C` and
`C · A` have identical characteristic polynomials; shifting by the scalar
`p(1) · I` using `Matrix.charpoly_sub_scalar` preserves this equality.
Hence `p(e^{AB})` and `p(e^{BA})` have the same characteristic
polynomial, and for matrices over `ℝ` (an integral domain) nilpotence is
equivalent to the characteristic polynomial equaling `X^m`.
-/

namespace Imc2000P12

open Matrix NormedSpace

open scoped Matrix.Norms.Operator

section

variable {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ)

/-- `(AB)^n · A = A · (BA)^n` for every `n`. -/
lemma pow_mul_comm_cycle (n : ℕ) : (A * B) ^ n * A = A * (B * A) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
      calc (A * B) ^ (k + 1) * A
          = (A * B) ^ k * (A * B) * A := by rw [pow_succ]
        _ = (A * B) ^ k * A * (B * A) := by
              simp only [mul_assoc]
        _ = A * (B * A) ^ k * (B * A) := by rw [ih]
        _ = A * ((B * A) ^ k * (B * A)) := by rw [mul_assoc]
        _ = A * (B * A) ^ (k + 1) := by rw [← pow_succ]

/-- `B · (AB)^n = (BA)^n · B` for every `n`. -/
lemma mul_pow_comm_cycle (n : ℕ) : B * (A * B) ^ n = (B * A) ^ n * B := by
  induction n with
  | zero => simp
  | succ k ih =>
      calc B * (A * B) ^ (k + 1)
          = B * ((A * B) ^ k * (A * B)) := by rw [pow_succ]
        _ = B * (A * B) ^ k * (A * B) := by rw [mul_assoc]
        _ = (B * A) ^ k * B * (A * B) := by rw [ih]
        _ = (B * A) ^ k * (B * A) * B := by
              simp only [mul_assoc]
        _ = (B * A) ^ (k + 1) * B := by rw [← pow_succ]

/-- The matrix exponential intertwines: `e^{AB} · A = A · e^{BA}`. -/
lemma exp_mul_comm_cycle :
    NormedSpace.exp (A * B) * A = A * NormedSpace.exp (B * A) := by
  simp_rw [NormedSpace.exp_eq_tsum ℝ]
  have hsum₁ : Summable (fun n : ℕ => ((n.factorial : ℝ))⁻¹ • (A * B) ^ n) :=
    NormedSpace.expSeries_summable' (𝕂 := ℝ) (A * B)
  have hsum₂ : Summable (fun n : ℕ => ((n.factorial : ℝ))⁻¹ • (B * A) ^ n) :=
    NormedSpace.expSeries_summable' (𝕂 := ℝ) (B * A)
  rw [← hsum₁.tsum_mul_right, ← hsum₂.tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  rw [smul_mul_assoc, mul_smul_comm]
  congr 1
  exact pow_mul_comm_cycle A B n

/-- `B · e^{AB} = e^{BA} · B`. -/
lemma mul_exp_comm_cycle :
    B * NormedSpace.exp (A * B) = NormedSpace.exp (B * A) * B := by
  simp_rw [NormedSpace.exp_eq_tsum ℝ]
  have hsum₁ : Summable (fun n : ℕ => ((n.factorial : ℝ))⁻¹ • (A * B) ^ n) :=
    NormedSpace.expSeries_summable' (𝕂 := ℝ) (A * B)
  have hsum₂ : Summable (fun n : ℕ => ((n.factorial : ℝ))⁻¹ • (B * A) ^ n) :=
    NormedSpace.expSeries_summable' (𝕂 := ℝ) (B * A)
  rw [← hsum₁.tsum_mul_left, ← hsum₂.tsum_mul_right]
  refine tsum_congr (fun n => ?_)
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  exact mul_pow_comm_cycle A B n

/-- Polynomial version of the intertwining relation:
`r(e^{AB}) · A = A · r(e^{BA})` for any polynomial `r`. -/
lemma poly_exp_mul_comm_cycle (r : Polynomial ℝ) :
    (Polynomial.aeval (NormedSpace.exp (A * B))) r * A =
      A * (Polynomial.aeval (NormedSpace.exp (B * A))) r := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, add_mul, mul_add, hp, hq]
  | monomial n c =>
      -- aeval (X_0^n * C c) applied, simp gives algebraMap form.
      -- Alternative: break into two parts, scalar · (power).
      simp only [Polynomial.aeval_monomial]
      -- Goal: algebraMap c * exp(AB)^n * A = A * (algebraMap c * exp(BA)^n)
      -- algebraMap c commutes with everything.
      have halg : (algebraMap ℝ (Matrix (Fin m) (Fin m) ℝ)) c = c • 1 := by
        rw [Algebra.algebraMap_eq_smul_one]
      rw [halg, smul_one_mul, smul_mul_assoc, smul_one_mul, mul_smul_comm]
      congr 1
      -- Goal: exp(AB)^n * A = A * exp(BA)^n
      induction n with
      | zero => simp
      | succ k ih =>
          calc NormedSpace.exp (A * B) ^ (k + 1) * A
              = NormedSpace.exp (A * B) ^ k * NormedSpace.exp (A * B) * A := by rw [pow_succ]
            _ = NormedSpace.exp (A * B) ^ k * (NormedSpace.exp (A * B) * A) := by
                  rw [mul_assoc]
            _ = NormedSpace.exp (A * B) ^ k * (A * NormedSpace.exp (B * A)) := by
                  rw [exp_mul_comm_cycle]
            _ = NormedSpace.exp (A * B) ^ k * A * NormedSpace.exp (B * A) := by
                  rw [mul_assoc]
            _ = A * NormedSpace.exp (B * A) ^ k * NormedSpace.exp (B * A) := by rw [ih]
            _ = A * (NormedSpace.exp (B * A) ^ k * NormedSpace.exp (B * A)) := by
                  rw [mul_assoc]
            _ = A * NormedSpace.exp (B * A) ^ (k + 1) := by rw [← pow_succ]

end

/-- For an `m × m` matrix `M` over `ℝ`, `M` is nilpotent iff
`M.charpoly = X^m`. -/
lemma isNilpotent_iff_charpoly_eq_pow {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ) :
    IsNilpotent M ↔ M.charpoly = Polynomial.X ^ m := by
  constructor
  · intro hM
    have hnil : IsNilpotent (M.charpoly - Polynomial.X ^ (Fintype.card (Fin m))) :=
      Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hM
    have hzero : M.charpoly - Polynomial.X ^ (Fintype.card (Fin m)) = 0 :=
      IsNilpotent.eq_zero hnil
    have heq := sub_eq_zero.mp hzero
    rw [Fintype.card_fin] at heq
    exact heq
  · intro h
    refine ⟨m, ?_⟩
    have h2 := M.aeval_self_charpoly
    rw [h] at h2
    simpa using h2

/-- Scalar shift on characteristic polynomial: translate by the scalar matrix
`μ • 1`. -/
lemma charpoly_sub_scalar_smul {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (μ : ℝ) :
    (M - μ • (1 : Matrix (Fin m) (Fin m) ℝ)).charpoly =
      M.charpoly.comp (Polynomial.X + Polynomial.C μ) := by
  have h : μ • (1 : Matrix (Fin m) (Fin m) ℝ) = Matrix.scalar (Fin m) μ := by
    ext i j
    by_cases hij : i = j
    · simp [hij, Matrix.scalar_apply, Matrix.smul_apply]
    · simp [hij, Matrix.scalar_apply, Matrix.smul_apply]
  rw [h]
  exact Matrix.charpoly_sub_scalar M μ

section

variable {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ)

/-- The "half exponential" series `T(X) = ∑_{n ≥ 0} X^n / (n+1)!`. This
is summable and satisfies `exp(X) = I + X · T(X)`. -/
noncomputable def expShift : Matrix (Fin m) (Fin m) ℝ :=
  ∑' n : ℕ, (((n + 1).factorial : ℝ))⁻¹ • A ^ n

lemma summable_expShift :
    Summable (fun n : ℕ => (((n + 1).factorial : ℝ))⁻¹ • A ^ n) := by
  have hs : Summable (fun n : ℕ => ((n.factorial : ℝ))⁻¹ • A ^ n) :=
    NormedSpace.expSeries_summable' (𝕂 := ℝ) A
  -- Summability: bounded by summability of exp itself and `(n+1)!⁻¹ ≤ n!⁻¹`.
  -- Alternative: use `Summable.mul_left` then relate to `expSeries_summable'`.
  -- Use direct comparison: norm of `((n+1)!)⁻¹ • A^n` ≤ norm of `(n!)⁻¹ • A^n` (since `(n+1)! ≥ n!` so `((n+1)!)⁻¹ ≤ n!⁻¹`, and norm scales by abs).
  -- But let's just use summable_of_absolute_summable pattern.
  -- Actually simplest: shift index. The shifted `n ↦ ((n+1)!)⁻¹ • A^(n+1)` is summable
  -- (by `summable_nat_add_iff`), then undo the shift and compare with summable of the power series.
  have hshift : Summable (fun n : ℕ => (((n + 1).factorial : ℝ))⁻¹ • A ^ (n + 1)) := by
    have := (summable_nat_add_iff (f := fun n : ℕ => ((n.factorial : ℝ))⁻¹ • A ^ n)
              (k := 1)).mpr hs
    simpa using this
  -- Factor A out: `((n+1)!)⁻¹ • A^(n+1) = A * (((n+1)!)⁻¹ • A^n)`.
  -- Then multiplication by A is bounded linear.
  -- Use `Summable.of_norm_bounded_eventually` with pointwise bound.
  have hbound : ∀ n, ‖(((n + 1).factorial : ℝ))⁻¹ • A ^ n‖
                  ≤ (n.factorial : ℝ)⁻¹ * ‖A ^ n‖ := by
    intro n
    rw [norm_smul]
    gcongr
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    exact_mod_cast Nat.factorial_le (Nat.le_succ _)
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound ?_ |>.of_norm
  have hs' : Summable (fun n : ℕ => ((n.factorial : ℝ))⁻¹ * ‖A ^ n‖) := by
    have := NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) A
    simpa [norm_smul, Real.norm_eq_abs, abs_of_pos, Nat.factorial_pos]
      using this
  exact hs'

/-- `exp(AB) = I + (AB) · expShift(AB)`. Equivalently `exp(AB) - I = AB · expShift(AB)`. -/
lemma exp_eq_one_add_mul_expShift :
    NormedSpace.exp A = 1 + A * expShift A := by
  -- Use the tsum expansion and split off n = 0.
  have hs : Summable (fun n : ℕ => ((n.factorial : ℝ))⁻¹ • A ^ n) :=
    NormedSpace.expSeries_summable' (𝕂 := ℝ) A
  rw [show NormedSpace.exp A = ∑' n : ℕ, ((n.factorial : ℝ))⁻¹ • A ^ n by
    rw [NormedSpace.exp_eq_tsum ℝ]]
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul]
  congr 1
  -- Goal: ∑' n, ((n+1)!)⁻¹ • A^(n+1) = A * expShift A
  unfold expShift
  have hsum_shift : Summable (fun n : ℕ => (((n + 1).factorial : ℝ))⁻¹ • A ^ n) :=
    summable_expShift A
  rw [← hsum_shift.tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  rw [pow_succ', mul_smul_comm]

/-- `(AB)^n · A = A · (BA)^n` implies `expShift(AB) · A = A · expShift(BA)`. -/
lemma expShift_mul_comm_cycle :
    expShift (A * B) * A = A * expShift (B * A) := by
  unfold expShift
  have hs1 := summable_expShift (A * B)
  have hs2 := summable_expShift (B * A)
  rw [← hs1.tsum_mul_right, ← hs2.tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  rw [smul_mul_assoc, mul_smul_comm]
  congr 1
  exact pow_mul_comm_cycle A B n

end

/-- The main statement: `p(e^{AB})` is nilpotent iff `p(e^{BA})` is. -/
problem imc2000_p12 (m : ℕ) (p : Polynomial ℝ) (A B : Matrix (Fin m) (Fin m) ℝ) :
    IsNilpotent ((Polynomial.aeval (NormedSpace.exp (A * B))) p) ↔
      IsNilpotent ((Polynomial.aeval (NormedSpace.exp (B * A))) p) := by
  suffices hcharpoly :
      ((Polynomial.aeval (NormedSpace.exp (A * B))) p).charpoly =
        ((Polynomial.aeval (NormedSpace.exp (B * A))) p).charpoly by
    rw [isNilpotent_iff_charpoly_eq_pow, isNilpotent_iff_charpoly_eq_pow, hcharpoly]
  -- Factor p(y) - p(1) = (y - 1) * r(y) for some polynomial r.
  have hfactor : ∃ r : Polynomial ℝ,
      p - Polynomial.C (p.eval 1) =
        (Polynomial.X - Polynomial.C 1) * r := by
    have h1 : (p - Polynomial.C (p.eval 1)).eval 1 = 0 := by simp
    obtain ⟨r, hr⟩ := Polynomial.dvd_iff_isRoot.mpr h1
    exact ⟨r, hr⟩
  obtain ⟨r, hr⟩ := hfactor
  -- Define matrix C so that p(exp(AB)) = p(1)·I + A·C and p(exp(BA)) = p(1)·I + C·A.
  set expAB := NormedSpace.exp (A * B) with hexpAB_def
  set expBA := NormedSpace.exp (B * A) with hexpBA_def
  -- C = B * expShift(AB) * r(exp(AB))
  set C : Matrix (Fin m) (Fin m) ℝ :=
    B * expShift (A * B) * (Polynomial.aeval expAB) r with hC_def
  -- Decompose p = C(p(1)) + (X - 1) * r.
  have hp_decomp : p = Polynomial.C (p.eval 1) + (Polynomial.X - Polynomial.C 1) * r := by
    linear_combination hr
  -- Step 1: p(exp(AB)) = p(1) • 1 + A * C.
  have h_eq_AB : (Polynomial.aeval expAB) p = (p.eval 1) • 1 + A * C := by
    conv_lhs => rw [hp_decomp]
    simp only [map_add, map_mul, map_sub, Polynomial.aeval_C, Polynomial.aeval_X,
               Algebra.algebraMap_eq_smul_one]
    -- Goal: (p.eval 1) • 1 + (expAB - 1 • 1) * r(expAB) = (p.eval 1) • 1 + A * C
    congr 1
    -- Goal: (expAB - 1 • 1) * r(expAB) = A * C
    rw [one_smul, hC_def, ← mul_assoc, ← mul_assoc]
    -- A * B * expShift(AB) * r(expAB)
    congr 1
    -- Goal: expAB - 1 = A * B * expShift(AB)
    rw [hexpAB_def, exp_eq_one_add_mul_expShift, add_sub_cancel_left]
  -- Step 2: p(exp(BA)) = p(1) • 1 + C * A.
  have h_eq_BA : (Polynomial.aeval expBA) p = (p.eval 1) • 1 + C * A := by
    conv_lhs => rw [hp_decomp]
    simp only [map_add, map_mul, map_sub, Polynomial.aeval_C, Polynomial.aeval_X,
               Algebra.algebraMap_eq_smul_one]
    congr 1
    rw [one_smul, hC_def]
    -- Goal: (expBA - 1) * r(expBA) = B * expShift(AB) * r(expAB) * A
    -- Use intertwining to move A to rightmost: r(expAB) * A = A * r(expBA)
    rw [mul_assoc (B * expShift (A * B)) ((Polynomial.aeval expAB) r) A]
    have h1 : (Polynomial.aeval expAB) r * A = A * (Polynomial.aeval expBA) r := by
      rw [hexpAB_def, hexpBA_def]
      exact poly_exp_mul_comm_cycle A B r
    rw [h1]
    -- Goal: (expBA - 1) * r(expBA) = B * expShift(AB) * (A * r(expBA))
    -- Use expShift(AB) * A = A * expShift(BA).
    rw [← mul_assoc (B * expShift (A * B)) A ((Polynomial.aeval expBA) r)]
    rw [mul_assoc B (expShift (A * B)) A, expShift_mul_comm_cycle]
    -- Goal: (expBA - 1) * r(expBA) = B * (A * expShift(BA)) * r(expBA)
    rw [show B * (A * expShift (B * A)) = B * A * expShift (B * A) by
        rw [← mul_assoc]]
    congr 1
    rw [hexpBA_def, exp_eq_one_add_mul_expShift]
    rw [add_sub_cancel_left]
  -- Step 3: charpoly of both sides are equal.
  rw [h_eq_AB, h_eq_BA]
  -- charpoly((p.eval 1) • 1 + A * C) = charpoly((p.eval 1) • 1 + C * A)
  have hAC : (A * C - (- (p.eval 1)) • (1 : Matrix (Fin m) (Fin m) ℝ)).charpoly =
             (A * C).charpoly.comp (Polynomial.X + Polynomial.C (- (p.eval 1))) :=
    charpoly_sub_scalar_smul _ _
  have hCA : (C * A - (- (p.eval 1)) • (1 : Matrix (Fin m) (Fin m) ℝ)).charpoly =
             (C * A).charpoly.comp (Polynomial.X + Polynomial.C (- (p.eval 1))) :=
    charpoly_sub_scalar_smul _ _
  have hAC_CA : (A * C).charpoly = (C * A).charpoly := Matrix.charpoly_mul_comm A C
  have key_AC : (A * C - (- (p.eval 1)) • (1 : Matrix (Fin m) (Fin m) ℝ)).charpoly =
                 (C * A - (- (p.eval 1)) • (1 : Matrix (Fin m) (Fin m) ℝ)).charpoly := by
    rw [hAC, hCA, hAC_CA]
  have rewrite_AC : (p.eval 1) • (1 : Matrix (Fin m) (Fin m) ℝ) + A * C =
                    A * C - (- (p.eval 1)) • (1 : Matrix (Fin m) (Fin m) ℝ) := by
    rw [neg_smul, sub_neg_eq_add, add_comm]
  have rewrite_CA : (p.eval 1) • (1 : Matrix (Fin m) (Fin m) ℝ) + C * A =
                    C * A - (- (p.eval 1)) • (1 : Matrix (Fin m) (Fin m) ℝ) := by
    rw [neg_smul, sub_neg_eq_add, add_comm]
  rw [rewrite_AC, rewrite_CA]
  exact key_AC

end Imc2000P12
