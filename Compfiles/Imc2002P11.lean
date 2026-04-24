/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Roots

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2002, Problem 11
(IMC 2002, Day 2, Problem 5)

Let `A` be an `n × n` complex matrix, `n > 1`. Show that
  `A * bar(A) = I  ↔  ∃ S invertible with A = S * bar(S)⁻¹`,
where `bar(M)` denotes entry-wise complex conjugation.

## Solution outline

(⇐) If `A = S * bar(S)⁻¹` then `A * bar(A) = S * bar(S)⁻¹ * bar(S) * S⁻¹ = I`.

(⇒) We seek `S` with `A * bar(S) = S`. Try `S = w • A + conj w • I` for some
`w ∈ ℂ`. Then
  `A * bar(S) = A * (conj w • bar(A) + w • I)`
             `= conj w • (A * bar(A)) + w • A`
             `= conj w • I + w • A = S`.
So we need `S` invertible for some `w`. Now `det(w • A + conj w • I)`, viewed as a
function of `w ∈ ℂ \ {0}` via `w = e^{iθ}`, becomes (up to a unit) `det(A + λ I)`
where `λ = conj w / w` ranges over the unit circle. Since `A` has at most `n`
eigenvalues, some unit `λ` is not the negative of an eigenvalue of `A`, hence
some `w` gives invertible `S`.
-/

namespace Imc2002P11

open Matrix

/-- The entrywise complex conjugate of a complex matrix. -/
noncomputable abbrev cbar {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  A.map (starRingEnd ℂ)

@[simp]
lemma cbar_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    cbar A i j = (starRingEnd ℂ) (A i j) := rfl

@[simp]
lemma cbar_one {n : ℕ} : cbar (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext i j
  set_option linter.unusedSimpArgs false in
  by_cases h : i = j
  · simp [cbar, Matrix.one_apply, h]
  · simp [cbar, Matrix.one_apply, h]

@[simp]
lemma cbar_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    cbar (A * B) = cbar A * cbar B := by
  ext i j
  simp [cbar, Matrix.mul_apply, map_sum, map_mul]

@[simp]
lemma cbar_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    cbar (A + B) = cbar A + cbar B := by
  ext i j; simp [cbar]

@[simp]
lemma cbar_smul {n : ℕ} (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    cbar (c • A) = (starRingEnd ℂ) c • cbar A := by
  ext i j; simp [cbar]

@[simp]
lemma cbar_cbar {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : cbar (cbar A) = A := by
  ext i j; simp [cbar]

/-- If `A * cbar A = I`, then `A` is invertible with inverse `cbar A`. -/
lemma isUnit_of_mul_cbar {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A * cbar A = 1) : IsUnit A := by
  refine (Matrix.isUnit_iff_isUnit_det A).mpr ?_
  have h1 : A.det * (cbar A).det = 1 := by
    rw [← Matrix.det_mul, hA, Matrix.det_one]
  exact IsUnit.of_mul_eq_one _ h1

snip begin

/-- `cbar` of an inverse equals the inverse of `cbar`. -/
lemma cbar_inv {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) :
    cbar S⁻¹ = (cbar S)⁻¹ := by
  have h2 : cbar S⁻¹ * cbar S = 1 := by
    rw [← cbar_mul]
    rw [Matrix.nonsing_inv_mul]
    · exact cbar_one
    · exact (Matrix.isUnit_iff_isUnit_det S).mp hS
  exact (Matrix.inv_eq_left_inv h2).symm

/-- Given `A * cbar A = I`, the matrix `S = w • A + conj w • I` satisfies
`A * cbar S = S`. -/
lemma A_mul_cbar_S_eq_S {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A * cbar A = 1) (w : ℂ) :
    A * cbar (w • A + (starRingEnd ℂ) w • (1 : Matrix (Fin n) (Fin n) ℂ)) =
      w • A + (starRingEnd ℂ) w • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have hbar : cbar (w • A + (starRingEnd ℂ) w • (1 : Matrix (Fin n) (Fin n) ℂ)) =
      (starRingEnd ℂ) w • cbar A + w • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [cbar_add, cbar_smul, cbar_smul, cbar_one]
    simp
  rw [hbar, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, hA,
    add_comm]

/-- The unit circle in `ℂ` is infinite. -/
lemma unit_circle_infinite : Set.Infinite {z : ℂ | ‖z‖ = 1} := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => Complex.exp (Complex.I * ((1 : ℂ) / (n + 1))))
  · intro a b hab
    dsimp at hab
    rw [Complex.exp_eq_exp_iff_exists_int] at hab
    obtain ⟨k, hk⟩ := hab
    -- I * (1/(a+1)) = I * (1/(b+1)) + k * (2π I).
    -- Multiply both sides by -I: 1/(a+1) = 1/(b+1) + k * 2π.
    have hk' : (1 : ℂ) / (a + 1) = 1 / (b + 1) + (k : ℂ) * (2 * Real.pi) := by
      have hI : Complex.I ≠ 0 := Complex.I_ne_zero
      have h1 : Complex.I * ((1 : ℂ) / (↑a + 1)) =
          Complex.I * (1 / (↑b + 1) + (k : ℂ) * (2 * Real.pi)) := by
        rw [hk]; ring
      exact mul_left_cancel₀ hI h1
    -- Take real part: 1/(a+1) - 1/(b+1) = k * 2π.
    have hk'' : ((1 : ℝ) / (↑a + 1)) - (1 / (↑b + 1)) = (k : ℝ) * (2 * Real.pi) := by
      have h := congrArg Complex.re hk'
      have h_pa : ((1 : ℂ) / ((a : ℂ) + 1)).re = 1 / ((a : ℝ) + 1) := by
        have : ((1 : ℂ) / ((a : ℂ) + 1)) = (((1 : ℝ) / ((a : ℝ) + 1) : ℝ) : ℂ) := by
          rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_add,
              Complex.ofReal_natCast, Complex.ofReal_one]
        rw [this, Complex.ofReal_re]
      have h_pb : ((1 : ℂ) / ((b : ℂ) + 1)).re = 1 / ((b : ℝ) + 1) := by
        have : ((1 : ℂ) / ((b : ℂ) + 1)) = (((1 : ℝ) / ((b : ℝ) + 1) : ℝ) : ℂ) := by
          rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_add,
              Complex.ofReal_natCast, Complex.ofReal_one]
        rw [this, Complex.ofReal_re]
      rw [Complex.add_re] at h
      rw [h_pa, h_pb] at h
      simp [Complex.mul_re, Complex.mul_im] at h
      rw [show ((1 : ℝ) / ((a : ℝ) + 1)) = ((a : ℝ) + 1)⁻¹ from one_div _,
          show ((1 : ℝ) / ((b : ℝ) + 1)) = ((b : ℝ) + 1)⁻¹ from one_div _]
      linarith
    -- LHS is in (-1, 1), so if k ≠ 0, |k * 2π| ≥ 2π > 6, contradiction.
    rcases eq_or_ne k 0 with hk0 | hk0
    · rw [hk0] at hk''
      push_cast at hk''
      have h1 : (1 : ℝ) / (↑a + 1) = 1 / (↑b + 1) := by linarith
      have ha1 : ((a : ℝ) + 1) ≠ 0 := by positivity
      have hb1 : ((b : ℝ) + 1) ≠ 0 := by positivity
      have : (↑a + 1 : ℝ) = (↑b + 1) := by
        rw [div_eq_div_iff ha1 hb1] at h1
        linarith
      have : (a : ℝ) = (b : ℝ) := by linarith
      exact_mod_cast this
    · exfalso
      have hlhs_bd : |(1 : ℝ) / (↑a + 1) - 1 / (↑b + 1)| < 2 := by
        have ha_pos : (0 : ℝ) < (a : ℝ) + 1 := by positivity
        have hb_pos : (0 : ℝ) < (b : ℝ) + 1 := by positivity
        have ha_bd : (1 : ℝ) / (↑a + 1) ≤ 1 := by
          rw [div_le_one ha_pos]
          have : (0 : ℝ) ≤ a := by positivity
          linarith
        have hb_bd : (1 : ℝ) / (↑b + 1) ≤ 1 := by
          rw [div_le_one hb_pos]
          have : (0 : ℝ) ≤ b := by positivity
          linarith
        have ha_pos2 : (0 : ℝ) < 1 / (↑a + 1) := by positivity
        have hb_pos2 : (0 : ℝ) < 1 / (↑b + 1) := by positivity
        rw [abs_sub_lt_iff]
        constructor <;> linarith
      have hrhs_bd : (2 * Real.pi) ≤ |(k : ℝ) * (2 * Real.pi)| := by
        rw [abs_mul]
        have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
          have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
          exact_mod_cast this
        have h2 : (0 : ℝ) ≤ |2 * Real.pi| := abs_nonneg _
        have h3 : |2 * Real.pi| = 2 * Real.pi := abs_of_pos (by linarith [Real.pi_pos])
        rw [h3]
        have h4 : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
        nlinarith
      have : |(k : ℝ) * (2 * Real.pi)| < 2 := by
        rw [← hk'']; exact hlhs_bd
      have h_bd : 2 * Real.pi < 2 := lt_of_le_of_lt hrhs_bd this
      linarith [Real.pi_gt_three]
  · intro a
    show ‖Complex.exp (Complex.I * ((1 : ℂ) / (a + 1)))‖ = 1
    rw [show (Complex.I * ((1 : ℂ) / (↑a + 1))) =
      (((1 : ℝ) / (↑a + 1) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _

/-- Existence of `w` making `w • A + conj w • I` invertible.
Using that `A` has at most `n` eigenvalues and the unit circle is infinite. -/
lemma exists_w_nonsing {n : ℕ} (_hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ w : ℂ, IsUnit (w • A + (starRingEnd ℂ) w • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  -- Let `p = charpoly (-A)`. We have `p.eval u = det(u • 1 + A)`. `p` is monic,
  -- hence nonzero, so its root set is finite. The unit circle is infinite, so
  -- there exists a unit `u` with `p.eval u ≠ 0`. Pick `v = u ^ (1/2 : ℂ)` a
  -- square root of `u` (also of norm 1). Set `w = v⁻¹` (nonzero). Then
  -- `conj w = conj v⁻¹ = (conj v)⁻¹ = v` (since `|v| = 1`), so `conj w / w = v / v⁻¹ = v^2 = u`.
  -- Finally `det(w • A + conj w • 1) = w^n * det(A + u • 1) = w^n * p.eval u ≠ 0`.
  let p := (-A).charpoly
  have hp_ne : p ≠ 0 := (-A).charpoly_monic.ne_zero
  have hp_fin : Set.Finite {x : ℂ | Polynomial.IsRoot p x} :=
    Polynomial.finite_setOf_isRoot hp_ne
  have hcircle : Set.Infinite {z : ℂ | ‖z‖ = 1} := unit_circle_infinite
  -- Hence {z : ‖z‖ = 1} \ {x : IsRoot p x} is nonempty.
  have hdiff : ({z : ℂ | ‖z‖ = 1} \ {x | Polynomial.IsRoot p x}).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    apply hcircle
    have : {z : ℂ | ‖z‖ = 1} ⊆ {x | Polynomial.IsRoot p x} := by
      intro z hz
      by_contra hzr
      exact Set.eq_empty_iff_forall_notMem.mp h z ⟨hz, hzr⟩
    exact hp_fin.subset this
  obtain ⟨u, hu_circle, hu_not_root⟩ := hdiff
  -- u is a unit complex number, not a root of p.
  change ‖u‖ = 1 at hu_circle
  change ¬ Polynomial.IsRoot p u at hu_not_root
  -- Let v be a square root of u (with `v = u ^ (1/2 : ℂ)` via Complex.cpow or
  -- Complex.exp (log u / 2)).
  have hu_ne : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu_circle; norm_num at hu_circle
  set v : ℂ := Complex.exp (Complex.log u / 2) with hv_def
  have hv_sq : v ^ 2 = u := by
    rw [hv_def, ← Complex.exp_nat_mul]
    push_cast
    rw [show (2 : ℂ) * (Complex.log u / 2) = Complex.log u by ring,
        Complex.exp_log hu_ne]
  have hv_ne : v ≠ 0 := Complex.exp_ne_zero _
  have hv_norm : ‖v‖ = 1 := by
    have h1 : ‖v‖^2 = 1 := by
      rw [← norm_pow, hv_sq, hu_circle]
    nlinarith [norm_nonneg v, h1]
  -- w = v⁻¹
  set w : ℂ := v⁻¹ with hw_def
  have hw_ne : w ≠ 0 := inv_ne_zero hv_ne
  -- Key relation: conj w / w = u.
  have h_conj_v : (starRingEnd ℂ) v = v⁻¹ := (Complex.inv_eq_conj hv_norm).symm
  have h_conj_w : (starRingEnd ℂ) w = v := by
    rw [hw_def, map_inv₀, h_conj_v, inv_inv]
  -- Show det(w • A + conj w • 1) ≠ 0.
  refine ⟨w, ?_⟩
  refine (Matrix.isUnit_iff_isUnit_det _).mpr ?_
  rw [isUnit_iff_ne_zero]
  -- det(w • A + conj w • 1) = det(v⁻¹ • A + v • 1) = v^(-n) * det(A + v^2 • 1)
  --                         = v^(-n) * det(A + u • 1) = v^(-n) * p.eval u ≠ 0.
  have hp_eval : p.eval u = (A + u • (1 : Matrix (Fin n) (Fin n) ℂ)).det := by
    rw [show p = (-A).charpoly from rfl, Matrix.eval_charpoly]
    congr 1
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal, Matrix.one_apply]
    by_cases h : i = j <;> simp [h]
    ring
  have hdet : (w • A + (starRingEnd ℂ) w • (1 : Matrix (Fin n) (Fin n) ℂ)).det
      = w^n * (A + u • (1 : Matrix (Fin n) (Fin n) ℂ)).det := by
    rw [h_conj_w]
    -- w • A + v • 1 = w • (A + w⁻¹ • v • 1) = w • (A + v^2 • 1) = w • (A + u • 1)
    have : w • A + v • (1 : Matrix (Fin n) (Fin n) ℂ) =
        w • (A + u • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
      rw [hw_def, smul_add, smul_smul]
      congr 1
      -- Goal: v • 1 = (v⁻¹ * u) • 1
      have hcoef : v = v⁻¹ * u := by
        have : v⁻¹ * u = v⁻¹ * v^2 := by rw [hv_sq]
        rw [this, sq]
        field_simp
      conv_lhs => rw [hcoef]
    rw [this, Matrix.det_smul]
    simp [Fintype.card_fin]
  rw [hdet]
  rw [← hp_eval]
  have hw_n_ne : w^n ≠ 0 := pow_ne_zero _ hw_ne
  exact mul_ne_zero hw_n_ne hu_not_root

snip end

problem imc2002_p11 {n : ℕ} (hn : 1 < n) (A : Matrix (Fin n) (Fin n) ℂ) :
    A * cbar A = 1 ↔
      ∃ S : Matrix (Fin n) (Fin n) ℂ, IsUnit S ∧ A = S * (cbar S)⁻¹ := by
  constructor
  · intro hA
    obtain ⟨w, hw⟩ := exists_w_nonsing (le_of_lt hn) A
    refine ⟨w • A + (starRingEnd ℂ) w • (1 : Matrix (Fin n) (Fin n) ℂ), hw, ?_⟩
    -- A * cbar S = S, so A = S * (cbar S)⁻¹
    have hS : A * cbar (w • A + (starRingEnd ℂ) w • (1 : Matrix (Fin n) (Fin n) ℂ))
        = w • A + (starRingEnd ℂ) w • (1 : Matrix (Fin n) (Fin n) ℂ) :=
      A_mul_cbar_S_eq_S hA w
    -- S_inv := cbar S is invertible since S is invertible.
    have hcbar_unit :
        IsUnit (cbar (w • A + (starRingEnd ℂ) w • (1 : Matrix (Fin n) (Fin n) ℂ))) := by
      apply (Matrix.isUnit_iff_isUnit_det _).mpr
      have : (cbar (w • A + (starRingEnd ℂ) w •
          (1 : Matrix (Fin n) (Fin n) ℂ))).det =
          (starRingEnd ℂ) (w • A + (starRingEnd ℂ) w •
            (1 : Matrix (Fin n) (Fin n) ℂ)).det := by
        rw [(starRingEnd ℂ).map_det]
        rfl
      rw [this]
      rcases (Matrix.isUnit_iff_isUnit_det _).mp hw with ⟨u, hu⟩
      exact ⟨((Units.map (starRingEnd ℂ).toMonoidHom) u), by simp [← hu]⟩
    -- From hS: A * cbar S = S. Multiply on the right by (cbar S)⁻¹:
    -- A = S * (cbar S)⁻¹.
    have := congrArg (fun X => X * (cbar (w • A + (starRingEnd ℂ) w •
        (1 : Matrix (Fin n) (Fin n) ℂ)))⁻¹) hS
    simp only at this
    rw [Matrix.mul_assoc] at this
    rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hcbar_unit),
      Matrix.mul_one] at this
    exact this
  · rintro ⟨S, hS, rfl⟩
    -- A = S * (cbar S)⁻¹
    -- A * cbar A = S * (cbar S)⁻¹ * cbar (S * (cbar S)⁻¹)
    --            = S * (cbar S)⁻¹ * (cbar S * (cbar (cbar S))⁻¹)
    --            = S * (cbar S)⁻¹ * (cbar S * S⁻¹)
    --            = S * S⁻¹ = 1.
    have hcbarS_unit : IsUnit (cbar S) := by
      apply (Matrix.isUnit_iff_isUnit_det _).mpr
      have : (cbar S).det = (starRingEnd ℂ) S.det := by
        rw [(starRingEnd ℂ).map_det]
        rfl
      rw [this]
      rcases (Matrix.isUnit_iff_isUnit_det _).mp hS with ⟨u, hu⟩
      exact ⟨((Units.map (starRingEnd ℂ).toMonoidHom) u), by simp [← hu]⟩
    have hcbar_inv : cbar S⁻¹ = (cbar S)⁻¹ := cbar_inv S hS
    rw [cbar_mul]
    have hinv_cbar : cbar ((cbar S)⁻¹) = S⁻¹ := by
      rw [← hcbar_inv, cbar_cbar]
    rw [hinv_cbar]
    -- Goal: (S * (cbar S)⁻¹) * (cbar S * S⁻¹) = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((cbar S)⁻¹) (cbar S) S⁻¹,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hcbarS_unit),
      Matrix.one_mul,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hS)]

end Imc2002P11
