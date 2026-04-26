/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1997, Problem 3 (Day 1)

Let `A` and `B` be real `n × n` matrices such that `A² + B² = A * B`. Prove
that if `B * A - A * B` is invertible then `n` is divisible by `3`.

## Solution outline (official)

Work over `ℂ`. Let `ω = (-1 + i √3) / 2`, a primitive cube root of unity, so
`ω² + ω + 1 = 0`, `ω³ = 1`, and `conj ω = ω²`. Set `S = A + ω • B` (with
entries in `ℂ`). Then

  `S * conj(S) = (A + ω B)(A + ω² B) = A² + B² + ω² A B + ω B A`
              `= A B + ω² A B + ω B A`
              `= (1 + ω²) A B + ω B A`
              `= -ω A B + ω B A = ω · (B A - A B)`.

Taking determinants, `det S * det (conj S) = ωⁿ · det (B A - A B)`. The LHS
is `|det S|² ∈ ℝ`, while `det (B A - A B)` is a non-zero real. Hence `ωⁿ`
is real. Since `ω` has order `3`, this forces `3 ∣ n`.
-/

namespace Imc1997P3

open scoped Matrix
open Matrix Complex

/-- A primitive cube root of unity: `ω = (-1 + i √3) / 2`. -/
noncomputable def ω : ℂ := (-1 + Complex.I * Real.sqrt 3) / 2

/-- Entrywise complex-conjugation on a complex matrix. -/
noncomputable abbrev cbar {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  M.map (starRingEnd ℂ)

/-- The lift of a real matrix to a complex matrix. -/
noncomputable abbrev liftR {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  M.map ((algebraMap ℝ ℂ : ℝ →+* ℂ))

snip begin

lemma sq_sqrt_three : Real.sqrt 3 ^ 2 = 3 := by
  rw [sq]
  exact Real.mul_self_sqrt (by norm_num)

/-- `ω² + ω + 1 = 0`. -/
lemma ω_quadratic : ω ^ 2 + ω + 1 = 0 := by
  unfold ω
  have h3 : ((Real.sqrt 3 : ℂ)) ^ 2 = 3 := by
    rw [show ((Real.sqrt 3 : ℂ)) ^ 2 = ((Real.sqrt 3 ^ 2 : ℝ) : ℂ) by push_cast; ring]
    rw [sq_sqrt_three]; push_cast; ring
  field_simp
  ring_nf
  rw [show (Complex.I) ^ 2 = -1 from Complex.I_sq]
  rw [h3]
  ring

/-- `ω³ = 1`. -/
lemma ω_cubed : ω ^ 3 = 1 := by
  have h := ω_quadratic
  linear_combination (ω - 1) * h

/-- `1 + ω² = -ω`, equivalent restatement of the quadratic relation. -/
lemma one_add_ω_sq : 1 + ω ^ 2 = -ω := by
  linear_combination ω_quadratic

/-- `ω` is non-zero. -/
lemma ω_ne_zero : ω ≠ 0 := by
  intro h
  have := ω_cubed
  rw [h] at this
  norm_num at this

/-- `conj ω = ω²`. Equivalently, `conj ω · ω = 1`. -/
lemma conj_ω : (starRingEnd ℂ) ω = ω ^ 2 := by
  unfold ω
  -- conj((-1 + i√3)/2) = (-1 - i√3)/2.
  -- And ω² = ((-1 + i√3)/2)² = (1 - 2i√3 - 3)/4 = (-2 - 2i√3)/4 = (-1 - i√3)/2.
  have h3 : ((Real.sqrt 3 : ℂ)) ^ 2 = 3 := by
    rw [show ((Real.sqrt 3 : ℂ)) ^ 2 = ((Real.sqrt 3 ^ 2 : ℝ) : ℂ) by push_cast; ring]
    rw [sq_sqrt_three]; push_cast; ring
  apply Complex.ext
  · simp [Complex.div_re, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.one_re,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.normSq, pow_two]
    have : Real.sqrt 3 * Real.sqrt 3 = 3 := by
      rw [← sq]; exact sq_sqrt_three
    nlinarith [this]
  · simp [Complex.div_im, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
      Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq, pow_two]
    have : Real.sqrt 3 * Real.sqrt 3 = 3 := by
      rw [← sq]; exact sq_sqrt_three
    nlinarith [this]

/-- For natural number `m`, `ω ^ m` depends only on `m % 3`. In particular,
`ω ^ m ∈ ℝ` iff `m % 3 = 0` iff `3 ∣ m`. -/
lemma ω_pow_eq_pow_mod (m : ℕ) : ω ^ m = ω ^ (m % 3) := by
  conv_lhs => rw [← Nat.div_add_mod m 3]
  rw [pow_add, pow_mul, ω_cubed, one_pow, one_mul]

/-- `ω` is non-real. -/
lemma ω_im_ne_zero : ω.im ≠ 0 := by
  have h : ω.im = Real.sqrt 3 / 2 := by
    unfold ω
    show ((-1 + Complex.I * Real.sqrt 3) / 2).im = Real.sqrt 3 / 2
    rw [Complex.div_im]
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.neg_im, Complex.one_im,
      Complex.normSq]
    ring
  rw [h]
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3)
  positivity

/-- `ω²` is non-real. -/
lemma ω_sq_im_ne_zero : (ω ^ 2).im ≠ 0 := by
  rw [← conj_ω]
  show -ω.im ≠ 0
  intro h
  exact ω_im_ne_zero (by linarith)

/-- The key step: `ω ^ m` is real iff `3 ∣ m`. -/
lemma ω_pow_isReal_iff (m : ℕ) : (ω ^ m).im = 0 ↔ 3 ∣ m := by
  constructor
  · intro h
    rw [ω_pow_eq_pow_mod m] at h
    have hmod : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases this with h0 | h1 | h2
    · exact Nat.dvd_of_mod_eq_zero h0
    · rw [h1, pow_one] at h
      exact absurd h ω_im_ne_zero
    · rw [h2] at h
      exact absurd h ω_sq_im_ne_zero
  · intro h
    obtain ⟨k, rfl⟩ := h
    rw [pow_mul, ω_cubed, one_pow]
    simp

@[simp]
lemma liftR_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    liftR (A + B) = liftR A + liftR B := by
  ext i j; simp [liftR]

@[simp]
lemma liftR_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    liftR (A * B) = liftR A * liftR B := by
  ext i j
  simp only [liftR, Matrix.map_apply, Matrix.mul_apply]
  push_cast
  rfl

@[simp]
lemma liftR_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    liftR (A - B) = liftR A - liftR B := by
  ext i j; simp [liftR]

@[simp]
lemma cbar_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    cbar (A + B) = cbar A + cbar B := by
  ext i j; simp [cbar]

@[simp]
lemma cbar_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    cbar (A * B) = cbar A * cbar B := by
  ext i j
  simp [cbar, Matrix.mul_apply, map_sum, map_mul]

@[simp]
lemma cbar_smul {n : ℕ} (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    cbar (c • A) = (starRingEnd ℂ) c • cbar A := by
  ext i j; simp [cbar]

@[simp]
lemma cbar_liftR {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    cbar (liftR A) = liftR A := by
  ext i j
  simp [cbar, liftR]

/-- Determinant of `cbar M` is the conjugate of `det M`. -/
lemma det_cbar {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    (cbar M).det = (starRingEnd ℂ) M.det :=
  ((starRingEnd ℂ).map_det M).symm

/-- Determinant of `liftR M` is the cast of `det M`. -/
lemma det_liftR {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (liftR M).det = ((M.det : ℝ) : ℂ) :=
  ((algebraMap ℝ ℂ : ℝ →+* ℂ).map_det M).symm

/-- The S-matrix algebraic identity:
`S * cbar S = ω • (liftR (B*A) - liftR (A*B))`, given `A² + B² = A * B`. -/
lemma S_mul_cbarS {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hAB : A * A + B * B = A * B) :
    (liftR A + ω • liftR B) * cbar (liftR A + ω • liftR B)
      = ω • (liftR (B * A) - liftR (A * B)) := by
  have hcbarS : cbar (liftR A + ω • liftR B)
      = liftR A + (starRingEnd ℂ) ω • liftR B := by
    rw [cbar_add, cbar_smul, cbar_liftR, cbar_liftR]
  rw [hcbarS]
  -- Set Ac := liftR A, Bc := liftR B, w := ω, w' := conj ω.
  set Ac : Matrix (Fin n) (Fin n) ℂ := liftR A with hAc
  set Bc : Matrix (Fin n) (Fin n) ℂ := liftR B with hBc
  set w := ω
  set w' := (starRingEnd ℂ) ω
  -- Key facts about w, w':
  have hww' : w * w' = 1 := by
    show ω * (starRingEnd ℂ) ω = 1
    rw [conj_ω]
    have : ω * ω ^ 2 = ω ^ 3 := by ring
    rw [this, ω_cubed]
  have h1w' : (1 + w') = -w := by
    show 1 + (starRingEnd ℂ) ω = -ω
    rw [conj_ω]; linear_combination one_add_ω_sq
  -- A² + B² = AB lifted:
  have hlift_id : Ac * Ac + Bc * Bc = Ac * Bc := by
    show liftR A * liftR A + liftR B * liftR B = liftR A * liftR B
    rw [← liftR_mul, ← liftR_mul, ← liftR_add, ← liftR_mul, hAB]
  have hw'w : w' * w = 1 := by rw [mul_comm]; exact hww'
  -- Expand (Ac + w • Bc) * (Ac + w' • Bc):
  have expand : (Ac + w • Bc) * (Ac + w' • Bc)
      = (Ac * Ac + Bc * Bc) + w' • (Ac * Bc) + w • (Bc * Ac) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
        Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
        smul_smul, hw'w, one_smul]
    abel
  rw [expand, hlift_id]
  -- Goal: Ac * Bc + w' • (Ac * Bc) + w • (Bc * Ac) = w • (liftR (B*A) - liftR (A*B))
  rw [show Ac * Bc + w' • (Ac * Bc) + w • (Bc * Ac)
        = (1 + w') • (Ac * Bc) + w • (Bc * Ac) by rw [add_smul, one_smul]]
  rw [h1w', neg_smul]
  -- Goal: -(w • (Ac*Bc)) + w • (Bc*Ac) = w • (liftR(B*A) - liftR(A*B))
  show -(w • (liftR A * liftR B)) + w • (liftR B * liftR A)
      = w • (liftR (B * A) - liftR (A * B))
  rw [liftR_mul, liftR_mul, smul_sub]
  abel

snip end

/-- The main problem: if `A² + B² = AB` and `BA - AB` is invertible (for real
`n × n` matrices), then `3 ∣ n`. -/
problem imc1997_p3 (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ)
    (hAB : A * A + B * B = A * B)
    (hinv : IsUnit (B * A - A * B).det) :
    3 ∣ n := by
  -- Set S = liftR A + ω • liftR B in complex matrices.
  set Sc : Matrix (Fin n) (Fin n) ℂ := liftR A + ω • liftR B with hSc
  -- Key identity: Sc * cbar Sc = ω • (liftR (B*A) - liftR (A*B)).
  have hkey := S_mul_cbarS A B hAB
  simp only at hkey
  -- Take determinants.
  have hdet : Sc.det * (cbar Sc).det = ω ^ n * ((B * A - A * B).det : ℝ) := by
    have h1 : (Sc * cbar Sc).det = Sc.det * (cbar Sc).det :=
      Matrix.det_mul _ _
    have h2 : (Sc * cbar Sc).det
        = ω ^ n * ((B * A - A * B).det : ℝ) := by
      rw [hkey]
      rw [Matrix.det_smul]
      rw [Fintype.card_fin]
      rw [← liftR_sub]
      rw [det_liftR]
    rw [← h1, h2]
  -- Cbar of det = conj of det, so LHS = |det Sc|².
  rw [det_cbar] at hdet
  -- Sc.det * conj (Sc.det) = ‖Sc.det‖² ∈ ℝ.
  have hLHS_real : (Sc.det * (starRingEnd ℂ) Sc.det).im = 0 := by
    rw [Complex.mul_conj]
    simp [Complex.normSq]
  -- RHS: ω^n * (real number).
  rw [hdet] at hLHS_real
  -- (ω^n * (r : ℂ)).im = (ω^n).im * r = 0 with r ≠ 0.
  have hr_ne : ((B * A - A * B).det : ℝ) ≠ 0 := hinv.ne_zero
  have hRHS_im : (ω ^ n * ((B * A - A * B).det : ℝ)).im
      = (ω ^ n).im * ((B * A - A * B).det : ℝ) := by
    rw [Complex.mul_im]
    simp
  rw [hRHS_im] at hLHS_real
  have : (ω ^ n).im = 0 := by
    rcases mul_eq_zero.mp hLHS_real with h | h
    · exact h
    · exact absurd h hr_ne
  exact (ω_pow_isReal_iff n).mp this

end Imc1997P3
