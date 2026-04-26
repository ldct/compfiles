/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2014, Problem 1

Determine all pairs `(a, b)` of real numbers for which there exists a unique
symmetric `2 × 2` matrix `M` with real entries satisfying `trace(M) = a` and
`det(M) = b`.

Answer: `a^2 = 4b`.
-/

namespace Imc2014P1

open Matrix

/-- The answer: the pairs `(a, b)` with `a^2 = 4b`. -/
determine answer : Set (ℝ × ℝ) := { p | p.1 ^ 2 = 4 * p.2 }

problem imc2014_p1 (a b : ℝ) :
    (∃! M : Matrix (Fin 2) (Fin 2) ℝ, M.IsSymm ∧ M.trace = a ∧ M.det = b) ↔
      (a, b) ∈ answer := by
  show (∃! M : Matrix (Fin 2) (Fin 2) ℝ, M.IsSymm ∧ M.trace = a ∧ M.det = b) ↔
      a ^ 2 = 4 * b
  constructor
  · -- If unique, then a^2 = 4b.
    rintro ⟨M, ⟨hsym, htr, hdet⟩, huniq⟩
    -- Let x = M 0 0, w = M 1 1, z = M 0 1. Symmetry: M 1 0 = z.
    set x : ℝ := M 0 0 with hxdef
    set w : ℝ := M 1 1 with hwdef
    set z : ℝ := M 0 1 with hzdef
    have hz' : M 1 0 = z := (hsym.apply 0 1).trans hzdef.symm
    -- trace M = x + w = a
    have hsum : x + w = a := by
      have htrace : M.trace = M 0 0 + M 1 1 := by
        simp [Matrix.trace, Fin.sum_univ_two]
      show M 0 0 + M 1 1 = a
      linarith [htrace, htr]
    -- det M = x * w - z * z = b
    have hprod : x * w - z * z = b := by
      show M 0 0 * M 1 1 - M 0 1 * M 0 1 = b
      rw [← hdet, Matrix.det_fin_two, hz']
    -- Consider M' : swap x, w. It is also symmetric with same trace and det.
    let M' : Matrix (Fin 2) (Fin 2) ℝ := !![w, z; z, x]
    have hM'_sym : M'.IsSymm := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [M', transpose_apply]
    have hM'_tr : M'.trace = a := by
      simp [M', Matrix.trace, Fin.sum_univ_two]; linarith
    have hM'_det : M'.det = b := by
      rw [Matrix.det_fin_two]; simp [M']; linarith
    -- By uniqueness, M = M'.
    have hMM' : M = M' := by
      have hMeq := huniq M ⟨hsym, htr, hdet⟩
      have hM'eq := huniq M' ⟨hM'_sym, hM'_tr, hM'_det⟩
      rw [hMeq, hM'eq]
    -- So x = w.
    have hxw : x = w := by
      have h1 : M 0 0 = M' 0 0 := by rw [hMM']
      simpa [M'] using h1
    -- Consider M'' : flip z -> -z.
    let M'' : Matrix (Fin 2) (Fin 2) ℝ := !![x, -z; -z, w]
    have hM''_sym : M''.IsSymm := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [M'', transpose_apply]
    have hM''_tr : M''.trace = a := by
      simp [M'', Matrix.trace, Fin.sum_univ_two]; linarith
    have hM''_det : M''.det = b := by
      rw [Matrix.det_fin_two]; simp [M'']; linarith
    have hMM'' : M = M'' := by
      have hMeq := huniq M ⟨hsym, htr, hdet⟩
      have hM''eq := huniq M'' ⟨hM''_sym, hM''_tr, hM''_det⟩
      rw [hMeq, hM''eq]
    have hz0 : z = 0 := by
      have h1 : M 0 1 = M'' 0 1 := by rw [hMM'']
      have h2 : z = -z := by simpa [M''] using h1
      linarith
    -- From x + w = a, x = w, z = 0, x*w - z*z = b, get a^2 = 4b.
    have hxa : x = a / 2 := by
      have : 2 * x = a := by linarith [hsum, hxw]
      linarith
    have hxxb : x * x = b := by
      have := hprod
      rw [← hxw, hz0] at this
      linarith
    have : (a / 2) * (a / 2) = b := by rw [← hxa]; exact hxxb
    nlinarith [this]
  · -- If a^2 = 4b, show uniqueness: M = (a/2) * I.
    intro hab
    refine ⟨!![a/2, 0; 0, a/2], ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [transpose_apply]
      · simp [Matrix.trace, Fin.sum_univ_two]
      · rw [Matrix.det_fin_two]; simp; nlinarith
    · rintro M ⟨hsym, htr, hdet⟩
      set x : ℝ := M 0 0 with hxdef
      set w : ℝ := M 1 1 with hwdef
      set z : ℝ := M 0 1 with hzdef
      have hz' : M 1 0 = z := (hsym.apply 0 1).trans hzdef.symm
      have hsum : x + w = a := by
        have htrace : M.trace = M 0 0 + M 1 1 := by
          simp [Matrix.trace, Fin.sum_univ_two]
        show M 0 0 + M 1 1 = a
        linarith [htrace, htr]
      have hprod : x * w - z * z = b := by
        show M 0 0 * M 1 1 - M 0 1 * M 0 1 = b
        rw [← hdet, Matrix.det_fin_two, hz']
      -- (x - w)^2 + 4 z^2 = (x + w)^2 - 4(xw - z^2) = a^2 - 4b = 0.
      have hkey : (x - w)^2 + 4 * z^2 = 0 := by
        have h1 : (x - w)^2 + 4 * z^2 = (x + w)^2 - 4 * (x * w - z * z) := by ring
        rw [h1, hsum, hprod, hab]; ring
      have hxw_eq : x = w := by nlinarith [sq_nonneg (x - w), sq_nonneg z, hkey]
      have hz_eq : z = 0 := by nlinarith [sq_nonneg (x - w), sq_nonneg z, hkey]
      have hxa : x = a / 2 := by
        have : 2 * x = a := by linarith [hsum, hxw_eq]
        linarith
      -- M = !![a/2, 0; 0, a/2]
      ext i j
      fin_cases i <;> fin_cases j
      · show M 0 0 = _; rw [← hxdef, hxa]; simp
      · show M 0 1 = _; rw [← hzdef, hz_eq]; simp
      · show M 1 0 = _; rw [hz', hz_eq]; simp
      · show M 1 1 = _; rw [← hwdef, ← hxw_eq, hxa]; simp

end Imc2014P1
