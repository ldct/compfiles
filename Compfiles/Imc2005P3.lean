/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2005, Problem 3

Let `f : ℝ → [0, ∞)` be a `C¹` function. Prove that

  `|∫₀¹ f(x)³ dx - f(0)² ∫₀¹ f(x) dx| ≤ (max_{x ∈ [0,1]} |f'(x)|) · (∫₀¹ f(x) dx)²`.

We formalize a slightly stronger statement: for any bound `M` with `|f'(x)| ≤ M`
on `[0, 1]`, the same inequality holds with `M` in place of `max |f'|`.
-/

namespace Imc2005P3

open Set MeasureTheory intervalIntegral

snip begin

/-- Key lemma: if `F(x) = ∫₀ˣ f` with `f` continuous and nonneg, then
`∫₀¹ f(x) · F(x) dx = F(1)² / 2`. -/
lemma integral_f_times_primitive (f : ℝ → ℝ) (hf_cont : Continuous f) :
    ∫ x in (0 : ℝ)..1, f x * (∫ t in (0 : ℝ)..x, f t) =
      ((∫ t in (0 : ℝ)..1, f t)) ^ 2 / 2 := by
  -- Let F(x) = ∫₀ˣ f. Then F'(x) = f(x), so (F²/2)' = F · F' = F · f.
  -- By FTC, ∫₀¹ f · F = F(1)² / 2 - F(0)² / 2 = F(1)² / 2.
  set F : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, f t with hF_def
  have hF_deriv : ∀ x, HasDerivAt F (f x) x := by
    intro x
    have : IntervalIntegrable f volume 0 x := hf_cont.intervalIntegrable _ _
    exact intervalIntegral.integral_hasDerivAt_right this
      (hf_cont.stronglyMeasurableAtFilter _ _) hf_cont.continuousAt
  -- (F²/2)' x = F x * f x
  have hFsq_deriv : ∀ x, HasDerivAt (fun y => F y ^ 2 / 2) (F x * f x) x := by
    intro x
    have h1 : HasDerivAt (fun y => F y ^ 2) (2 * F x * f x) x := by
      have := (hF_deriv x).pow 2
      simpa using this
    have h2 : HasDerivAt (fun y => F y ^ 2 / 2) (2 * F x * f x / 2) x :=
      h1.div_const 2
    convert h2 using 1
    ring
  -- F(0) = 0
  have hF0 : F 0 = 0 := by simp [F]
  -- F is continuous (since differentiable).
  have hF_cont' : Continuous F :=
    continuous_iff_continuousAt.mpr (fun x => (hF_deriv x).continuousAt)
  have hFf_int : IntervalIntegrable (fun x => F x * f x) volume 0 1 :=
    (hF_cont'.mul hf_cont).intervalIntegrable _ _
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y => F y ^ 2 / 2) (f' := fun x => F x * f x)
    (fun x _ => hFsq_deriv x) hFf_int
  -- ∫₀¹ F x * f x = F 1 ^ 2 / 2 - F 0 ^ 2 / 2 = F 1 ^ 2 / 2.
  have hF1 : F 1 = ∫ t in (0 : ℝ)..1, f t := rfl
  -- Rewrite our goal: ∫ f x * F x = ∫ F x * f x by mul_comm.
  have h_comm : (∫ x in (0 : ℝ)..1, f x * F x) = ∫ x in (0 : ℝ)..1, F x * f x := by
    congr 1; ext x; ring
  rw [show (∫ x in (0:ℝ)..1, f x * (∫ t in (0:ℝ)..x, f t))
        = ∫ x in (0:ℝ)..1, f x * F x from rfl]
  rw [h_comm, this]
  simp only [hF0]
  ring

snip end

problem imc2005_p3 (f f' : ℝ → ℝ)
    (hf_nn : ∀ x, 0 ≤ f x)
    (hf_deriv : ∀ x, HasDerivAt f (f' x) x)
    (hf'_cont : Continuous f')
    (M : ℝ) (hM : ∀ x ∈ Icc (0 : ℝ) 1, |f' x| ≤ M) :
    |(∫ x in (0 : ℝ)..1, f x ^ 3) - f 0 ^ 2 * ∫ x in (0 : ℝ)..1, f x|
      ≤ M * (∫ x in (0 : ℝ)..1, f x) ^ 2 := by
  -- f is continuous.
  have hf_cont : Continuous f :=
    continuous_iff_continuousAt.mpr (fun x => (hf_deriv x).continuousAt)
  -- M ≥ 0 since |f'(0)| ≤ M.
  have hM_nn : 0 ≤ M := by
    have : |f' 0| ≤ M := hM 0 ⟨le_refl _, by norm_num⟩
    linarith [abs_nonneg (f' 0)]
  -- (f²/2)' x = f x * f' x
  have hfsq_deriv : ∀ x, HasDerivAt (fun y => f y ^ 2 / 2) (f x * f' x) x := by
    intro x
    have h1 : HasDerivAt (fun y => f y ^ 2) (2 * f x * f' x) x := by
      have := (hf_deriv x).pow 2
      simpa using this
    have h2 : HasDerivAt (fun y => f y ^ 2 / 2) (2 * f x * f' x / 2) x :=
      h1.div_const 2
    convert h2 using 1
    ring
  -- For x ∈ [0,1], f(x)²/2 - f(0)²/2 = ∫₀ˣ f(t) f'(t) dt.
  have hff'_int : ∀ x, IntervalIntegrable (fun t => f t * f' t) volume 0 x :=
    fun x => (hf_cont.mul hf'_cont).intervalIntegrable _ _
  have hftc : ∀ x, f x ^ 2 / 2 - f 0 ^ 2 / 2 = ∫ t in (0 : ℝ)..x, f t * f' t := by
    intro x
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y => f y ^ 2 / 2) (f' := fun t => f t * f' t)
      (fun t _ => hfsq_deriv t) (hff'_int x)
    linarith
  -- For x ∈ [0,1], |∫₀ˣ f f'| ≤ M ∫₀ˣ f.
  -- (We need 0 ≤ x ≤ 1 for the bound on |f'|.)
  have h_int_bound : ∀ x ∈ Icc (0 : ℝ) 1,
      |∫ t in (0 : ℝ)..x, f t * f' t| ≤ M * ∫ t in (0 : ℝ)..x, f t := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    -- Use triangle inequality for integrals and bound |f t * f' t| ≤ M * f t.
    have h_abs : |∫ t in (0 : ℝ)..x, f t * f' t|
        ≤ ∫ t in (0 : ℝ)..x, |f t * f' t| :=
      intervalIntegral.abs_integral_le_integral_abs (μ := volume) hx0
    have h_mono : ∫ t in (0 : ℝ)..x, |f t * f' t| ≤ ∫ t in (0 : ℝ)..x, M * f t := by
      apply intervalIntegral.integral_mono_on hx0
      · exact ((hf_cont.mul hf'_cont).abs).intervalIntegrable _ _
      · exact (continuous_const.mul hf_cont).intervalIntegrable _ _
      · intro t ht
        have htxmem : t ∈ Icc (0:ℝ) 1 := ⟨ht.1, le_trans ht.2 hx1⟩
        have h1 : |f' t| ≤ M := hM t htxmem
        calc |f t * f' t| = |f t| * |f' t| := abs_mul _ _
          _ = f t * |f' t| := by rw [abs_of_nonneg (hf_nn t)]
          _ ≤ f t * M := by
              apply mul_le_mul_of_nonneg_left h1 (hf_nn t)
          _ = M * f t := by ring
    have h_eq : ∫ t in (0 : ℝ)..x, M * f t = M * ∫ t in (0 : ℝ)..x, f t :=
      intervalIntegral.integral_const_mul _ _
    linarith
  -- So for x ∈ [0,1], |f(x)² - f(0)²| ≤ 2 M ∫₀ˣ f.
  have h_sq_bound : ∀ x ∈ Icc (0 : ℝ) 1,
      |f x ^ 2 - f 0 ^ 2| ≤ 2 * M * ∫ t in (0 : ℝ)..x, f t := by
    intro x hx
    have h := h_int_bound x hx
    have heq : f x ^ 2 - f 0 ^ 2 = 2 * (∫ t in (0 : ℝ)..x, f t * f' t) := by
      have := hftc x; linarith
    rw [heq, abs_mul]
    have : |(2:ℝ)| = 2 := abs_of_pos (by norm_num)
    rw [this]
    have : (2:ℝ) * |∫ t in (0 : ℝ)..x, f t * f' t| ≤ 2 * (M * ∫ t in (0 : ℝ)..x, f t) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    linarith
  -- Multiply by f(x) ≥ 0: for x ∈ [0,1], |f(x)³ - f(0)² f(x)| ≤ 2 M f(x) ∫₀ˣ f.
  have h_cubed_bound : ∀ x ∈ Icc (0 : ℝ) 1,
      |f x ^ 3 - f 0 ^ 2 * f x| ≤ 2 * M * f x * (∫ t in (0 : ℝ)..x, f t) := by
    intro x hx
    have h := h_sq_bound x hx
    have hfx_nn : 0 ≤ f x := hf_nn x
    have heq : f x ^ 3 - f 0 ^ 2 * f x = f x * (f x ^ 2 - f 0 ^ 2) := by ring
    rw [heq, abs_mul, abs_of_nonneg hfx_nn]
    have := mul_le_mul_of_nonneg_left h hfx_nn
    calc f x * |f x ^ 2 - f 0 ^ 2| ≤ f x * (2 * M * ∫ t in (0 : ℝ)..x, f t) := this
      _ = 2 * M * f x * ∫ t in (0 : ℝ)..x, f t := by ring
  -- Integrate over [0,1]: |∫₀¹ (f³ - f(0)² f)| ≤ 2M ∫₀¹ f(x) ∫₀ˣ f(t) dt dx = M (∫₀¹ f)².
  -- First, |∫₀¹ (f³ - f(0)² f)| ≤ ∫₀¹ |f³ - f(0)² f| ≤ 2M ∫₀¹ f(x) ∫₀ˣ f(t) dt dx.
  have hcube_int : IntervalIntegrable (fun x => f x ^ 3) volume 0 1 :=
    (hf_cont.pow 3).intervalIntegrable _ _
  have hlin_int : IntervalIntegrable (fun x => f 0 ^ 2 * f x) volume 0 1 :=
    (continuous_const.mul hf_cont).intervalIntegrable _ _
  have hdiff_int : IntervalIntegrable (fun x => f x ^ 3 - f 0 ^ 2 * f x) volume 0 1 :=
    hcube_int.sub hlin_int
  -- Abbreviation for ∫₀ˣ f t dt.
  set F : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, f t with hF_def
  have hF_deriv : ∀ x, HasDerivAt F (f x) x := by
    intro x
    have : IntervalIntegrable f volume 0 x := hf_cont.intervalIntegrable _ _
    exact intervalIntegral.integral_hasDerivAt_right this
      (hf_cont.stronglyMeasurableAtFilter _ _) hf_cont.continuousAt
  have hF_cont : Continuous F :=
    continuous_iff_continuousAt.mpr (fun x => (hF_deriv x).continuousAt)
  -- Step 1: |∫₀¹ (f³ - f(0)² f)| ≤ ∫₀¹ |f³ - f(0)² f|.
  have hstep1 : |∫ x in (0:ℝ)..1, (f x ^ 3 - f 0 ^ 2 * f x)|
      ≤ ∫ x in (0:ℝ)..1, |f x ^ 3 - f 0 ^ 2 * f x| :=
    intervalIntegral.abs_integral_le_integral_abs (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
  -- Step 2: ∫₀¹ |f³ - f(0)² f| ≤ ∫₀¹ 2 M f(x) F(x).
  have hbound_int : IntervalIntegrable (fun x => 2 * M * f x * F x) volume 0 1 :=
    ((continuous_const.mul hf_cont).mul hF_cont).intervalIntegrable _ _
  have habs_int : IntervalIntegrable (fun x => |f x ^ 3 - f 0 ^ 2 * f x|) volume 0 1 :=
    hdiff_int.abs
  have hstep2 : ∫ x in (0:ℝ)..1, |f x ^ 3 - f 0 ^ 2 * f x|
      ≤ ∫ x in (0:ℝ)..1, 2 * M * f x * F x := by
    apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) habs_int hbound_int
    intro x hx
    exact h_cubed_bound x hx
  -- Step 3: ∫₀¹ 2 M f(x) F(x) = 2M · (∫₀¹ f)² / 2 = M (∫₀¹ f)².
  have hstep3 : ∫ x in (0:ℝ)..1, 2 * M * f x * F x = M * F 1 ^ 2 := by
    have h1 : ∫ x in (0:ℝ)..1, 2 * M * f x * F x
        = 2 * M * ∫ x in (0:ℝ)..1, f x * F x := by
      have : (fun x => 2 * M * f x * F x) = (fun x => (2 * M) * (f x * F x)) := by
        ext x; ring
      rw [this, intervalIntegral.integral_const_mul]
    rw [h1]
    have hkey : ∫ x in (0:ℝ)..1, f x * F x = F 1 ^ 2 / 2 :=
      integral_f_times_primitive f hf_cont
    rw [hkey]
    ring
  -- Step 4: reassemble.
  have h_decomp : (∫ x in (0:ℝ)..1, f x ^ 3) - f 0 ^ 2 * ∫ x in (0:ℝ)..1, f x
      = ∫ x in (0:ℝ)..1, (f x ^ 3 - f 0 ^ 2 * f x) := by
    rw [intervalIntegral.integral_sub hcube_int hlin_int]
    rw [intervalIntegral.integral_const_mul]
  rw [h_decomp]
  have : F 1 = ∫ x in (0:ℝ)..1, f x := rfl
  rw [show (∫ x in (0:ℝ)..1, f x) ^ 2 = F 1 ^ 2 from by rw [this]]
  linarith [hstep1, hstep2, hstep3]

end Imc2005P3
