/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2025, Problem 2

Let `f : ℝ → ℝ` be a twice continuously differentiable function, and suppose
that `∫_{-1}^{1} f(x) dx = 0` and `f(1) = f(-1) = 1`. Prove that

  `∫_{-1}^{1} (f''(x))² dx ≥ 15`,

and find all such functions for which equality holds.

The answer: equality holds iff `f(x) = (-5x⁴ + 30x² - 9) / 16` on `[-1, 1]`.
-/

namespace Imc2025P2

open scoped MeasureTheory Interval
open intervalIntegral Set

/-- The extremal function: `f(x) = (-5x⁴ + 30x² - 9) / 16`. -/
noncomputable def extremal : ℝ → ℝ := fun x => (-5 * x^4 + 30 * x^2 - 9) / 16

/-- The set of functions achieving equality in Problem 2: those that agree with
`extremal` on `[-1, 1]`. -/
determine equalitySet : Set (ℝ → ℝ) :=
  { f | ∀ x ∈ Set.Icc (-1 : ℝ) 1, f x = extremal x }

snip begin

/-- Continuity of iterated derivatives of a `ContDiff` function. -/
lemma continuous_iteratedDeriv_of_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (k : ℕ)
    (hk : k ≤ 2) : Continuous (iteratedDeriv k f) :=
  hf.continuous_iteratedDeriv k (by exact_mod_cast hk)

lemma contDiff_one_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (deriv f) := by
  have h := (contDiff_succ_iff_deriv (n := 1) (f := f)).mp (by exact_mod_cast hf)
  exact h.2.2

/-- `f` has a derivative if `ContDiff ℝ 2`. -/
lemma hasDerivAt_of_contDiff2 {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    HasDerivAt f (deriv f x) x :=
  (hf.differentiable (by decide) x).hasDerivAt

/-- `deriv f` has a derivative (= iteratedDeriv 2 f) if `ContDiff ℝ 2 f`. -/
lemma hasDerivAt_deriv_of_contDiff2 {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    HasDerivAt (deriv f) (iteratedDeriv 2 f x) x := by
  have h2 : Differentiable ℝ (deriv f) := hf.differentiable_deriv_two
  have h3 : HasDerivAt (deriv f) (deriv (deriv f) x) x := (h2 x).hasDerivAt
  have heq : iteratedDeriv 2 f = deriv (deriv f) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [heq]; exact h3

/-- First step of IBP: `∫₋₁¹ (1-x²) · f'' = -∫₋₁¹ (-2x) · f'`. -/
lemma ibp_step1 {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    (∫ x in (-1 : ℝ)..1, (1 - x^2) * iteratedDeriv 2 f x) =
    - ∫ x in (-1 : ℝ)..1, (-2 * x) * deriv f x := by
  have hu : ∀ x ∈ [[(-1 : ℝ), 1]], HasDerivAt (fun x => 1 - x^2) (-2 * x) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => x^2) (2 * x ^ 1) x := by simpa using hasDerivAt_pow 2 x
    have h2 : HasDerivAt (fun x : ℝ => 1 - x^2) (0 - 2 * x ^ 1) x :=
      (hasDerivAt_const x (1:ℝ)).sub h1
    simpa [pow_one] using h2
  have hv : ∀ x ∈ [[(-1 : ℝ), 1]], HasDerivAt (deriv f) (iteratedDeriv 2 f x) x :=
    fun x _ => hasDerivAt_deriv_of_contDiff2 hf x
  have hu' : IntervalIntegrable (fun x : ℝ => -2 * x) MeasureTheory.volume (-1) 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hv' : IntervalIntegrable (iteratedDeriv 2 f) MeasureTheory.volume (-1) 1 :=
    (continuous_iteratedDeriv_of_contDiff hf 2 le_rfl).intervalIntegrable _ _
  have IBP := integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  simp only [one_pow, neg_one_sq, sub_self, zero_mul, zero_sub] at IBP
  exact IBP

/-- Second step of IBP: `∫₋₁¹ (-2x) · f' = -4`. -/
lemma ibp_step2 {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hint : ∫ x in (-1 : ℝ)..1, f x = 0)
    (hf1 : f 1 = 1) (hfm1 : f (-1) = 1) :
    (∫ x in (-1 : ℝ)..1, (-2 * x) * deriv f x) = -4 := by
  have hu : ∀ x ∈ [[(-1 : ℝ), 1]], HasDerivAt (fun x : ℝ => -2 * x) (-2) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id x
    have h2 : HasDerivAt (fun x : ℝ => -2 * x) (-2 * 1) x := h1.const_mul (-2)
    simpa using h2
  have hv : ∀ x ∈ [[(-1 : ℝ), 1]], HasDerivAt f (deriv f x) x :=
    fun x _ => hasDerivAt_of_contDiff2 hf x
  have hu' : IntervalIntegrable (fun _ : ℝ => (-2 : ℝ)) MeasureTheory.volume (-1) 1 :=
    _root_.intervalIntegrable_const
  have hv' : IntervalIntegrable (deriv f) MeasureTheory.volume (-1) 1 :=
    ((contDiff_one_deriv hf).continuous).intervalIntegrable _ _
  have IBP := integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  simp only [hf1, hfm1] at IBP
  have hconst : (∫ x in (-1 : ℝ)..1, ((-2 : ℝ)) * f x) = -2 * ∫ x in (-1 : ℝ)..1, f x :=
    intervalIntegral.integral_const_mul _ _
  rw [hconst, hint] at IBP
  linarith

/-- Combining: `∫₋₁¹ (1-x²) · f'' = 4`. -/
lemma integral_g_mul_fpp {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hint : ∫ x in (-1 : ℝ)..1, f x = 0)
    (hf1 : f 1 = 1) (hfm1 : f (-1) = 1) :
    (∫ x in (-1 : ℝ)..1, (1 - x^2) * iteratedDeriv 2 f x) = 4 := by
  rw [ibp_step1 hf, ibp_step2 hf hint hf1 hfm1]; ring

/-- `∫₋₁¹ (1-x²)² = 16/15`. -/
lemma integral_g_sq : (∫ x in (-1 : ℝ)..1, (1 - x^2)^2) = 16/15 := by
  have h : (∫ x in (-1 : ℝ)..1, (1 - x^2)^2) =
      ∫ x in (-1 : ℝ)..1, (1 - 2 * x^2 + x^4) := by
    congr 1; ext x; ring
  rw [h]
  have h1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume (-1) 1 :=
    _root_.intervalIntegrable_const
  have h2 : IntervalIntegrable (fun x : ℝ => 2 * x^2) MeasureTheory.volume (-1) 1 :=
    (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _
  have h4 : IntervalIntegrable (fun x : ℝ => x^4) MeasureTheory.volume (-1) 1 :=
    (continuous_pow 4).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (h1.sub h2) h4,
      intervalIntegral.integral_sub h1 h2,
      intervalIntegral.integral_const_mul]
  simp only [integral_pow, integral_const, smul_eq_mul]
  norm_num

/-- Expansion of `∫(f'' - (15/4)·g)²`. -/
lemma expand_square {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    (∫ x in (-1 : ℝ)..1, (iteratedDeriv 2 f x - (15/4) * (1 - x^2))^2) =
    (∫ x in (-1 : ℝ)..1, (iteratedDeriv 2 f x)^2)
      - 2 * (15/4) * (∫ x in (-1 : ℝ)..1, (1 - x^2) * iteratedDeriv 2 f x)
      + (15/4)^2 * (∫ x in (-1 : ℝ)..1, (1 - x^2)^2) := by
  have hfpp_cont : Continuous (iteratedDeriv 2 f) :=
    continuous_iteratedDeriv_of_contDiff hf 2 le_rfl
  have hg_cont : Continuous (fun x : ℝ => (1 - x^2)) := by continuity
  have h_expand : ∀ x,
      (iteratedDeriv 2 f x - (15/4) * (1 - x^2))^2 =
      (iteratedDeriv 2 f x)^2 - 2 * (15/4) * ((1 - x^2) * iteratedDeriv 2 f x)
      + (15/4)^2 * (1 - x^2)^2 := by
    intro x; ring
  simp_rw [h_expand]
  have int_sq : IntervalIntegrable (fun x => (iteratedDeriv 2 f x)^2)
      MeasureTheory.volume (-1) 1 :=
    (hfpp_cont.pow 2).intervalIntegrable _ _
  have int_mix : IntervalIntegrable
      (fun x => 2 * (15/4) * ((1 - x^2) * iteratedDeriv 2 f x))
      MeasureTheory.volume (-1) 1 :=
    ((hg_cont.mul hfpp_cont).const_mul _).intervalIntegrable _ _
  have int_gsq : IntervalIntegrable (fun x : ℝ => (15/4)^2 * (1 - x^2)^2)
      MeasureTheory.volume (-1) 1 :=
    ((hg_cont.pow 2).const_mul _).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (int_sq.sub int_mix) int_gsq,
      intervalIntegral.integral_sub int_sq int_mix,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- If a continuous nonneg square function has zero integral on `[-1,1]`,
the function is zero on `[-1,1]`. -/
lemma eq_zero_of_integral_sq_eq_zero (h : ℝ → ℝ) (hcont : Continuous h)
    (hint : (∫ x in (-1 : ℝ)..1, (h x)^2) = 0) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, h x = 0 := by
  have hle : (-1 : ℝ) ≤ 1 := by norm_num
  have hcontsq : Continuous (fun x => (h x)^2) := hcont.pow 2
  have hpos : ∀ x, 0 ≤ (h x)^2 := fun x => sq_nonneg _
  rw [intervalIntegral.integral_of_le hle] at hint
  have hint' := (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => hpos x))
    (hcontsq.integrableOn_Ioc)).mp hint
  -- h² =ᵐ 0 on Ioc (-1) 1.
  have h_on_Ioo : ∀ y ∈ Set.Ioo (-1 : ℝ) 1, h y = 0 := by
    intro y hy
    by_contra hne
    have hy2 : 0 < (h y)^2 := by positivity
    have hnhd : Set.Ioo (-1 : ℝ) 1 ∈ nhds y := Ioo_mem_nhds hy.1 hy.2
    have hcontat : ContinuousAt (fun z => (h z)^2) y := hcontsq.continuousAt
    have hev : ∀ᶠ z in nhds y, (h y)^2 / 2 < (h z)^2 :=
      (hcontat.tendsto).eventually_const_lt (by linarith : (h y)^2 / 2 < (h y)^2)
    -- Get an open U around y in Ioo where h² > (h y)²/2.
    obtain ⟨U, hU_sub_hpos, hU_open, hyU⟩ :
        ∃ U : Set ℝ, (∀ z ∈ U, (h y)^2 / 2 < (h z)^2 ∧ z ∈ Set.Ioo (-1 : ℝ) 1) ∧
          IsOpen U ∧ y ∈ U := by
      rcases (nhds_basis_opens y).eventually_iff.mp (hev.and
        (Filter.eventually_of_mem hnhd (fun z hz => hz))) with ⟨U, ⟨hyU, hU_open⟩, hU_sub⟩
      exact ⟨U, hU_sub, hU_open, hyU⟩
    have hU_Ioc : U ⊆ Set.Ioc (-1 : ℝ) 1 :=
      fun z hz => Set.Ioo_subset_Ioc_self (hU_sub_hpos z hz).2
    have hU_meas_pos : 0 < MeasureTheory.volume U := hU_open.measure_pos _ ⟨y, hyU⟩
    have hU_meas : MeasurableSet U := hU_open.measurableSet
    have hrestrict_pos :
        0 < (MeasureTheory.volume.restrict (Set.Ioc (-1 : ℝ) 1)) U := by
      rw [MeasureTheory.Measure.restrict_apply hU_meas]
      have heq : U ∩ Set.Ioc (-1 : ℝ) 1 = U := Set.inter_eq_left.mpr hU_Ioc
      rw [heq]; exact hU_meas_pos
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff] at hint'
    simp only [Pi.zero_apply] at hint'
    -- Set where h² ≠ 0 contains U (modulo Ioc).
    have hU_sub_ne : U ⊆ {z | (h z)^2 ≠ 0} := by
      intro z hz
      have := (hU_sub_hpos z hz).1
      intro habs
      rw [habs] at this
      linarith
    have : (MeasureTheory.volume.restrict (Set.Ioc (-1 : ℝ) 1)) U ≤
        (MeasureTheory.volume.restrict (Set.Ioc (-1 : ℝ) 1)) {z | (h z)^2 ≠ 0} :=
      MeasureTheory.measure_mono hU_sub_ne
    rw [hint'] at this
    exact absurd (lt_of_lt_of_le hrestrict_pos this) (lt_irrefl _)
  intro x hx
  rcases eq_or_lt_of_le hx.1 with heq | hlt1
  · have hx1 : x = -1 := heq.symm
    subst hx1
    have htend : Filter.Tendsto h (nhdsWithin (-1 : ℝ) (Set.Ioo (-1) 1))
        (nhds (h (-1 : ℝ))) :=
      (hcont.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have hzero : h =ᶠ[nhdsWithin (-1 : ℝ) (Set.Ioo (-1) 1)] (fun _ => 0) := by
      filter_upwards [self_mem_nhdsWithin] with y hy using h_on_Ioo y hy
    have hlim : Filter.Tendsto h (nhdsWithin (-1 : ℝ) (Set.Ioo (-1) 1)) (nhds 0) :=
      (tendsto_const_nhds).congr' hzero.symm
    have hnb : (nhdsWithin (-1 : ℝ) (Set.Ioo (-1) 1)).NeBot := by
      rw [nhdsWithin_Ioo_eq_nhdsGT (by norm_num : (-1 : ℝ) < 1)]
      exact nhdsGT_neBot_of_exists_gt ⟨1, by norm_num⟩
    exact tendsto_nhds_unique htend hlim
  · rcases eq_or_lt_of_le hx.2 with heq2 | hlt2
    · have hx2 : x = 1 := heq2
      subst hx2
      have htend : Filter.Tendsto h (nhdsWithin (1 : ℝ) (Set.Ioo (-1) 1))
          (nhds (h (1 : ℝ))) :=
        (hcont.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
      have hzero : h =ᶠ[nhdsWithin (1 : ℝ) (Set.Ioo (-1) 1)] (fun _ => 0) := by
        filter_upwards [self_mem_nhdsWithin] with y hy using h_on_Ioo y hy
      have hlim : Filter.Tendsto h (nhdsWithin (1 : ℝ) (Set.Ioo (-1) 1)) (nhds 0) :=
        (tendsto_const_nhds).congr' hzero.symm
      have hnb : (nhdsWithin (1 : ℝ) (Set.Ioo (-1) 1)).NeBot := by
        rw [nhdsWithin_Ioo_eq_nhdsLT (by norm_num : (-1 : ℝ) < 1)]
        exact nhdsLT_neBot_of_exists_lt ⟨-1, by norm_num⟩
      exact tendsto_nhds_unique htend hlim
    · exact h_on_Ioo x ⟨hlt1, hlt2⟩

/-- The 2nd derivative of the extremal is `(15/4)(1 - x²)`. -/
lemma iteratedDeriv_2_extremal (x : ℝ) :
    iteratedDeriv 2 extremal x = (15/4) * (1 - x^2) := by
  rw [show iteratedDeriv 2 extremal = deriv (deriv extremal) by
    rw [iteratedDeriv_succ, iteratedDeriv_one] ]
  have hd1 : ∀ y : ℝ, deriv extremal y = (-20 * y^3 + 60 * y) / 16 := by
    intro y
    have h1 : HasDerivAt (fun x : ℝ => x^4) (4 * y^3) y := by simpa using hasDerivAt_pow 4 y
    have h2 : HasDerivAt (fun x : ℝ => x^2) (2 * y^1) y := by simpa using hasDerivAt_pow 2 y
    have h9 : HasDerivAt (fun _ : ℝ => (9 : ℝ)) 0 y := hasDerivAt_const y 9
    have hda : HasDerivAt (fun x : ℝ => -5 * x^4 + 30 * x^2 - 9)
        (-5 * (4 * y^3) + 30 * (2 * y^1) - 0) y :=
      ((h1.const_mul (-5)).add (h2.const_mul 30)).sub h9
    have hda2 : HasDerivAt extremal ((-5 * (4 * y^3) + 30 * (2 * y^1) - 0) / 16) y := by
      have := hda.div_const 16
      exact this
    have hval : (-5 * (4 * y^3) + 30 * (2 * y^1) - 0) / 16 = (-20 * y^3 + 60 * y) / 16 := by
      ring
    rw [hval] at hda2
    exact hda2.deriv
  have hderiv_ext_eq : deriv extremal = fun y => (-20 * y^3 + 60 * y) / 16 := funext hd1
  rw [hderiv_ext_eq]
  have h1 : HasDerivAt (fun y : ℝ => y^3) (3 * x^2) x := by simpa using hasDerivAt_pow 3 x
  have h2 : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hda : HasDerivAt (fun y : ℝ => -20 * y^3 + 60 * y) (-20 * (3 * x^2) + 60 * 1) x :=
    (h1.const_mul (-20)).add (h2.const_mul 60)
  have hda2 : HasDerivAt (fun y : ℝ => (-20 * y^3 + 60 * y) / 16)
      ((-20 * (3 * x^2) + 60 * 1) / 16) x := hda.div_const 16
  have hval : (-20 * (3 * x^2) + 60 * 1) / 16 = (15/4) * (1 - x^2) := by ring
  rw [hval] at hda2
  exact hda2.deriv

lemma extremal_contDiff : ContDiff ℝ 2 extremal := by
  unfold extremal
  exact ContDiff.div_const
    ((((contDiff_const.mul (contDiff_id.pow 4)).add
      (contDiff_const.mul (contDiff_id.pow 2))).sub contDiff_const)) 16

lemma extremal_at_one : extremal 1 = 1 := by unfold extremal; norm_num
lemma extremal_at_neg_one : extremal (-1) = 1 := by unfold extremal; norm_num

lemma integral_extremal : (∫ x in (-1 : ℝ)..1, extremal x) = 0 := by
  unfold extremal
  have h_rw : (fun x : ℝ => (-5 * x^4 + 30 * x^2 - 9) / 16) =
      fun x => (1/16) * (-5 * x^4 + 30 * x^2 - 9) := by
    funext x; ring
  rw [h_rw, intervalIntegral.integral_const_mul]
  have h4 : IntervalIntegrable (fun x : ℝ => -5 * x^4) MeasureTheory.volume (-1) 1 :=
    (continuous_const.mul (continuous_pow 4)).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x : ℝ => 30 * x^2) MeasureTheory.volume (-1) 1 :=
    (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _
  have h0 : IntervalIntegrable (fun _ : ℝ => (9 : ℝ)) MeasureTheory.volume (-1) 1 :=
    _root_.intervalIntegrable_const
  rw [intervalIntegral.integral_sub (h4.add h2) h0,
      intervalIntegral.integral_add h4 h2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp only [integral_pow, integral_const, smul_eq_mul]
  norm_num

snip end

problem imc2025_p2 (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hint : ∫ x in (-1 : ℝ)..1, f x = 0)
    (hf1 : f 1 = 1) (hfm1 : f (-1) = 1) :
    15 ≤ ∫ x in (-1 : ℝ)..1, (iteratedDeriv 2 f x) ^ 2 ∧
    (f ∈ equalitySet ↔ ∫ x in (-1 : ℝ)..1, (iteratedDeriv 2 f x) ^ 2 = 15) := by
  have hgf := integral_g_mul_fpp hf hint hf1 hfm1
  have hg2 := integral_g_sq
  have hexp := expand_square hf
  rw [hgf, hg2] at hexp
  have hkey : (∫ x in (-1 : ℝ)..1, (iteratedDeriv 2 f x - (15/4) * (1 - x^2))^2) =
      (∫ x in (-1 : ℝ)..1, (iteratedDeriv 2 f x)^2) - 15 := by
    rw [hexp]; ring
  have hnonneg : 0 ≤ ∫ x in (-1 : ℝ)..1, (iteratedDeriv 2 f x - (15/4) * (1 - x^2))^2 := by
    apply intervalIntegral.integral_nonneg (by norm_num : (-1 : ℝ) ≤ 1)
    intro x _; exact sq_nonneg _
  refine ⟨by linarith, ?_⟩
  constructor
  · intro hfe
    simp only [equalitySet, Set.mem_setOf_eq] at hfe
    have hfpp_eq_on_Ioo : ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        iteratedDeriv 2 f x = iteratedDeriv 2 extremal x := by
      intro x hx
      have hnhd : Set.Icc (-1 : ℝ) 1 ∈ nhds x := Icc_mem_nhds hx.1 hx.2
      have heq_nhd : f =ᶠ[nhds x] extremal := by
        filter_upwards [hnhd] with y hy using hfe y hy
      rw [show iteratedDeriv 2 f = deriv (deriv f) by
        rw [iteratedDeriv_succ, iteratedDeriv_one],
        show iteratedDeriv 2 extremal = deriv (deriv extremal) by
        rw [iteratedDeriv_succ, iteratedDeriv_one] ]
      have hderiv_eq : deriv f =ᶠ[nhds x] deriv extremal := by
        filter_upwards [heq_nhd.eventuallyEq_nhds] with y hy
        exact hy.deriv_eq
      exact hderiv_eq.deriv_eq
    have hfpp_eq_on_Icc : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        iteratedDeriv 2 f x = iteratedDeriv 2 extremal x := by
      intro x hx
      have hcontf : Continuous (iteratedDeriv 2 f) :=
        continuous_iteratedDeriv_of_contDiff hf 2 le_rfl
      have hconte : Continuous (iteratedDeriv 2 extremal) :=
        continuous_iteratedDeriv_of_contDiff extremal_contDiff 2 le_rfl
      rcases eq_or_lt_of_le hx.1 with heq1 | hlt1
      · have hx1 : x = -1 := heq1.symm
        subst hx1
        have htend : Filter.Tendsto (fun y => iteratedDeriv 2 f y - iteratedDeriv 2 extremal y)
            (nhdsWithin (-1 : ℝ) (Set.Ioo (-1) 1))
            (nhds (iteratedDeriv 2 f (-1) - iteratedDeriv 2 extremal (-1))) :=
          ((hcontf.sub hconte).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
        have hzero : (fun y => iteratedDeriv 2 f y - iteratedDeriv 2 extremal y)
            =ᶠ[nhdsWithin (-1 : ℝ) (Set.Ioo (-1) 1)] (fun _ => 0) := by
          filter_upwards [self_mem_nhdsWithin] with y hy
          rw [hfpp_eq_on_Ioo y hy]; ring
        have hlim : Filter.Tendsto (fun y => iteratedDeriv 2 f y - iteratedDeriv 2 extremal y)
            (nhdsWithin (-1 : ℝ) (Set.Ioo (-1) 1)) (nhds 0) :=
          (tendsto_const_nhds).congr' hzero.symm
        have hnb : (nhdsWithin (-1 : ℝ) (Set.Ioo (-1) 1)).NeBot := by
          rw [nhdsWithin_Ioo_eq_nhdsGT (by norm_num : (-1 : ℝ) < 1)]
          exact nhdsGT_neBot_of_exists_gt ⟨1, by norm_num⟩
        have hheq := tendsto_nhds_unique htend hlim
        linarith
      · rcases eq_or_lt_of_le hx.2 with heq2 | hlt2
        · have hx2 : x = 1 := heq2
          subst hx2
          have htend : Filter.Tendsto (fun y => iteratedDeriv 2 f y - iteratedDeriv 2 extremal y)
              (nhdsWithin (1 : ℝ) (Set.Ioo (-1) 1))
              (nhds (iteratedDeriv 2 f 1 - iteratedDeriv 2 extremal 1)) :=
            ((hcontf.sub hconte).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
          have hzero : (fun y => iteratedDeriv 2 f y - iteratedDeriv 2 extremal y)
              =ᶠ[nhdsWithin (1 : ℝ) (Set.Ioo (-1) 1)] (fun _ => 0) := by
            filter_upwards [self_mem_nhdsWithin] with y hy
            rw [hfpp_eq_on_Ioo y hy]; ring
          have hlim : Filter.Tendsto (fun y => iteratedDeriv 2 f y - iteratedDeriv 2 extremal y)
              (nhdsWithin (1 : ℝ) (Set.Ioo (-1) 1)) (nhds 0) :=
            (tendsto_const_nhds).congr' hzero.symm
          have hnb : (nhdsWithin (1 : ℝ) (Set.Ioo (-1) 1)).NeBot := by
            rw [nhdsWithin_Ioo_eq_nhdsLT (by norm_num : (-1 : ℝ) < 1)]
            exact nhdsLT_neBot_of_exists_lt ⟨-1, by norm_num⟩
          have hheq := tendsto_nhds_unique htend hlim
          linarith
        · exact hfpp_eq_on_Ioo x ⟨hlt1, hlt2⟩
    have hint_eq : (∫ x in (-1 : ℝ)..1, (iteratedDeriv 2 f x)^2) =
        ∫ x in (-1 : ℝ)..1, ((15/4) * (1 - x^2))^2 := by
      rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
          intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      have hxIcc : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_of_lt hx.1, hx.2⟩
      show (iteratedDeriv 2 f x)^2 = ((15/4) * (1 - x^2))^2
      rw [hfpp_eq_on_Icc x hxIcc, iteratedDeriv_2_extremal]
    rw [hint_eq]
    have h_pull : (∫ x in (-1 : ℝ)..1, ((15/4 : ℝ) * (1 - x^2))^2) =
        (15/4)^2 * ∫ x in (-1 : ℝ)..1, (1 - x^2)^2 := by
      have hh : ∀ x, ((15/4 : ℝ) * (1 - x^2))^2 = (15/4)^2 * (1 - x^2)^2 := by
        intro x; ring
      simp_rw [hh]
      rw [intervalIntegral.integral_const_mul]
    rw [h_pull, integral_g_sq]; ring
  · intro hint15
    have hzero : (∫ x in (-1 : ℝ)..1, (iteratedDeriv 2 f x - (15/4) * (1 - x^2))^2) = 0 := by
      rw [hkey, hint15]; ring
    have hfpp_eq : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        iteratedDeriv 2 f x - (15/4) * (1 - x^2) = 0 :=
      eq_zero_of_integral_sq_eq_zero _
        ((continuous_iteratedDeriv_of_contDiff hf 2 le_rfl).sub
          (continuous_const.mul (by continuity))) hzero
    set hfn : ℝ → ℝ := fun x => f x - extremal x with hfn_def
    have hh_cd : ContDiff ℝ 2 hfn := hf.sub extremal_contDiff
    have hh_fpp : ∀ x ∈ Set.Icc (-1 : ℝ) 1, iteratedDeriv 2 hfn x = 0 := by
      intro x hx
      have hd_deriv : deriv hfn = fun y => deriv f y - deriv extremal y := by
        funext y; rw [hfn_def]
        exact deriv_sub (hf.differentiable (by norm_num) y)
          (extremal_contDiff.differentiable (by norm_num) y)
      have hi2 : iteratedDeriv 2 hfn x =
          iteratedDeriv 2 f x - iteratedDeriv 2 extremal x := by
        rw [show iteratedDeriv 2 hfn = deriv (deriv hfn) by
          rw [iteratedDeriv_succ, iteratedDeriv_one],
          show iteratedDeriv 2 f = deriv (deriv f) by
          rw [iteratedDeriv_succ, iteratedDeriv_one],
          show iteratedDeriv 2 extremal = deriv (deriv extremal) by
          rw [iteratedDeriv_succ, iteratedDeriv_one] ]
        rw [hd_deriv]
        exact deriv_sub ((contDiff_one_deriv hf).differentiable (by decide) x)
          ((contDiff_one_deriv extremal_contDiff).differentiable (by decide) x)
      rw [hi2, iteratedDeriv_2_extremal]
      have := hfpp_eq x hx; linarith
    have hh1 : hfn 1 = 0 := by simp only [hfn_def]; rw [hf1, extremal_at_one]; ring
    have hhm1 : hfn (-1) = 0 := by
      simp only [hfn_def]; rw [hfm1, extremal_at_neg_one]; ring
    have hderiv_h_const : ∀ x ∈ Set.Icc (-1 : ℝ) 1, deriv hfn x = deriv hfn (-1) := by
      intro x hx
      have h_fp_hda : ∀ y, HasDerivAt (deriv hfn) (iteratedDeriv 2 hfn y) y :=
        fun y => hasDerivAt_deriv_of_contDiff2 hh_cd y
      have hfpp_cont : Continuous (iteratedDeriv 2 hfn) :=
        continuous_iteratedDeriv_of_contDiff hh_cd 2 le_rfl
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := deriv hfn) (f' := iteratedDeriv 2 hfn)
        (a := -1) (b := x)
        (fun y _ => h_fp_hda y)
        (hfpp_cont.intervalIntegrable _ _)
      have hzero_int : (∫ y in (-1 : ℝ)..x, iteratedDeriv 2 hfn y) = 0 := by
        rw [intervalIntegral.integral_of_le hx.1]
        apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
        intro y hy
        have hy_Icc : y ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_of_lt hy.1, le_trans hy.2 hx.2⟩
        exact hh_fpp y hy_Icc
      rw [hzero_int] at hFTC; linarith
    set c := deriv hfn (-1) with hc_def
    have hh_val : ∀ x ∈ Set.Icc (-1 : ℝ) 1, hfn x = c * (x + 1) := by
      intro x hx
      have hda : ∀ y, HasDerivAt hfn (deriv hfn y) y :=
        fun y => hasDerivAt_of_contDiff2 hh_cd y
      have hderiv_cont : Continuous (deriv hfn) := (contDiff_one_deriv hh_cd).continuous
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := hfn) (f' := deriv hfn)
        (a := -1) (b := x)
        (fun y _ => hda y)
        (hderiv_cont.intervalIntegrable _ _)
      have hint_dh : (∫ y in (-1 : ℝ)..x, deriv hfn y) = c * (x + 1) := by
        have hconst : ∀ y ∈ Set.uIcc (-1 : ℝ) x, deriv hfn y = c := by
          intro y hy
          rw [uIcc_of_le hx.1] at hy
          have hy_Icc : y ∈ Set.Icc (-1 : ℝ) 1 := ⟨hy.1, le_trans hy.2 hx.2⟩
          exact hderiv_h_const y hy_Icc
        rw [intervalIntegral.integral_congr hconst, intervalIntegral.integral_const]
        simp; ring
      rw [hint_dh, hhm1] at hFTC; linarith
    have hc_zero : c = 0 := by
      have := hh_val 1 (by constructor <;> norm_num)
      rw [hh1] at this; linarith
    intro x hx
    have hzero_at : hfn x = 0 := by rw [hh_val x hx, hc_zero]; ring
    show f x = extremal x
    simp only [hfn_def] at hzero_at
    linarith

end Imc2025P2
