/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1998, Problem 4 (Day 1)

Let `f : ℝ → ℝ` be twice differentiable with `f(0) = 2`, `f'(0) = -2`,
`f(1) = 1`. Show that there exists `ξ ∈ (0, 1)` with
`f(ξ) f'(ξ) + f''(ξ) = 0`.

## Proof outline (official solution)

Let `g(x) = (1/2) f(x)^2 + f'(x)`. Then `g'(x) = f(x) f'(x) + f''(x)` and
`g(0) = (1/2)·4 + (-2) = 0`. We aim to find `η ∈ (0, 1]` with `g(η) = 0`;
Rolle's theorem applied to `g` on `[0, η]` then yields the desired `ξ`.

* **Case 1**: `f` has no zero on `[0, 1]`. Set `h(x) = x/2 - 1/f(x)`.
  Then `h(0) = -1/2 = h(1)`, so by Rolle's theorem there is
  `η ∈ (0, 1)` with `h'(η) = 0`. Since
  `h'(x) = 1/2 + f'(x)/f(x)^2 = g(x)/f(x)^2`,
  we get `g(η) = 0`.

* **Case 2**: `f` has a zero on `[0, 1]`. Let `z₁ = inf` and
  `z₂ = sup` of the (closed) zero set. Both lie in `(0, 1)` since
  `f(0) = 2 ≠ 0` and `f(1) = 1 ≠ 0`. On `[0, z₁]` we have `f ≥ 0`,
  so the slopes `(f x - f z₁)/(x - z₁)` for `x < z₁` are non-positive
  (numerator non-negative, denominator negative), giving `f'(z₁) ≤ 0`;
  hence `g(z₁) = f'(z₁) ≤ 0`. Symmetrically `g(z₂) ≥ 0`. By IVT applied
  to the continuous `g` on `[z₁, z₂]`, some `η ∈ [z₁, z₂] ⊆ (0, 1)`
  satisfies `g(η) = 0`.
-/

namespace Imc1998P4

open Set Filter Topology

problem imc1998_p4
    (f : ℝ → ℝ)
    (hf : Differentiable ℝ f)
    (hf' : Differentiable ℝ (deriv f))
    (h0 : f 0 = 2)
    (hd0 : deriv f 0 = -2)
    (h1 : f 1 = 1) :
    ∃ ξ ∈ Set.Ioo (0 : ℝ) 1,
      f ξ * deriv f ξ + deriv (deriv f) ξ = 0 := by
  -- Define g(x) = (1/2) f(x)^2 + f'(x).
  set g : ℝ → ℝ := fun x => (1/2) * f x ^ 2 + deriv f x with hg_def
  -- g is differentiable, with g'(x) = f(x) f'(x) + f''(x).
  have hg_diff : Differentiable ℝ g := by
    have h1' : Differentiable ℝ (fun x => (1/2 : ℝ) * f x ^ 2) :=
      (hf.pow 2).const_mul _
    exact h1'.add hf'
  have hg_deriv : ∀ x, deriv g x = f x * deriv f x + deriv (deriv f) x := by
    intro x
    have hf_at : HasDerivAt f (deriv f x) x := (hf x).hasDerivAt
    have hf2_at : HasDerivAt (fun y => f y ^ 2) (2 * f x * deriv f x) x := by
      have := hf_at.pow 2
      convert this using 1
      ring
    have hcm : HasDerivAt (fun y => (1/2 : ℝ) * f y ^ 2)
        ((1/2) * (2 * f x * deriv f x)) x :=
      hf2_at.const_mul (1/2)
    have hf'_at : HasDerivAt (deriv f) (deriv (deriv f) x) x :=
      (hf' x).hasDerivAt
    have hadd : HasDerivAt g
        ((1/2) * (2 * f x * deriv f x) + deriv (deriv f) x) x :=
      hcm.add hf'_at
    rw [hadd.deriv]; ring
  have hg0 : g 0 = 0 := by
    show (1/2) * f 0 ^ 2 + deriv f 0 = 0
    rw [h0, hd0]; norm_num
  have hg_cont : Continuous g := hg_diff.continuous
  -- Reduce to finding η ∈ (0, 1] with g(η) = 0.
  suffices h : ∃ η ∈ Set.Ioc (0 : ℝ) 1, g η = 0 by
    obtain ⟨η, ⟨hη_pos, hη_le⟩, hgη⟩ := h
    -- Apply Rolle's theorem to g on [0, η].
    have hcont : ContinuousOn g (Icc 0 η) := hg_cont.continuousOn
    have hcd : ∀ x ∈ Ioo (0 : ℝ) η, HasDerivAt g (deriv g x) x :=
      fun x _ => (hg_diff x).hasDerivAt
    obtain ⟨ξ, hξ_mem, hξ⟩ :=
      exists_hasDerivAt_eq_zero hη_pos hcont (hg0.trans hgη.symm) hcd
    refine ⟨ξ, ?_, ?_⟩
    · exact ⟨hξ_mem.1, lt_of_lt_of_le hξ_mem.2 hη_le⟩
    · rw [← hg_deriv ξ]; exact hξ
  -- Now we split into cases based on whether f has a zero on [0, 1].
  by_cases hcase : ∀ x ∈ Icc (0 : ℝ) 1, f x ≠ 0
  · -- Case 1: f never zero on [0, 1]. Use h(x) = x/2 - 1/f(x).
    set h : ℝ → ℝ := fun x => x / 2 - 1 / f x with hh_def
    have hf_ne : ∀ x ∈ Icc (0 : ℝ) 1, f x ≠ 0 := hcase
    -- h is differentiable on (0, 1).
    have hh_deriv : ∀ x ∈ Ioo (0 : ℝ) 1,
        HasDerivAt h (1/2 + deriv f x / (f x)^2) x := by
      intro x hx
      have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      have hfx : f x ≠ 0 := hf_ne x hxI
      have h_xs : HasDerivAt (fun y : ℝ => y / 2) (1/2 : ℝ) x := by
        simpa using (hasDerivAt_id x).div_const 2
      have hf_at : HasDerivAt f (deriv f x) x := (hf x).hasDerivAt
      have h_inv_aux : HasDerivAt (fun y : ℝ => (f y)⁻¹)
          (-(deriv f x) / (f x)^2) x :=
        hf_at.inv hfx
      have h_inv : HasDerivAt (fun y : ℝ => 1 / f y)
          (-(deriv f x) / (f x)^2) x := by
        have h_eq : (fun y : ℝ => 1 / f y) = (fun y : ℝ => (f y)⁻¹) := by
          funext y; rw [one_div]
        rw [h_eq]; exact h_inv_aux
      have hsub := h_xs.sub h_inv
      convert hsub using 1
      ring
    -- h(0) = h(1) = -1/2.
    have hh0 : h 0 = -1/2 := by
      show 0 / 2 - 1 / f 0 = -1/2
      rw [h0]; norm_num
    have hh1 : h 1 = -1/2 := by
      show 1 / 2 - 1 / f 1 = -1/2
      rw [h1]; norm_num
    -- h is continuous on [0, 1].
    have hh_cont : ContinuousOn h (Icc (0 : ℝ) 1) := by
      apply ContinuousOn.sub
      · exact (continuous_id.div_const 2).continuousOn
      · apply ContinuousOn.div continuousOn_const hf.continuous.continuousOn
        exact fun x hx => hf_ne x hx
    -- Apply Rolle to h.
    obtain ⟨η, hη_mem, hη⟩ :=
      exists_hasDerivAt_eq_zero (by norm_num : (0 : ℝ) < 1)
        hh_cont (hh0.trans hh1.symm) hh_deriv
    -- Then g(η) = 0.
    have hηI : η ∈ Icc (0 : ℝ) 1 :=
      ⟨le_of_lt hη_mem.1, le_of_lt hη_mem.2⟩
    have hfη : f η ≠ 0 := hf_ne η hηI
    have heq : (1/2 : ℝ) + deriv f η / (f η)^2 = 0 := hη
    -- Multiply through by (f η)^2.
    have hsq : (f η)^2 ≠ 0 := pow_ne_zero 2 hfη
    have hmul : ((1/2 : ℝ) + deriv f η / (f η)^2) * (f η)^2 = 0 := by
      rw [heq]; ring
    have hgη : g η = 0 := by
      show (1/2) * (f η)^2 + deriv f η = 0
      have hexp : ((1/2 : ℝ) + deriv f η / (f η)^2) * (f η)^2 =
          (1/2) * (f η)^2 + deriv f η := by
        field_simp
      linarith [hmul, hexp]
    exact ⟨η, ⟨hη_mem.1, le_of_lt hη_mem.2⟩, hgη⟩
  · -- Case 2: f has a zero in [0, 1].
    push Not at hcase
    obtain ⟨z, hzI, hzf⟩ := hcase
    -- Define the (closed) zero set Z = {x ∈ [0,1] | f x = 0}.
    set Z : Set ℝ := {x ∈ Icc (0 : ℝ) 1 | f x = 0} with hZ_def
    have hZ_ne : Z.Nonempty := ⟨z, hzI, hzf⟩
    -- Z is closed: intersection of [0,1] with f⁻¹{0}.
    have hZ_closed : IsClosed Z := by
      have h_pre : IsClosed (f ⁻¹' {0}) :=
        (isClosed_singleton).preimage hf.continuous
      have hZ_eq : Z = Icc (0 : ℝ) 1 ∩ f ⁻¹' {0} := by
        ext x
        constructor
        · rintro ⟨hxI, hfx⟩; exact ⟨hxI, hfx⟩
        · rintro ⟨hxI, hfx⟩; exact ⟨hxI, hfx⟩
      rw [hZ_eq]
      exact isClosed_Icc.inter h_pre
    have hZ_bdd : BddAbove Z := ⟨1, fun x hx => hx.1.2⟩
    have hZ_bdd_below : BddBelow Z := ⟨0, fun x hx => hx.1.1⟩
    set z₂ := sSup Z with hz2_def
    set z₁ := sInf Z with hz1_def
    have hz2_in_Z : z₂ ∈ Z := hZ_closed.csSup_mem hZ_ne hZ_bdd
    have hz1_in_Z : z₁ ∈ Z := hZ_closed.csInf_mem hZ_ne hZ_bdd_below
    have hz1_le_z2 : z₁ ≤ z₂ :=
      csInf_le_csSup hZ_ne hZ_bdd_below hZ_bdd
    have hz1_I : z₁ ∈ Icc (0 : ℝ) 1 := hz1_in_Z.1
    have hz2_I : z₂ ∈ Icc (0 : ℝ) 1 := hz2_in_Z.1
    have hf_z1 : f z₁ = 0 := hz1_in_Z.2
    have hf_z2 : f z₂ = 0 := hz2_in_Z.2
    -- z₁ > 0 and z₂ < 1.
    have hz1_pos : 0 < z₁ := by
      rcases lt_or_eq_of_le hz1_I.1 with h | h
      · exact h
      · exfalso
        -- h : 0 = z₁
        have heq : f 0 = 0 := h ▸ hf_z1
        rw [h0] at heq; norm_num at heq
    have hz2_lt : z₂ < 1 := by
      rcases lt_or_eq_of_le hz2_I.2 with h | h
      · exact h
      · exfalso
        -- h : z₂ = 1
        have heq : f 1 = 0 := h ▸ hf_z2
        rw [h1] at heq; norm_num at heq
    -- For x ∈ [0, z₁), f x > 0 (and f x ≠ 0 in particular).
    have hf_pos_left : ∀ x ∈ Ico (0 : ℝ) z₁, 0 < f x := by
      intro x hx
      by_contra hle
      push Not at hle
      rcases lt_or_eq_of_le hle with hlt | heq
      · -- f x < 0; f 0 = 2 > 0; IVT gives a zero in [0, x] ⊆ [0, z₁).
        have hcont_xI : ContinuousOn f (Icc 0 x) := hf.continuous.continuousOn
        have h_in : (0 : ℝ) ∈ Icc (f x) (f 0) := by
          rw [h0]; exact ⟨le_of_lt hlt, by norm_num⟩
        obtain ⟨y, hyI, hyf⟩ :=
          intermediate_value_Icc' hx.1 hcont_xI h_in
        -- y ∈ Z (so z₁ ≤ y) and y ≤ x < z₁, contradiction.
        have hyZ : y ∈ Z := by
          refine ⟨⟨hyI.1, ?_⟩, hyf⟩
          exact le_trans hyI.2 (le_trans (le_of_lt hx.2) hz1_I.2)
        have hyle : z₁ ≤ y := csInf_le hZ_bdd_below hyZ
        linarith [hyI.2, hx.2]
      · -- f x = 0; x ∈ Z but x < z₁ = inf Z.
        have hxZ : x ∈ Z := ⟨⟨hx.1, le_trans (le_of_lt hx.2) hz1_I.2⟩, heq⟩
        have hxle : z₁ ≤ x := csInf_le hZ_bdd_below hxZ
        linarith [hx.2]
    -- For x ∈ (z₂, 1], f x > 0.
    have hf_pos_right : ∀ x ∈ Ioc z₂ 1, 0 < f x := by
      intro x hx
      by_contra hle
      push Not at hle
      rcases lt_or_eq_of_le hle with hlt | heq
      · -- f x < 0; f 1 = 1 > 0; IVT gives a zero in [x, 1] ⊆ (z₂, 1].
        have hcont_xI : ContinuousOn f (Icc x 1) := hf.continuous.continuousOn
        have h_in : (0 : ℝ) ∈ Icc (f x) (f 1) := by
          rw [h1]; exact ⟨le_of_lt hlt, by norm_num⟩
        obtain ⟨y, hyI, hyf⟩ :=
          intermediate_value_Icc hx.2 hcont_xI h_in
        have hyZ : y ∈ Z := by
          refine ⟨⟨?_, hyI.2⟩, hyf⟩
          exact le_trans hz2_I.1 (le_trans (le_of_lt hx.1) hyI.1)
        have hyge : y ≤ z₂ := le_csSup hZ_bdd hyZ
        linarith [hyI.1, hx.1]
      · -- f x = 0; x ∈ Z but x > z₂ = sup Z.
        have hxZ : x ∈ Z := ⟨⟨le_trans hz2_I.1 (le_of_lt hx.1), hx.2⟩, heq⟩
        have hxge : x ≤ z₂ := le_csSup hZ_bdd hxZ
        linarith [hx.1]
    -- Now show f'(z₁) ≤ 0 using the slope.
    have hf'_z1_le : deriv f z₁ ≤ 0 := by
      have hf_at : HasDerivAt f (deriv f z₁) z₁ := (hf z₁).hasDerivAt
      -- Slope tendsto along 𝓝[<] z₁ to deriv f z₁.
      have hslope : Tendsto (slope f z₁) (𝓝[≠] z₁) (𝓝 (deriv f z₁)) :=
        hf_at.tendsto_slope
      have hslope_left : Tendsto (slope f z₁) (𝓝[<] z₁) (𝓝 (deriv f z₁)) :=
        hslope.mono_left (nhdsLT_le_nhdsNE _)
      -- For x ∈ [0, z₁) ∩ (𝓝[<] z₁), slope f z₁ x = (f x - f z₁)/(x - z₁) ≤ 0.
      have hev : ∀ᶠ x in 𝓝[<] z₁, slope f z₁ x ≤ 0 := by
        have : ∀ᶠ x in 𝓝[<] z₁, x ∈ Ico (0 : ℝ) z₁ := by
          have hx0 : (𝓝[<] z₁).Tendsto id (𝓝 z₁) :=
            (tendsto_id (α := ℝ)).mono_left nhdsWithin_le_nhds
          have h_lt : ∀ᶠ x in 𝓝[<] z₁, x < z₁ := self_mem_nhdsWithin
          have h_gt : ∀ᶠ x in 𝓝[<] z₁, 0 < x := by
            have : ∀ᶠ x in 𝓝 z₁, 0 < x := by
              have := isOpen_Ioi.mem_nhds (show z₁ ∈ Ioi (0 : ℝ) from hz1_pos)
              exact this
            exact this.filter_mono nhdsWithin_le_nhds
          filter_upwards [h_lt, h_gt] with x hx_lt hx_gt
          exact ⟨le_of_lt hx_gt, hx_lt⟩
        filter_upwards [this] with x hx
        have hfx_pos : 0 < f x := hf_pos_left x hx
        have hxlt : x < z₁ := hx.2
        rw [slope_def_field, hf_z1, sub_zero]
        -- (f x) / (x - z₁) ≤ 0 since f x > 0 and x - z₁ < 0.
        have hxz : x - z₁ < 0 := by linarith
        exact div_nonpos_of_nonneg_of_nonpos (le_of_lt hfx_pos) (le_of_lt hxz)
      exact le_of_tendsto hslope_left hev
    -- f'(z₂) ≥ 0:
    have hf'_z2_ge : 0 ≤ deriv f z₂ := by
      have hf_at : HasDerivAt f (deriv f z₂) z₂ := (hf z₂).hasDerivAt
      have hslope : Tendsto (slope f z₂) (𝓝[≠] z₂) (𝓝 (deriv f z₂)) :=
        hf_at.tendsto_slope
      have hslope_right : Tendsto (slope f z₂) (𝓝[>] z₂) (𝓝 (deriv f z₂)) :=
        hslope.mono_left (nhdsGT_le_nhdsNE _)
      have hev : ∀ᶠ x in 𝓝[>] z₂, 0 ≤ slope f z₂ x := by
        have hmem : ∀ᶠ x in 𝓝[>] z₂, x ∈ Ioc z₂ 1 := by
          have h_gt : ∀ᶠ x in 𝓝[>] z₂, z₂ < x := self_mem_nhdsWithin
          have h_lt : ∀ᶠ x in 𝓝[>] z₂, x ≤ 1 := by
            have : ∀ᶠ x in 𝓝 z₂, x < 1 := by
              exact isOpen_Iio.mem_nhds hz2_lt
            exact (this.filter_mono nhdsWithin_le_nhds).mono (fun _ h => le_of_lt h)
          filter_upwards [h_gt, h_lt] with x hx_gt hx_le
          exact ⟨hx_gt, hx_le⟩
        filter_upwards [hmem] with x hx
        have hfx_pos : 0 < f x := hf_pos_right x hx
        have hxgt : z₂ < x := hx.1
        rw [slope_def_field, hf_z2, sub_zero]
        have hxz : 0 < x - z₂ := by linarith
        exact div_nonneg (le_of_lt hfx_pos) (le_of_lt hxz)
      exact ge_of_tendsto hslope_right hev
    -- Now g(z₁) = (1/2) f(z₁)^2 + f'(z₁) = f'(z₁) ≤ 0.
    have hg_z1 : g z₁ ≤ 0 := by
      show (1/2) * (f z₁)^2 + deriv f z₁ ≤ 0
      rw [hf_z1]; simp; exact hf'_z1_le
    -- g(z₂) ≥ 0.
    have hg_z2 : 0 ≤ g z₂ := by
      show 0 ≤ (1/2) * (f z₂)^2 + deriv f z₂
      rw [hf_z2]; simp; exact hf'_z2_ge
    -- Apply IVT to g on [z₁, z₂]: 0 ∈ [g z₁, g z₂].
    have hcont_g : ContinuousOn g (Icc z₁ z₂) := hg_cont.continuousOn
    have h0_in : (0 : ℝ) ∈ Icc (g z₁) (g z₂) := ⟨hg_z1, hg_z2⟩
    obtain ⟨η, hηI, hηg⟩ :=
      intermediate_value_Icc hz1_le_z2 hcont_g h0_in
    refine ⟨η, ⟨?_, ?_⟩, hηg⟩
    · exact lt_of_lt_of_le hz1_pos hηI.1
    · exact le_trans hηI.2 (le_of_lt hz2_lt)

end Imc1998P4
