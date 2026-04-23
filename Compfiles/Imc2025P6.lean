/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2025, Problem 6

Let `f : (0, ∞) → ℝ` be a continuously differentiable function, and let
`b > a > 0` be real numbers such that `f(a) = f(b) = k`. Prove that there
exists a point `ξ ∈ (a, b)` such that

  `f(ξ) − ξ f'(ξ) = k`.
-/

namespace Imc2025P6

problem imc2025_p6 (f : ℝ → ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0))
    (a b k : ℝ) (ha : 0 < a) (hab : a < b)
    (hfa : f a = k) (hfb : f b = k) :
    ∃ ξ ∈ Set.Ioo a b, f ξ - ξ * deriv f ξ = k := by
  -- Apply Cauchy's mean value theorem to g(x) = f(x)/x and h(x) = 1/x
  -- on [a, b]. We get ξ ∈ (a, b) such that
  --   (h b - h a) * g'(ξ) = (g b - g a) * h'(ξ).
  -- The LHS simplifies (using 1/b - 1/a = (a-b)/(ab)) to ((a-b)/(ab)) * g'(ξ).
  -- The RHS = (k/b - k/a) * (-1/ξ²) = -k*(a-b)/(ab*ξ²).
  -- Since a < b, (a-b) ≠ 0, dividing by (a-b)/(ab) gives g'(ξ) = -k/ξ².
  -- But g'(ξ) = (ξ f'(ξ) - f(ξ))/ξ², so f(ξ) - ξ f'(ξ) = k.
  set g : ℝ → ℝ := fun x => f x / x with hg_def
  set h : ℝ → ℝ := fun x => 1 / x with hh_def
  have hb : 0 < b := lt_trans ha hab
  -- Ioi-based: for any x > 0, x ≠ 0.
  have hx_ne_of_pos : ∀ {x : ℝ}, 0 < x → x ≠ 0 := fun hx => ne_of_gt hx
  -- f is differentiable at every point of Ioi 0.
  have hf_diffOn : DifferentiableOn ℝ f (Set.Ioi 0) := hf.differentiableOn (by norm_num)
  -- On any open set, ContDiffOn gives HasDerivAt at each interior point.
  have hf_hasDerivAt : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt f (deriv f x) x := by
    intro x hx
    exact ((hf_diffOn x hx).differentiableAt
      (IsOpen.mem_nhds isOpen_Ioi hx)).hasDerivAt
  have hf_cont : ContinuousOn f (Set.Ioi 0) := hf.continuousOn
  -- Icc a b ⊆ Ioi 0.
  have hIcc_sub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact lt_of_lt_of_le ha hx.1
  have hIoo_sub : Set.Ioo a b ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact lt_of_lt_of_le ha hx.1.le
  -- Continuity of g and h on Icc a b.
  have hg_cont : ContinuousOn g (Set.Icc a b) := by
    apply ContinuousOn.div
    · exact hf_cont.mono hIcc_sub
    · exact continuousOn_id
    · intro x hx
      exact ne_of_gt (lt_of_lt_of_le ha hx.1)
  have hh_cont : ContinuousOn h (Set.Icc a b) := by
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro x hx
    exact ne_of_gt (lt_of_lt_of_le ha hx.1)
  -- Derivative of g on Ioo a b.
  have hg_deriv : ∀ x ∈ Set.Ioo a b,
      HasDerivAt g ((x * deriv f x - f x) / x^2) x := by
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le ha hx.1.le
    have hx_ne : x ≠ 0 := ne_of_gt hx_pos
    have hfx := hf_hasDerivAt x (hIoo_sub hx)
    have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
    have hd := hfx.div hid hx_ne
    convert hd using 1
    show (x * deriv f x - f x) / x^2 = (deriv f x * id x - f x * 1) / id x ^ 2
    simp [id]
    ring
  -- Derivative of h on Ioo a b.
  have hh_deriv : ∀ x ∈ Set.Ioo a b, HasDerivAt h (-1 / x^2) x := by
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le ha hx.1.le
    have hx_ne : x ≠ 0 := ne_of_gt hx_pos
    have hd := (hasDerivAt_const x (1:ℝ)).div (hasDerivAt_id x) hx_ne
    convert hd using 1
    show -1 / x^2 = (0 * id x - 1 * 1) / id x ^ 2
    simp [id]
  -- Apply Cauchy's MVT.
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ :=
    exists_ratio_hasDerivAt_eq_ratio_slope g (fun x => (x * deriv f x - f x) / x^2)
      hab hg_cont hg_deriv h (fun x => -1 / x^2) hh_cont hh_deriv
  refine ⟨ξ, hξ_mem, ?_⟩
  have hξ_pos : 0 < ξ := lt_of_lt_of_le ha hξ_mem.1.le
  have hξ_ne : ξ ≠ 0 := ne_of_gt hξ_pos
  have hξ_sq_ne : ξ^2 ≠ 0 := pow_ne_zero 2 hξ_ne
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hb_ne : b ≠ 0 := ne_of_gt hb
  have hab_ne : a - b ≠ 0 := sub_ne_zero.mpr (ne_of_lt hab)
  have hba_ne : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  -- Substitute values of g, h at a and b.
  have hga : g a = k / a := by simp [hg_def, hfa]
  have hgb : g b = k / b := by simp [hg_def, hfb]
  have hha : h a = 1 / a := by simp [hh_def]
  have hhb : h b = 1 / b := by simp [hh_def]
  rw [hga, hgb, hha, hhb] at hξ_eq
  -- Now hξ_eq : (1/b - 1/a) * ((ξ * deriv f ξ - f ξ) / ξ^2) = (k/b - k/a) * (-1/ξ^2).
  -- Multiply both sides by ξ^2 * a * b and simplify.
  have h1 : (1/b - 1/a : ℝ) = (a - b) / (a * b) := by field_simp
  have h2 : (k/b - k/a : ℝ) = k * (a - b) / (a * b) := by
    rw [div_sub_div _ _ hb_ne ha_ne]; ring
  rw [h1, h2] at hξ_eq
  -- hξ_eq : ((a - b)/(a*b)) * ((ξ*f'(ξ) - f(ξ))/ξ^2) = (k*(a - b)/(a*b)) * (-1/ξ^2)
  have hab_prod_ne : a * b ≠ 0 := mul_ne_zero ha_ne hb_ne
  have hξ_eq' := hξ_eq
  field_simp at hξ_eq'
  -- At this point hξ_eq' should have form allowing nlinarith.
  nlinarith [hξ_eq', sq_nonneg (a - b), sq_nonneg ξ, hξ_pos, ha, hb]

end Imc2025P6
