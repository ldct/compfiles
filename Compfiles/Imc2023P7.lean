/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2023, Problem 7

Let `V` be the set of all continuous functions `f : [0,1] → ℝ`, differentiable
on `(0,1)`, with `f(0) = 0` and `f(1) = 1`. Determine all `α ∈ ℝ` such that for
every `f ∈ V`, there exists some `ξ ∈ (0,1)` such that

  `f(ξ) + α = f'(ξ)`.

Answer: `α = 1/(e - 1)`.
-/

namespace Imc2023P7

open Real

/-- The set of admissible α values: those for which every `f ∈ V` has some
`ξ ∈ (0,1)` with `f(ξ) + α = f'(ξ)`. -/
determine answer : Set ℝ := {1 / (Real.exp 1 - 1)}

snip begin

/-- `e > 1`, hence `e - 1 > 0`. -/
lemma e_sub_one_pos : (0 : ℝ) < Real.exp 1 - 1 := by
  have : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr one_pos
  linarith

lemma e_sub_one_ne : (Real.exp 1 - 1 : ℝ) ≠ 0 := ne_of_gt e_sub_one_pos

snip end

problem imc2023_p7 :
    answer = {α : ℝ | ∀ f : ℝ → ℝ,
      ContinuousOn f (Set.Icc (0:ℝ) 1) →
      (∀ x ∈ Set.Ioo (0:ℝ) 1, DifferentiableAt ℝ f x) →
      f 0 = 0 → f 1 = 1 →
      ∃ ξ ∈ Set.Ioo (0:ℝ) 1, f ξ + α = deriv f ξ} := by
  show ({1 / (Real.exp 1 - 1)} : Set ℝ) = _
  ext α
  simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · -- Existence direction: α = 1/(e-1) works for all f ∈ V.
    rintro rfl f hf_cont hf_diff hf0 hf1
    -- Apply Cauchy's MVT to F(x) = f(x) * e^{-x} and G(x) = -e^{-x} on [0,1].
    -- F'(x) = (f'(x) - f(x)) * e^{-x}
    -- G'(x) = e^{-x}
    -- F(1) - F(0) = f(1) * e^{-1} - f(0) * 1 = e^{-1}
    -- G(1) - G(0) = -e^{-1} - (-1) = 1 - e^{-1}
    -- So F'(ξ)/G'(ξ) = e^{-1}/(1 - e^{-1}) = 1/(e - 1).
    -- Hence (f'(ξ) - f(ξ)) = 1/(e-1), i.e., f(ξ) + 1/(e-1) = f'(ξ).
    set F : ℝ → ℝ := fun x => f x * Real.exp (-x) with hF_def
    set G : ℝ → ℝ := fun x => -Real.exp (-x) with hG_def
    -- Continuity of F and G on [0, 1].
    have hexp_neg_cont : Continuous (fun x : ℝ => Real.exp (-x)) :=
      Real.continuous_exp.comp continuous_neg
    have hF_cont : ContinuousOn F (Set.Icc (0:ℝ) 1) :=
      hf_cont.mul hexp_neg_cont.continuousOn
    have hG_cont : ContinuousOn G (Set.Icc (0:ℝ) 1) :=
      (hexp_neg_cont.continuousOn).neg
    -- Derivatives on (0, 1).
    have hF_deriv : ∀ x ∈ Set.Ioo (0:ℝ) 1,
        HasDerivAt F ((deriv f x - f x) * Real.exp (-x)) x := by
      intro x hx
      have hfx : HasDerivAt f (deriv f x) x := (hf_diff x hx).hasDerivAt
      have hexp : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
        have h1 : HasDerivAt (fun y : ℝ => -y) (-1) x := (hasDerivAt_id x).neg
        have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (Real.exp (-x) * (-1)) x :=
          (Real.hasDerivAt_exp (-x)).comp x h1
        convert h2 using 1; ring
      have hprod := hfx.mul hexp
      convert hprod using 1
      ring
    have hG_deriv : ∀ x ∈ Set.Ioo (0:ℝ) 1,
        HasDerivAt G (Real.exp (-x)) x := by
      intro x _
      have h1 : HasDerivAt (fun y : ℝ => -y) (-1) x := (hasDerivAt_id x).neg
      have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (Real.exp (-x) * (-1)) x :=
        (Real.hasDerivAt_exp (-x)).comp x h1
      have h3 : HasDerivAt G (-(Real.exp (-x) * (-1))) x := h2.neg
      convert h3 using 1; ring
    -- Cauchy's MVT.
    obtain ⟨ξ, hξ_mem, hξ_eq⟩ :=
      exists_ratio_hasDerivAt_eq_ratio_slope F (fun x => (deriv f x - f x) * Real.exp (-x))
        one_pos hF_cont hF_deriv G (fun x => Real.exp (-x)) hG_cont hG_deriv
    refine ⟨ξ, hξ_mem, ?_⟩
    -- Compute F(0), F(1), G(0), G(1).
    have hF0 : F 0 = 0 := by simp [F, hf0]
    have hF1 : F 1 = Real.exp (-1) := by simp [F, hf1]
    have hG0 : G 0 = -1 := by simp [G]
    have hG1 : G 1 = -Real.exp (-1) := by simp [G]
    rw [hF0, hF1, hG0, hG1] at hξ_eq
    -- hξ_eq: (-exp(-1) - (-1)) * ((f'(ξ) - f(ξ)) * exp(-ξ))
    --       = (exp(-1) - 0) * exp(-ξ)
    -- i.e., (1 - exp(-1)) * (f'(ξ) - f(ξ)) * exp(-ξ) = exp(-1) * exp(-ξ)
    have hexp_neg_xi_pos : 0 < Real.exp (-ξ) := Real.exp_pos _
    have hexp_neg_xi_ne : Real.exp (-ξ) ≠ 0 := ne_of_gt hexp_neg_xi_pos
    have hexp_neg_one_eq : Real.exp (-1) = 1 / Real.exp 1 := by
      rw [Real.exp_neg]; ring
    have hexp1_pos : 0 < Real.exp 1 := Real.exp_pos _
    have hexp1_ne : Real.exp 1 ≠ 0 := ne_of_gt hexp1_pos
    -- Rearrange to get f(ξ) + 1/(e-1) = deriv f ξ.
    have h_one_minus : (1 - Real.exp (-1)) = (Real.exp 1 - 1) / Real.exp 1 := by
      rw [hexp_neg_one_eq]; field_simp
    have hes : (Real.exp 1 - 1) ≠ 0 := e_sub_one_ne
    -- Simplify hξ_eq.
    have hξ_eq' : (1 - Real.exp (-1)) * ((deriv f ξ - f ξ) * Real.exp (-ξ))
                = Real.exp (-1) * Real.exp (-ξ) := by
      have := hξ_eq
      linarith
    -- Divide both sides by exp(-ξ).
    have hξ_eq'' : (1 - Real.exp (-1)) * (deriv f ξ - f ξ) = Real.exp (-1) := by
      have h := hξ_eq'
      have : (1 - Real.exp (-1)) * ((deriv f ξ - f ξ) * Real.exp (-ξ))
           = ((1 - Real.exp (-1)) * (deriv f ξ - f ξ)) * Real.exp (-ξ) := by ring
      rw [this] at h
      exact mul_right_cancel₀ hexp_neg_xi_ne h
    -- Now compute (deriv f ξ - f ξ) = exp(-1) / (1 - exp(-1)) = 1/(e - 1).
    have h_1me_pos : 0 < 1 - Real.exp (-1) := by
      have : Real.exp (-1) < 1 := by
        rw [hexp_neg_one_eq]
        rw [div_lt_one hexp1_pos]
        exact Real.one_lt_exp_iff.mpr one_pos
      linarith
    have h_1me_ne : (1 - Real.exp (-1)) ≠ 0 := ne_of_gt h_1me_pos
    have h_diff_eq : deriv f ξ - f ξ = Real.exp (-1) / (1 - Real.exp (-1)) := by
      field_simp at hξ_eq''
      rw [eq_div_iff h_1me_ne]
      linarith
    -- Finally show exp(-1)/(1 - exp(-1)) = 1/(e - 1).
    have h_ratio : Real.exp (-1) / (1 - Real.exp (-1)) = 1 / (Real.exp 1 - 1) := by
      rw [hexp_neg_one_eq]
      field_simp
    rw [h_ratio] at h_diff_eq
    linarith
  · -- Uniqueness direction: if α works for all f ∈ V, then α = 1/(e - 1).
    intro hα
    -- Take f(x) = (e^x - 1) / (e - 1). Then f'(x) - f(x) ≡ 1/(e - 1).
    set f : ℝ → ℝ := fun x => (Real.exp x - 1) / (Real.exp 1 - 1) with hf_def
    have hes : (Real.exp 1 - 1) ≠ 0 := e_sub_one_ne
    have hf_cont : ContinuousOn f (Set.Icc (0:ℝ) 1) := by
      have hc : Continuous f :=
        (Real.continuous_exp.sub continuous_const).div_const _
      exact hc.continuousOn
    have hf_deriv_at : ∀ x, HasDerivAt f (Real.exp x / (Real.exp 1 - 1)) x := by
      intro x
      have h1 : HasDerivAt (fun y => Real.exp y - 1) (Real.exp x) x :=
        (Real.hasDerivAt_exp x).sub_const 1
      have h2 : HasDerivAt f (Real.exp x / (Real.exp 1 - 1)) x := h1.div_const _
      exact h2
    have hf_diff : ∀ x ∈ Set.Ioo (0:ℝ) 1, DifferentiableAt ℝ f x :=
      fun x _ => (hf_deriv_at x).differentiableAt
    have hf0 : f 0 = 0 := by
      simp [f]
    have hf1 : f 1 = 1 := by
      show (Real.exp 1 - 1) / (Real.exp 1 - 1) = 1
      exact div_self hes
    have hderiv : ∀ x, deriv f x = Real.exp x / (Real.exp 1 - 1) :=
      fun x => (hf_deriv_at x).deriv
    obtain ⟨ξ, _, hξ⟩ := hα f hf_cont hf_diff hf0 hf1
    -- hξ : f ξ + α = deriv f ξ = exp(ξ)/(e-1)
    -- f ξ = (exp(ξ) - 1)/(e-1)
    -- So α = exp(ξ)/(e-1) - (exp(ξ) - 1)/(e-1) = 1/(e-1).
    rw [hderiv] at hξ
    have : α = 1 / (Real.exp 1 - 1) := by
      have hf_val : f ξ = (Real.exp ξ - 1) / (Real.exp 1 - 1) := rfl
      rw [hf_val] at hξ
      field_simp at hξ ⊢
      linarith
    exact this

end Imc2023P7
