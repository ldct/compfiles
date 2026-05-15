/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2013, Problem 2

Let `f : ℝ → ℝ` be a twice differentiable function with `f(0) = 0`.
Prove that there exists `ξ ∈ (-π/2, π/2)` such that
`f''(ξ) = f(ξ) * (1 + 2 * tan²(ξ))`.
-/

namespace Imc2013P2

open Set Real

snip begin

/-- Auxiliary: on `(-π/2, π/2)`, `cos x > 0`. -/
lemma cos_pos_of_mem {x : ℝ} (hx : x ∈ Ioo (-(π/2)) (π/2)) :
    0 < cos x :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩

snip end

problem imc2013_p2 (f f' f'' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf0 : f 0 = 0) :
    ∃ ξ ∈ Ioo (-(π/2)) (π/2), f'' ξ = f ξ * (1 + 2 * tan ξ ^ 2) := by
  -- Let g(x) = f(x) * cos x.
  set g : ℝ → ℝ := fun x => f x * cos x with hg_def
  -- Its derivative: g'(x) = f'(x) cos x - f(x) sin x.
  set g' : ℝ → ℝ := fun x => f' x * cos x - f x * sin x with hg'_def
  have hg_deriv : ∀ x, HasDerivAt g (g' x) x := by
    intro x
    have h1 : HasDerivAt (fun y => cos y) (-sin x) x := Real.hasDerivAt_cos x
    have h2 : HasDerivAt (fun y => f y * cos y) (f' x * cos x + f x * (-sin x)) x :=
      (hf x).mul h1
    convert h2 using 1
    simp [g']; ring
  -- g is continuous (since differentiable).
  have hg_cont : Continuous g := by
    have : Differentiable ℝ g := fun x => (hg_deriv x).differentiableAt
    exact this.continuous
  -- g(-π/2) = 0, g(0) = 0, g(π/2) = 0.
  have hpi2_pos : (0 : ℝ) < π / 2 := by positivity
  have hg_neg : g (-(π/2)) = 0 := by
    simp [g, Real.cos_neg, Real.cos_pi_div_two]
  have hg_zero : g 0 = 0 := by simp [g, hf0]
  have hg_pos : g (π/2) = 0 := by simp [g, Real.cos_pi_div_two]
  -- Apply Rolle on [-π/2, 0].
  obtain ⟨ξ₁, hξ₁_mem, hξ₁⟩ :
      ∃ c ∈ Ioo (-(π/2)) 0, g' c = 0 := by
    refine exists_hasDerivAt_eq_zero (a := -(π/2)) (b := 0) (f := g) (f' := g')
      (by linarith) hg_cont.continuousOn ?_ (fun x _ => hg_deriv x)
    rw [hg_neg, hg_zero]
  -- Apply Rolle on [0, π/2].
  obtain ⟨ξ₂, hξ₂_mem, hξ₂⟩ :
      ∃ c ∈ Ioo 0 (π/2), g' c = 0 := by
    refine exists_hasDerivAt_eq_zero (a := 0) (b := π/2) (f := g) (f' := g')
      (by linarith) hg_cont.continuousOn ?_ (fun x _ => hg_deriv x)
    rw [hg_zero, hg_pos]
  -- Now ξ₁ < 0 < ξ₂ and both in (-π/2, π/2).
  have hξ₁_in : ξ₁ ∈ Ioo (-(π/2)) (π/2) :=
    ⟨hξ₁_mem.1, lt_trans hξ₁_mem.2 hpi2_pos⟩
  have hξ₂_in : ξ₂ ∈ Ioo (-(π/2)) (π/2) :=
    ⟨lt_trans (by linarith : -(π/2) < 0) hξ₂_mem.1, hξ₂_mem.2⟩
  have hξ₁ξ₂ : ξ₁ < ξ₂ := lt_trans hξ₁_mem.2 hξ₂_mem.1
  -- Define h(x) = g'(x) / cos²(x).
  set h : ℝ → ℝ := fun x => g' x / cos x ^ 2 with hh_def
  -- Define its derivative h' on (-π/2, π/2):
  -- h'(x) = (g''(x) cos x + 2 g'(x) sin x) / cos³(x)
  -- where g''(x) = f''(x) cos x - 2 f'(x) sin x - f(x) cos x.
  set g'' : ℝ → ℝ := fun x => f'' x * cos x - 2 * f' x * sin x - f x * cos x with hg''_def
  have hg'_deriv : ∀ x, HasDerivAt g' (g'' x) x := by
    intro x
    -- g'(x) = f'(x) * cos x - f(x) * sin x
    have h1 : HasDerivAt (fun y => cos y) (-sin x) x := Real.hasDerivAt_cos x
    have h2 : HasDerivAt (fun y => sin y) (cos x) x := Real.hasDerivAt_sin x
    have hp1 : HasDerivAt (fun y => f' y * cos y) (f'' x * cos x + f' x * (-sin x)) x :=
      (hf' x).mul h1
    have hp2 : HasDerivAt (fun y => f y * sin y) (f' x * sin x + f x * cos x) x :=
      (hf x).mul h2
    have hp3 : HasDerivAt (fun y => f' y * cos y - f y * sin y)
        ((f'' x * cos x + f' x * (-sin x)) - (f' x * sin x + f x * cos x)) x :=
      hp1.sub hp2
    convert hp3 using 1
    simp [g'']; ring
  -- Now show HasDerivAt h (h' x) x on Ioo (-π/2) (π/2), where
  -- h'(x) := (g''(x) cos²x + 2 g'(x) cos x sin x) / cos⁴ x
  set hh' : ℝ → ℝ := fun x =>
    (g'' x * cos x ^ 2 + 2 * g' x * cos x * sin x) / cos x ^ 4 with hh'_def
  have hh_deriv : ∀ x ∈ Ioo (-(π/2)) (π/2), HasDerivAt h (hh' x) x := by
    intro x hx
    have hcos_pos : 0 < cos x := cos_pos_of_mem hx
    have hcos_ne : cos x ≠ 0 := ne_of_gt hcos_pos
    have hcos2_ne : cos x ^ 2 ≠ 0 := pow_ne_zero _ hcos_ne
    -- Derivative of cos x ^ 2 is 2 cos x * (- sin x)
    have hcos_d : HasDerivAt (fun y => cos y) (-sin x) x := Real.hasDerivAt_cos x
    have hcos2_d : HasDerivAt (fun y => cos y ^ 2) (2 * cos x * (-sin x)) x := by
      have := hcos_d.pow 2
      convert this using 1
      ring
    -- Quotient rule.
    have hquot : HasDerivAt (fun y => g' y / cos y ^ 2)
        ((g'' x * cos x ^ 2 - g' x * (2 * cos x * (-sin x))) / (cos x ^ 2) ^ 2) x :=
      (hg'_deriv x).div hcos2_d hcos2_ne
    convert hquot using 1
    simp only [hh']
    have hc4 : cos x ^ 4 = (cos x ^ 2) ^ 2 := by ring
    rw [hc4]
    congr 1
    ring
  -- Apply Rolle on [ξ₁, ξ₂] to h.
  -- First need h continuous on [ξ₁, ξ₂] (it's differentiable on (-π/2, π/2) which contains [ξ₁, ξ₂]).
  have hIcc_sub : Icc ξ₁ ξ₂ ⊆ Ioo (-(π/2)) (π/2) := by
    intro y hy
    exact ⟨lt_of_lt_of_le hξ₁_in.1 hy.1, lt_of_le_of_lt hy.2 hξ₂_in.2⟩
  have hIoo_sub : Ioo ξ₁ ξ₂ ⊆ Ioo (-(π/2)) (π/2) := fun y hy =>
    hIcc_sub ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  have hh_cont_on : ContinuousOn h (Icc ξ₁ ξ₂) := by
    intro y hy
    have := (hh_deriv y (hIcc_sub hy)).continuousAt
    exact this.continuousWithinAt
  -- h(ξ₁) = 0 and h(ξ₂) = 0.
  have hh_ξ₁ : h ξ₁ = 0 := by
    simp only [h, hξ₁, zero_div]
  have hh_ξ₂ : h ξ₂ = 0 := by
    simp only [h, hξ₂, zero_div]
  obtain ⟨ξ, hξ_mem, hξ⟩ :
      ∃ c ∈ Ioo ξ₁ ξ₂, hh' c = 0 := by
    refine exists_hasDerivAt_eq_zero (a := ξ₁) (b := ξ₂) (f := h) (f' := hh')
      hξ₁ξ₂ hh_cont_on ?_ (fun x hx => hh_deriv x (hIoo_sub hx))
    rw [hh_ξ₁, hh_ξ₂]
  -- ξ is in Ioo (-(π/2)) (π/2).
  have hξ_in : ξ ∈ Ioo (-(π/2)) (π/2) := hIoo_sub hξ_mem
  refine ⟨ξ, hξ_in, ?_⟩
  -- From hh' ξ = 0, deduce f''(ξ) = f(ξ)(1 + 2 tan²ξ).
  have hcos_pos : 0 < cos ξ := cos_pos_of_mem_Ioo hξ_in
  have hcos_ne : cos ξ ≠ 0 := ne_of_gt hcos_pos
  have hcos2_ne : cos ξ ^ 2 ≠ 0 := pow_ne_zero _ hcos_ne
  have hcos4_ne : cos ξ ^ 4 ≠ 0 := pow_ne_zero _ hcos_ne
  -- hh' ξ = (g'' ξ cos²ξ + 2 g' ξ cos ξ sin ξ) / cos⁴ ξ = 0
  -- So g'' ξ cos²ξ + 2 g' ξ cos ξ sin ξ = 0.
  have hnum : g'' ξ * cos ξ ^ 2 + 2 * g' ξ * cos ξ * sin ξ = 0 := by
    have hξ' : (g'' ξ * cos ξ ^ 2 + 2 * g' ξ * cos ξ * sin ξ) / cos ξ ^ 4 = 0 := hξ
    rw [div_eq_zero_iff] at hξ'
    rcases hξ' with h | h
    · exact h
    · exact absurd h hcos4_ne
  -- Expand g' and g'':
  -- g' ξ = f' ξ cos ξ - f ξ sin ξ
  -- g'' ξ = f'' ξ cos ξ - 2 f' ξ sin ξ - f ξ cos ξ
  have hg'_val : g' ξ = f' ξ * cos ξ - f ξ * sin ξ := rfl
  have hg''_val : g'' ξ = f'' ξ * cos ξ - 2 * f' ξ * sin ξ - f ξ * cos ξ := rfl
  -- Substitute:
  -- (f'' ξ cos ξ - 2 f' ξ sin ξ - f ξ cos ξ) cos²ξ
  --   + 2 (f' ξ cos ξ - f ξ sin ξ) cos ξ sin ξ = 0
  -- = f'' ξ cos³ξ - 2 f' ξ sin ξ cos²ξ - f ξ cos³ξ + 2 f' ξ sin ξ cos²ξ - 2 f ξ sin²ξ cos ξ
  -- = f'' ξ cos³ξ - f ξ cos³ξ - 2 f ξ sin²ξ cos ξ
  -- = cos ξ (f'' ξ cos²ξ - f ξ cos²ξ - 2 f ξ sin²ξ)
  -- = cos ξ (f'' ξ cos²ξ - f ξ (cos²ξ + 2 sin²ξ))
  -- Setting to zero, and using cos ξ ≠ 0:
  -- f'' ξ cos²ξ = f ξ (cos²ξ + 2 sin²ξ) = f ξ (1 + sin²ξ)
  -- Divide by cos²ξ:
  -- f'' ξ = f ξ (1 + sin²ξ)/cos²ξ = f ξ (1 + 2 tan²ξ)
  have hsincos : sin ξ ^ 2 + cos ξ ^ 2 = 1 := Real.sin_sq_add_cos_sq ξ
  have key : f'' ξ * cos ξ ^ 2 = f ξ * (cos ξ ^ 2 + 2 * sin ξ ^ 2) := by
    have hnum' : cos ξ * (f'' ξ * cos ξ ^ 2 - f ξ * (cos ξ ^ 2 + 2 * sin ξ ^ 2)) = 0 := by
      rw [hg''_val, hg'_val] at hnum
      linarith [hnum]
    have : f'' ξ * cos ξ ^ 2 - f ξ * (cos ξ ^ 2 + 2 * sin ξ ^ 2) = 0 := by
      rcases mul_eq_zero.mp hnum' with h | h
      · exact absurd h hcos_ne
      · exact h
    linarith
  -- Now divide by cos²ξ.
  have htan : tan ξ ^ 2 = sin ξ ^ 2 / cos ξ ^ 2 := by
    rw [Real.tan_eq_sin_div_cos]; ring
  rw [htan]
  field_simp
  linarith [key]

end Imc2013P2
