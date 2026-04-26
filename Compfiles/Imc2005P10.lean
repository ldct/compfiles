/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2005, Problem 10
(Second day, Problem 4)

Let `f : ℝ → ℝ` be three-times differentiable. Prove that there exists
`ξ ∈ (-1, 1)` such that
  `f'''(ξ) / 6 = (f(1) - f(-1)) / 2 - f'(0)`.
-/

namespace Imc2005P10

open Set

/-!
We follow the standard approach: define a cubic `g` that interpolates the
values `f(-1), f(0), f(1)` and the derivative `f'(0)`, set `h = f - g`, and
apply Rolle's theorem repeatedly to `h`.
-/

problem imc2005_p10 (f f' f'' f''' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ x, HasDerivAt f'' (f''' x) x) :
    ∃ ξ ∈ Ioo (-1 : ℝ) 1,
      f''' ξ / 6 = (f 1 - f (-1)) / 2 - f' 0 := by
  -- Abbreviations for the four values that determine the interpolant.
  set A : ℝ := f (-1)
  set B : ℝ := f 0
  set C : ℝ := f 1
  set D : ℝ := f' 0
  -- Coefficients of the interpolating cubic
  --   g(x) = -A/2 * x^2 (x-1) - B (x^2 - 1) + C/2 * x^2 (x+1) - D * x (x^2 - 1).
  -- Expanding: g(x) = c3 x^3 + c2 x^2 + c1 x + c0 where
  --   c3 = -A/2 + C/2 - D
  --   c2 =  A/2 - B + C/2
  --   c1 =  D
  --   c0 =  B.
  set c3 : ℝ := -A/2 + C/2 - D
  set c2 : ℝ := A/2 - B + C/2
  set c1 : ℝ := D
  set c0 : ℝ := B
  -- Polynomial g and its derivatives.
  set g   : ℝ → ℝ := fun x => c3 * x^3 + c2 * x^2 + c1 * x + c0
  set g'  : ℝ → ℝ := fun x => 3 * c3 * x^2 + 2 * c2 * x + c1
  set g'' : ℝ → ℝ := fun x => 6 * c3 * x + 2 * c2
  -- Derivative facts for g.
  have hg_deriv : ∀ x, HasDerivAt g (g' x) x := by
    intro x
    have hpow3 : HasDerivAt (fun y : ℝ => y^3) (3 * x^2) x := by
      simpa using hasDerivAt_pow 3 x
    have hpow2 : HasDerivAt (fun y : ℝ => y^2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have h1 : HasDerivAt (fun y : ℝ => c3 * y^3) (c3 * (3 * x^2)) x :=
      hpow3.const_mul c3
    have h2 : HasDerivAt (fun y : ℝ => c2 * y^2) (c2 * (2 * x)) x :=
      hpow2.const_mul c2
    have h3 : HasDerivAt (fun y : ℝ => c1 * y) c1 x := by
      simpa using (hasDerivAt_id x).const_mul c1
    have h4 : HasDerivAt (fun _ : ℝ => c0) 0 x := hasDerivAt_const _ _
    have := ((h1.add h2).add h3).add h4
    convert this using 1
    simp [g']
    ring
  have hg'_deriv : ∀ x, HasDerivAt g' (g'' x) x := by
    intro x
    have hpow2 : HasDerivAt (fun y : ℝ => y^2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have h1 : HasDerivAt (fun y : ℝ => 3 * c3 * y^2) (3 * c3 * (2 * x)) x :=
      hpow2.const_mul _
    have h2 : HasDerivAt (fun y : ℝ => 2 * c2 * y) (2 * c2) x := by
      simpa using (hasDerivAt_id x).const_mul (2 * c2)
    have h3 : HasDerivAt (fun _ : ℝ => c1) 0 x := hasDerivAt_const _ _
    have := ((h1.add h2).add h3)
    convert this using 1
    simp [g'']
    ring
  have hg''_deriv : ∀ x, HasDerivAt g'' (6 * c3) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => 6 * c3 * y) (6 * c3) x := by
      simpa using (hasDerivAt_id x).const_mul (6 * c3)
    have h2 : HasDerivAt (fun _ : ℝ => 2 * c2) 0 x := hasDerivAt_const _ _
    have := h1.add h2
    convert this using 1
    simp
  -- Values of g at -1, 0, 1 and g' at 0.
  have hg_neg1 : g (-1) = A := by
    show c3 * (-1)^3 + c2 * (-1)^2 + c1 * (-1) + c0 = A
    simp [c3, c2, c1, c0]; ring
  have hg_zero : g 0 = B := by
    show c3 * (0:ℝ)^3 + c2 * 0^2 + c1 * 0 + c0 = B
    simp [c0]
  have hg_one : g 1 = C := by
    show c3 * (1:ℝ)^3 + c2 * 1^2 + c1 * 1 + c0 = C
    simp [c3, c2, c1, c0]; ring
  have hg'_zero : g' 0 = D := by
    show 3 * c3 * (0:ℝ)^2 + 2 * c2 * 0 + c1 = D
    simp [c1]
  -- Define h = f - g.
  set h    : ℝ → ℝ := fun x => f x - g x
  set h'   : ℝ → ℝ := fun x => f' x - g' x
  set h''  : ℝ → ℝ := fun x => f'' x - g'' x
  set h''' : ℝ → ℝ := fun x => f''' x - 6 * c3
  have hh_deriv : ∀ x, HasDerivAt h (h' x) x := fun x => (hf x).sub (hg_deriv x)
  have hh'_deriv : ∀ x, HasDerivAt h' (h'' x) x := fun x => (hf' x).sub (hg'_deriv x)
  have hh''_deriv : ∀ x, HasDerivAt h'' (h''' x) x :=
    fun x => (hf'' x).sub (hg''_deriv x)
  -- h is continuous everywhere.
  have hh_diff : Differentiable ℝ h := fun x => (hh_deriv x).differentiableAt
  have hh'_diff : Differentiable ℝ h' := fun x => (hh'_deriv x).differentiableAt
  have hh''_diff : Differentiable ℝ h'' := fun x => (hh''_deriv x).differentiableAt
  have hh_cont : Continuous h := hh_diff.continuous
  have hh'_cont : Continuous h' := hh'_diff.continuous
  have hh''_cont : Continuous h'' := hh''_diff.continuous
  -- h(-1) = 0, h(0) = 0, h(1) = 0.
  have hh_neg1 : h (-1) = 0 := by
    show f (-1) - g (-1) = 0
    rw [hg_neg1]; simp [A]
  have hh_zero : h 0 = 0 := by
    show f 0 - g 0 = 0
    rw [hg_zero]; simp [B]
  have hh_one : h 1 = 0 := by
    show f 1 - g 1 = 0
    rw [hg_one]; simp [C]
  have hh'_zero : h' 0 = 0 := by
    show f' 0 - g' 0 = 0
    rw [hg'_zero]; simp [D]
  -- Rolle on [-1, 0]: ∃ η ∈ (-1, 0), h'(η) = 0.
  obtain ⟨η, hη_mem, hη⟩ :
      ∃ c ∈ Ioo (-1 : ℝ) 0, h' c = 0 := by
    refine exists_hasDerivAt_eq_zero (a := -1) (b := 0) (f := h) (f' := h')
      (by norm_num) hh_cont.continuousOn ?_ (fun x _ => hh_deriv x)
    rw [hh_neg1, hh_zero]
  -- Rolle on [0, 1]: ∃ ϑ ∈ (0, 1), h'(ϑ) = 0.
  obtain ⟨ϑ, hϑ_mem, hϑ⟩ :
      ∃ c ∈ Ioo (0 : ℝ) 1, h' c = 0 := by
    refine exists_hasDerivAt_eq_zero (a := 0) (b := 1) (f := h) (f' := h')
      (by norm_num) hh_cont.continuousOn ?_ (fun x _ => hh_deriv x)
    rw [hh_zero, hh_one]
  -- Now h'(η) = h'(0) = h'(ϑ) = 0 with η < 0 < ϑ.
  -- Rolle on h' over [η, 0]: ∃ α ∈ (η, 0), h''(α) = 0.
  obtain ⟨α, hα_mem, hα⟩ :
      ∃ c ∈ Ioo η 0, h'' c = 0 := by
    refine exists_hasDerivAt_eq_zero (a := η) (b := 0) (f := h') (f' := h'')
      hη_mem.2 hh'_cont.continuousOn ?_ (fun x _ => hh'_deriv x)
    rw [hη, hh'_zero]
  -- Rolle on h' over [0, ϑ]: ∃ β ∈ (0, ϑ), h''(β) = 0.
  obtain ⟨β, hβ_mem, hβ⟩ :
      ∃ c ∈ Ioo 0 ϑ, h'' c = 0 := by
    refine exists_hasDerivAt_eq_zero (a := 0) (b := ϑ) (f := h') (f' := h'')
      hϑ_mem.1 hh'_cont.continuousOn ?_ (fun x _ => hh'_deriv x)
    rw [hh'_zero, hϑ]
  -- α < β since α < 0 < β.
  have hαβ : α < β := lt_trans hα_mem.2 hβ_mem.1
  -- Rolle on h'' over [α, β]: ∃ ξ ∈ (α, β), h'''(ξ) = 0.
  obtain ⟨ξ, hξ_mem, hξ⟩ :
      ∃ c ∈ Ioo α β, h''' c = 0 := by
    refine exists_hasDerivAt_eq_zero (a := α) (b := β) (f := h'') (f' := h''')
      hαβ hh''_cont.continuousOn ?_ (fun x _ => hh''_deriv x)
    rw [hα, hβ]
  -- ξ ∈ (-1, 1).
  have hη_lt : (-1 : ℝ) < η := hη_mem.1
  have hϑ_lt : ϑ < 1 := hϑ_mem.2
  have hα_gt : η < α := hα_mem.1
  have hβ_lt : β < ϑ := hβ_mem.2
  have hξ_gt : α < ξ := hξ_mem.1
  have hξ_lt : ξ < β := hξ_mem.2
  have h_in : ξ ∈ Ioo (-1 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · linarith
    · linarith
  refine ⟨ξ, h_in, ?_⟩
  -- h'''(ξ) = 0 means f'''(ξ) = 6 * c3.
  have hξ' : f''' ξ = 6 * c3 := by
    have := hξ
    show f''' ξ = 6 * c3
    have : f''' ξ - 6 * c3 = 0 := hξ
    linarith
  -- 6 * c3 = 3 (C - A) - 6 D, so f'''(ξ)/6 = (C-A)/2 - D.
  rw [hξ']
  show 6 * c3 / 6 = (C - A) / 2 - D
  simp [c3]; ring

end Imc2005P10
