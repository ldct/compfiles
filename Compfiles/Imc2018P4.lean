/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2018, Problem 4

Find all differentiable `f : (0, ∞) → ℝ` such that
`f(b) - f(a) = (b - a) * f'(√(a*b))` for all `a, b > 0`.

Answer: `f(t) = C₁·t + C₂/t + C₃` for some real constants `C₁, C₂, C₃`.
-/

namespace Imc2018P4

/-- The functional equation: `f(b) - f(a) = (b - a) * f'(√(a*b))` for all `a, b > 0`. -/
def FuncEq (f f' : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 < a → 0 < b → f b - f a = (b - a) * f' (Real.sqrt (a * b))

/-- `f` is differentiable on `(0, ∞)` with derivative `f'`. -/
def HasDerivOnPos (f f' : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → HasDerivAt f (f' t) t

snip begin

/-- The derivative of `t ↦ C₁·t + C₂/t + C₃` on `(0, ∞)` is `C₁ - C₂/t²`. -/
lemma hasDerivAt_solution (C1 C2 C3 : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => C1 * s + C2 / s + C3) (C1 - C2 / t^2) t := by
  have h1 : HasDerivAt (fun s : ℝ => C1 * s) C1 t := by
    simpa using (hasDerivAt_id t).const_mul C1
  have h2 : HasDerivAt (fun s : ℝ => C2 / s) (-(C2 / t^2)) t := by
    have h : HasDerivAt (fun s : ℝ => (s : ℝ)⁻¹) (-(t^2)⁻¹) t :=
      hasDerivAt_inv ht.ne'
    have h' : HasDerivAt (fun s : ℝ => C2 * s⁻¹) (C2 * (-(t^2)⁻¹)) t := h.const_mul C2
    have heq : (fun s : ℝ => C2 * s⁻¹) = (fun s => C2 / s) := by
      funext s; rw [div_eq_mul_inv, mul_comm]
    rw [heq] at h'
    convert h' using 1
    rw [div_eq_mul_inv]; ring
  have h3 : HasDerivAt (fun _ : ℝ => C3) 0 t := hasDerivAt_const _ _
  have h12 : HasDerivAt (fun s : ℝ => C1 * s + C2 / s) (C1 + -(C2 / t^2)) t := h1.add h2
  have h123 : HasDerivAt (fun s : ℝ => C1 * s + C2 / s + C3) (C1 + -(C2 / t^2) + 0) t :=
    h12.add h3
  convert h123 using 1
  ring

/-- Verification: functions of the form `t ↦ C₁·t + C₂/t + C₃` satisfy the FE. -/
lemma solution_satisfies (C1 C2 C3 : ℝ) :
    FuncEq (fun t => C1 * t + C2 / t + C3) (fun t => C1 - C2 / t^2) := by
  intro a b ha hb
  have hab : 0 < a * b := mul_pos ha hb
  have hsqrt : 0 < Real.sqrt (a * b) := Real.sqrt_pos.mpr hab
  have hsq : Real.sqrt (a * b) ^ 2 = a * b := Real.sq_sqrt hab.le
  have ha_ne : a ≠ 0 := ha.ne'
  have hb_ne : b ≠ 0 := hb.ne'
  have habne : a * b ≠ 0 := hab.ne'
  -- Compute both sides.
  -- LHS: C1*b + C2/b + C3 - (C1*a + C2/a + C3) = C1*(b-a) + C2*(1/b - 1/a)
  -- RHS: (b - a) * (C1 - C2/(a*b)) = C1*(b-a) - C2*(b-a)/(a*b)
  --    = C1*(b-a) - C2*(1/a - 1/b) = C1*(b-a) + C2*(1/b - 1/a)
  simp only
  rw [hsq]
  field_simp
  ring

snip end

/-- The solution set: functions of the form `t ↦ C₁·t + C₂/t + C₃` (on `(0,∞)`). -/
determine SolutionSet : Set (ℝ → ℝ) :=
  { f | ∃ C1 C2 C3 : ℝ, ∀ t : ℝ, 0 < t → f t = C1 * t + C2 / t + C3 }

/--
  Main statement. `f` on `(0, ∞)` with derivative `f'` satisfies the functional
  equation iff `f` equals some `t ↦ C₁·t + C₂/t + C₃` on `(0, ∞)`.
-/
problem imc2018_p4 (f f' : ℝ → ℝ) (hf : HasDerivOnPos f f') :
    FuncEq f f' ↔ f ∈ SolutionSet := by
  constructor
  · -- Forward: f satisfies FE ⟹ f is of the specified form.
    -- TODO: The proof proceeds by bootstrapping smoothness from the functional equation:
    --   (1) Setting a = t/2, b = 2t gives f'(t) = (f(2t) - f(t/2)) / (3t/2),
    --       which expresses f' in terms of values of f; hence f' is differentiable,
    --       so f is C². Iterating gives f is C^∞.
    --   (2) Substitute b = e^h * t, a = e^{-h} * t and differentiate 3 times in h, then set h = 0.
    --       This yields 2t³ f'''(t) + 6t² f''(t) = 0, i.e., (t·f(t))''' = 0.
    --   (3) Hence t·f(t) is a polynomial of degree ≤ 2 in t, say t·f(t) = C₂ + C₃·t + C₁·t².
    --       Therefore f(t) = C₁·t + C₂/t + C₃.
    intro _hFE
    sorry
  · -- Backward: f of the specified form satisfies the FE.
    rintro ⟨C1, C2, C3, hform⟩ a b ha hb
    have hab : 0 < a * b := mul_pos ha hb
    have hsqrt : 0 < Real.sqrt (a * b) := Real.sqrt_pos.mpr hab
    have hsq : Real.sqrt (a * b) ^ 2 = a * b := Real.sq_sqrt hab.le
    -- Use uniqueness of derivative to relate f' at √(a*b) to C1 - C2/(a*b).
    have h_has_deriv : HasDerivAt f (f' (Real.sqrt (a * b))) (Real.sqrt (a * b)) :=
      hf _ hsqrt
    -- The model function
    have h_model_deriv : HasDerivAt (fun s => C1 * s + C2 / s + C3)
        (C1 - C2 / (Real.sqrt (a * b))^2) (Real.sqrt (a * b)) :=
      hasDerivAt_solution C1 C2 C3 hsqrt
    -- f agrees with the model on (0, ∞); in particular on a neighborhood of √(a*b).
    have h_eq_nhds : f =ᶠ[nhds (Real.sqrt (a * b))] (fun s => C1 * s + C2 / s + C3) := by
      have hmem : Set.Ioi (0 : ℝ) ∈ nhds (Real.sqrt (a * b)) :=
        IsOpen.mem_nhds isOpen_Ioi hsqrt
      filter_upwards [hmem] with s hs
      exact hform s hs
    -- Hence derivatives agree at √(a*b).
    have h_model_deriv_f : HasDerivAt f (C1 - C2 / (Real.sqrt (a * b))^2) (Real.sqrt (a * b)) :=
      h_model_deriv.congr_of_eventuallyEq h_eq_nhds
    have h_f'_eq : f' (Real.sqrt (a * b)) = C1 - C2 / (Real.sqrt (a * b))^2 :=
      h_has_deriv.unique h_model_deriv_f
    rw [h_f'_eq, hsq]
    rw [hform a ha, hform b hb]
    have ha_ne : a ≠ 0 := ha.ne'
    have hb_ne : b ≠ 0 := hb.ne'
    field_simp
    ring

end Imc2018P4
