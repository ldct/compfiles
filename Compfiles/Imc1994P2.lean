/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1994, Problem 2

Let `f : ℝ → ℝ` be `C¹` on `(a,b)` with `f(x) → +∞` as `x → a+`,
`f(x) → -∞` as `x → b-`, and `f'(x) + f(x)² ≥ -1` on `(a,b)`.
Prove `b - a ≥ π`.

## Proof outline

Consider `g(x) := arctan (f x) + x`. Its derivative is

  `g'(x) = f'(x) / (1 + f(x)²) + 1 = (f'(x) + 1 + f(x)²) / (1 + f(x)²) ≥ 0`

so `g` is monotone on `(a,b)`. Since `arctan(f x) → π/2` as `x → a+` and
`arctan(f x) → -π/2` as `x → b-`, we have

  `g(x) → a + π/2`  as `x → a+`,
  `g(x) → b - π/2`  as `x → b-`.

Picking a midpoint `c ∈ (a,b)`, monotonicity and the limits give
`a + π/2 ≤ g(c) ≤ b - π/2`, hence `b - a ≥ π`.
-/

namespace Imc1994P2

open Real Filter Topology

problem imc1994_p2 (f f' : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hineq : ∀ x ∈ Set.Ioo a b, f' x + (f x)^2 ≥ -1)
    (hatop : Tendsto f (𝓝[>] a) atTop)
    (hbot  : Tendsto f (𝓝[<] b) atBot) :
    b - a ≥ π := by
  -- Define g(x) = arctan(f x) + x
  set g : ℝ → ℝ := fun x => arctan (f x) + x with hg_def
  -- g has derivative g'(x) = 1/(1 + (f x)^2) * f' x + 1 at every x ∈ (a,b)
  have hg_deriv : ∀ x ∈ Set.Ioo a b,
      HasDerivAt g (1 / (1 + (f x)^2) * f' x + 1) x := by
    intro x hx
    have h1 : HasDerivAt (fun y => arctan (f y)) (1 / (1 + (f x)^2) * f' x) x :=
      (hf x hx).arctan
    exact h1.add (hasDerivAt_id x)
  -- Strengthened: g'(x) ≥ 0 for x ∈ (a,b)
  have hg_nonneg : ∀ x ∈ Set.Ioo a b, 0 ≤ 1 / (1 + (f x)^2) * f' x + 1 := by
    intro x hx
    have hpos : 0 < 1 + (f x)^2 := by positivity
    have h1 : 1 / (1 + (f x)^2) * f' x + 1
            = (f' x + (1 + (f x)^2)) / (1 + (f x)^2) := by
      field_simp
    rw [h1]
    apply div_nonneg _ hpos.le
    have := hineq x hx
    linarith
  -- g is continuous on Ioo a b
  have hg_cont : ContinuousOn g (Set.Ioo a b) := by
    intro x hx
    exact ((hg_deriv x hx).continuousAt).continuousWithinAt
  -- Ioo a b is convex
  have hconv : Convex ℝ (Set.Ioo a b) := convex_Ioo a b
  -- interior of Ioo a b is itself
  have hint : interior (Set.Ioo a b) = Set.Ioo a b := isOpen_Ioo.interior_eq
  -- g is differentiable on interior
  have hg_diff : DifferentiableOn ℝ g (interior (Set.Ioo a b)) := by
    rw [hint]
    intro x hx
    exact (hg_deriv x hx).differentiableAt.differentiableWithinAt
  -- deriv g x ≥ 0 on interior
  have hg_deriv_nonneg : ∀ x ∈ interior (Set.Ioo a b), 0 ≤ deriv g x := by
    rw [hint]
    intro x hx
    rw [(hg_deriv x hx).deriv]
    exact hg_nonneg x hx
  -- g is monotone on Ioo a b
  have hg_mono : MonotoneOn g (Set.Ioo a b) :=
    monotoneOn_of_deriv_nonneg hconv hg_cont hg_diff hg_deriv_nonneg
  -- arctan ∘ f tends to π/2 from below at a+
  have h_arctan_a : Tendsto (fun x => arctan (f x)) (𝓝[>] a) (𝓝 (π/2)) := by
    have h1 : Tendsto arctan atTop (𝓝[<] (π / 2)) := tendsto_arctan_atTop
    have h2 : Tendsto arctan atTop (𝓝 (π/2)) := h1.mono_right nhdsWithin_le_nhds
    exact h2.comp hatop
  -- arctan ∘ f tends to -π/2 from above at b-
  have h_arctan_b : Tendsto (fun x => arctan (f x)) (𝓝[<] b) (𝓝 (-(π/2))) := by
    have h1 : Tendsto arctan atBot (𝓝[>] (-(π / 2))) := tendsto_arctan_atBot
    have h2 : Tendsto arctan atBot (𝓝 (-(π/2))) := h1.mono_right nhdsWithin_le_nhds
    exact h2.comp hbot
  -- g tends to a + π/2 at a+
  have hg_a : Tendsto g (𝓝[>] a) (𝓝 (π/2 + a)) := by
    have h1 : Tendsto (fun x : ℝ => x) (𝓝[>] a) (𝓝 a) :=
      Tendsto.mono_left tendsto_id nhdsWithin_le_nhds
    exact h_arctan_a.add h1
  -- g tends to -π/2 + b at b-
  have hg_b : Tendsto g (𝓝[<] b) (𝓝 (-(π/2) + b)) := by
    have h1 : Tendsto (fun x : ℝ => x) (𝓝[<] b) (𝓝 b) :=
      Tendsto.mono_left tendsto_id nhdsWithin_le_nhds
    exact h_arctan_b.add h1
  -- Pick midpoint c
  set c : ℝ := (a + b) / 2 with hc_def
  have hc_mem : c ∈ Set.Ioo a b := by
    refine ⟨?_, ?_⟩ <;> simp [c] <;> linarith
  -- Limit comparison: a + π/2 ≤ g(c)
  have h_left : π/2 + a ≤ g c := by
    -- Eventually for x ∈ (a, c), g x ≤ g c
    have h_eventually : ∀ᶠ x in 𝓝[>] a, g x ≤ g c := by
      filter_upwards [Ioo_mem_nhdsGT hc_mem.1] with x hx
      exact hg_mono ⟨hx.1, lt_trans hx.2 hc_mem.2⟩ hc_mem hx.2.le
    exact le_of_tendsto_of_tendsto hg_a tendsto_const_nhds h_eventually
  -- Limit comparison: g(c) ≤ -π/2 + b
  have h_right : g c ≤ -(π/2) + b := by
    have h_eventually : ∀ᶠ x in 𝓝[<] b, g c ≤ g x := by
      filter_upwards [Ioo_mem_nhdsLT hc_mem.2] with x hx
      exact hg_mono hc_mem ⟨lt_trans hc_mem.1 hx.1, hx.2⟩ hx.1.le
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hg_b h_eventually
  -- Combine
  linarith

end Imc1994P2
