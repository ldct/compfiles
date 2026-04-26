/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2007, Problem 7
(IMC 2007, Day 2, Problem 1)

Let `f : ℝ → ℝ` be a continuous function. Suppose that for every `c > 0`,
the graph of `f` can be moved to the graph of `c · f` by a translation or
a rotation of the plane. Does it follow that `f(x) = a x + b` for some
constants `a, b`?

Answer: No. A counterexample is `f(x) = exp x`, since for every `c > 0`,
`c · exp x = exp(x + log c)`, so the graph of `c · f` is obtained from the
graph of `f` by the translation `(x, y) ↦ (x - log c, y)`.
-/

namespace Imc2007P7

open Real

/-- The graph of a real function, viewed as a subset of `ℝ²`. -/
def graph (f : ℝ → ℝ) : Set (ℝ × ℝ) := {p | p.2 = f p.1}

/-- A translation of the plane by a vector `(a, b)`. -/
def translation (a b : ℝ) : ℝ × ℝ → ℝ × ℝ := fun p => (p.1 + a, p.2 + b)

/-- A rotation of the plane by angle `θ` about the point `(x₀, y₀)`. -/
noncomputable def rotation (θ x₀ y₀ : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  fun p => (x₀ + cos θ * (p.1 - x₀) - sin θ * (p.2 - y₀),
            y₀ + sin θ * (p.1 - x₀) + cos θ * (p.2 - y₀))

/-- A planar motion is either a translation or a rotation. -/
def IsPlanarMotion (φ : ℝ × ℝ → ℝ × ℝ) : Prop :=
  (∃ a b, φ = translation a b) ∨ (∃ θ x₀ y₀, φ = rotation θ x₀ y₀)

/-- The property that for every `c > 0`, the graph of `c · f` is the image of the
graph of `f` under some planar motion (translation or rotation). -/
def HasMotionProperty (f : ℝ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∃ φ : ℝ × ℝ → ℝ × ℝ, IsPlanarMotion φ ∧
    φ '' graph f = graph (fun x => c * f x)

/-- The answer to the problem: No, it does not follow that `f` is affine. -/
determine answer : Prop := False

problem imc2007_p7 :
    (answer ↔
      ∀ f : ℝ → ℝ, Continuous f → HasMotionProperty f →
        ∃ a b : ℝ, ∀ x, f x = a * x + b) := by
  show False ↔ _
  refine ⟨False.elim, fun h => ?_⟩
  -- Apply h to the counterexample f = exp.
  specialize h Real.exp Real.continuous_exp
  -- First show that exp has the motion property.
  have hmotion : HasMotionProperty Real.exp := by
    intro c hc
    -- Use the translation by (-log c, 0).
    refine ⟨translation (-Real.log c) 0, Or.inl ⟨-Real.log c, 0, rfl⟩, ?_⟩
    ext ⟨x, y⟩
    simp only [Set.mem_image, graph, Set.mem_setOf_eq, translation, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨x', y'⟩, hy', hxy⟩
      simp only at hy'
      obtain ⟨hx, hy⟩ := hxy
      -- hy' : y' = exp x', hx : x' + (-log c) = x, hy : y' + 0 = y
      have hx' : x' = x + Real.log c := by linarith
      have hy0 : y' = y := by linarith
      rw [← hy0, hy', hx', Real.exp_add, Real.exp_log hc]
      ring
    · intro hy
      -- Given y = c * exp x, find preimage (x + log c, exp (x + log c)).
      refine ⟨(x + Real.log c, Real.exp (x + Real.log c)), rfl, ?_, ?_⟩
      · ring
      · rw [hy, Real.exp_add, Real.exp_log hc]; ring
  -- So by h, exp is affine.
  obtain ⟨a, b, hab⟩ := h hmotion
  -- But exp is not affine: derive contradiction by evaluating at three points.
  have h0 := hab 0
  have h1 := hab 1
  have h2 := hab 2
  rw [Real.exp_zero] at h0
  -- h0: 1 = a * 0 + b = b
  -- h1: exp 1 = a + b
  -- h2: exp 2 = 2a + b
  have hb : b = 1 := by linarith
  have ha : a = Real.exp 1 - 1 := by linarith
  -- So exp 2 = 2 * (exp 1 - 1) + 1 = 2 * exp 1 - 1.
  have : Real.exp 2 = 2 * Real.exp 1 - 1 := by linarith
  -- But exp 2 = (exp 1)^2, so (exp 1)^2 - 2 * exp 1 + 1 = 0, i.e. (exp 1 - 1)^2 = 0, so exp 1 = 1.
  have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 from by norm_num, Real.exp_add]
  have heq : Real.exp 1 * Real.exp 1 = 2 * Real.exp 1 - 1 := by rw [← hsq]; exact this
  have hperfsq : (Real.exp 1 - 1) ^ 2 = 0 := by ring_nf; linarith
  have hexp1 : Real.exp 1 = 1 := by
    have := sq_eq_zero_iff.mp hperfsq
    linarith
  -- Contradiction: exp 1 > 1.
  have hgt : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := (1 : ℝ)) (by norm_num)
    linarith
  linarith

end Imc2007P7
