/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2019, Round 1, Problem 5

Two solid cylinders are mathematically similar. The sum of their
heights is 1. The sum of their surface areas is 8π. The sum of their
volumes is 2π. Find all possibilities for the dimensions of each
cylinder.
-/

namespace UK2019R1P5

/-- Surface area of a solid cylinder with radius r and height h. -/
noncomputable def surfaceArea (r h : ℝ) : ℝ := 2 * Real.pi * r^2 + 2 * Real.pi * r * h

/-- Volume of a solid cylinder with radius r and height h. -/
noncomputable def volume (r h : ℝ) : ℝ := Real.pi * r^2 * h

/-- The set of possible pairs ((r₁, h₁), (r₂, h₂)) of (radius, height)
for the two cylinders. -/
determine solution_set : Set ((ℝ × ℝ) × (ℝ × ℝ)) := ∅

problem uk2019_r1_p5 (r₁ h₁ r₂ h₂ : ℝ)
    (hr₁ : 0 < r₁) (hh₁ : 0 < h₁) (hr₂ : 0 < r₂) (hh₂ : 0 < h₂) :
    (∃ k : ℝ, 0 < k ∧ r₂ = k * r₁ ∧ h₂ = k * h₁) ∧
    h₁ + h₂ = 1 ∧
    surfaceArea r₁ h₁ + surfaceArea r₂ h₂ = 8 * Real.pi ∧
    volume r₁ h₁ + volume r₂ h₂ = 2 * Real.pi ↔
    ((r₁, h₁), (r₂, h₂)) ∈ solution_set := by
  sorry

end UK2019R1P5
