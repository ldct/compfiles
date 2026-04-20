/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2008, Round 2, Problem 1

Find the minimum value of x² + y² + z² where x, y, z are real numbers
such that x³ + y³ + z³ − 3xyz = 1.
-/

namespace UK2008R2P1

def solution_set : Set ℝ :=
  { v | ∃ x y z : ℝ, x^3 + y^3 + z^3 - 3 * x * y * z = 1 ∧ v = x^2 + y^2 + z^2 }

determine min_value : ℝ := 1

problem uk2008_r2_p1 : IsLeast solution_set min_value := by
  constructor
  · -- Achieved at (x, y, z) = (1, 0, 0).
    refine ⟨1, 0, 0, ?_, ?_⟩ <;> norm_num
  · -- Lower bound.
    rintro v ⟨x, y, z, hxyz, hv⟩
    -- Key identity: x³+y³+z³-3xyz = (x+y+z)(x²+y²+z²-xy-yz-zx).
    -- And 2(x²+y²+z²-xy-yz-zx) = (x-y)²+(y-z)²+(z-x)² ≥ 0.
    -- Let s = x+y+z, q = x²+y²+z². Constraint: s(3q - s²)/2 = 1 so s > 0 and
    -- q = (2 + s³)/(3s). AM-GM: (2+s³)/(3s) = 2/(3s) + s²/3 ≥ 1, with equality at s=1.
    have key : (x + y + z) * (x^2 + y^2 + z^2 - (x*y + y*z + z*x)) = 1 := by linarith [hxyz]
    have nn : 0 ≤ (x - y)^2 + (y - z)^2 + (z - x)^2 := by positivity
    -- 2(q - (xy+yz+zx)) = (x-y)²+(y-z)²+(z-x)²
    have h2 : 2 * (x^2 + y^2 + z^2 - (x*y + y*z + z*x)) =
              (x - y)^2 + (y - z)^2 + (z - x)^2 := by ring
    -- So x^2+y^2+z^2 - (xy+yz+zx) ≥ 0.
    have hqxy : 0 ≤ x^2 + y^2 + z^2 - (x*y + y*z + z*x) := by linarith
    -- From key: (x+y+z) > 0, since RHS=1>0 and second factor ≥ 0, so first factor > 0
    -- and in fact second factor > 0 as well.
    have hs_pos : 0 < x + y + z := by
      rcases lt_trichotomy (x + y + z) 0 with hs | hs | hs
      · exfalso; nlinarith [hqxy, key, hs]
      · exfalso; rw [hs] at key; linarith [key]
      · exact hs
    have hq_pos : 0 < x^2 + y^2 + z^2 - (x*y + y*z + z*x) := by
      rcases lt_or_eq_of_le hqxy with h | h
      · exact h
      · exfalso; rw [← h] at key; linarith
    -- q = x²+y²+z², with 2q ≥ s² + (s² - 2(xy+yz+zx))... let me use a nlinarith approach.
    -- We have: s * (3q - s²) = 2 where q = x²+y²+z² and using xy+yz+zx = (s²-q)/2.
    -- Actually: 2*(x²+y²+z² - (xy+yz+zx)) = 3(x²+y²+z²) - (x+y+z)².
    -- So 3q - s² = 2 · (x²+y²+z² - (xy+yz+zx)).
    have h3qs : 3 * (x^2 + y^2 + z^2) - (x + y + z)^2 =
                2 * (x^2 + y^2 + z^2 - (x*y + y*z + z*x)) := by ring
    -- From key: (x+y+z) * (3(x²+y²+z²) - (x+y+z)²) / 2 = 1.
    -- So (x+y+z) * (3(x²+y²+z²) - (x+y+z)²) = 2.
    have hkey2 : (x + y + z) * (3 * (x^2 + y^2 + z^2) - (x + y + z)^2) = 2 := by
      have := key
      linarith [h3qs, this]
    -- Let s = x+y+z, q = x²+y²+z². We have s > 0, and s(3q - s²) = 2, so 3sq = 2 + s³.
    -- Want q ≥ 1, i.e., 3sq ≥ 3s, i.e., 2 + s³ ≥ 3s.
    -- But s³ - 3s + 2 = (s-1)²(s+2) ≥ 0 for s > 0.
    have hcubic : (x + y + z)^3 - 3 * (x + y + z) + 2 =
                  ((x + y + z) - 1)^2 * ((x + y + z) + 2) := by ring
    have hpos : 0 ≤ ((x + y + z) - 1)^2 * ((x + y + z) + 2) := by
      apply mul_nonneg (sq_nonneg _) (by linarith)
    -- So s³ + 2 ≥ 3s, combined with 3sq = s³ + 2, gives 3sq ≥ 3s, and s > 0 so q ≥ 1.
    rw [hv]
    have h3sq : 3 * (x + y + z) * (x^2 + y^2 + z^2) = (x + y + z)^3 + 2 := by
      nlinarith [hkey2]
    nlinarith [h3sq, hpos, hcubic, hs_pos]

end UK2008R2P1
