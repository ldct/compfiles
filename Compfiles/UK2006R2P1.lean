/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2006, Round 2, Problem 1

Find the minimum possible value of x² + y² given that x and y are real
numbers satisfying xy(x² − y²) = x² + y² and x ≠ 0.
-/

namespace UK2006R2P1

def solution_set : Set ℝ :=
  { v | ∃ x y : ℝ, x ≠ 0 ∧ x * y * (x^2 - y^2) = x^2 + y^2 ∧ v = x^2 + y^2 }

determine min_value : ℝ := 4

problem uk2006_r2_p1 : IsLeast solution_set min_value := by
  constructor
  · -- 4 is in solution_set: take x² = 2+√2, y² = 2-√2. x = √(2+√2), y = √(2-√2).
    -- Need xy(x²-y²) = x²+y². x²-y² = 2√2. x²+y² = 4. So need xy·2√2 = 4, i.e. xy = √2.
    -- xy = √((2+√2)(2-√2)) = √(4-2) = √2. ✓
    refine ⟨Real.sqrt (2 + Real.sqrt 2), Real.sqrt (2 - Real.sqrt 2), ?_, ?_, ?_⟩
    · -- x ≠ 0
      have h1 : 0 < 2 + Real.sqrt 2 := by positivity
      exact Real.sqrt_ne_zero'.mpr h1
    · -- xy(x²-y²) = x²+y²
      have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)
      have h2pos : (2 : ℝ) + Real.sqrt 2 ≥ 0 := by
        have : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
        linarith
      have h2neg : (2 : ℝ) - Real.sqrt 2 ≥ 0 := by
        have : Real.sqrt 2 ≤ 2 := by
          rw [show (2 : ℝ) = Real.sqrt 4 from by rw [show (4 : ℝ) = 2^2 from by norm_num]; exact (Real.sqrt_sq (by norm_num)).symm]
          exact Real.sqrt_le_sqrt (by norm_num)
        linarith
      have hxsq : (Real.sqrt (2 + Real.sqrt 2))^2 = 2 + Real.sqrt 2 := Real.sq_sqrt h2pos
      have hysq : (Real.sqrt (2 - Real.sqrt 2))^2 = 2 - Real.sqrt 2 := Real.sq_sqrt h2neg
      have hprod : Real.sqrt (2 + Real.sqrt 2) * Real.sqrt (2 - Real.sqrt 2) = Real.sqrt 2 := by
        rw [← Real.sqrt_mul h2pos]
        have : (2 + Real.sqrt 2) * (2 - Real.sqrt 2) = 2 := by
          have := hsqrt2
          nlinarith
        rw [this]
      set x := Real.sqrt (2 + Real.sqrt 2)
      set y := Real.sqrt (2 - Real.sqrt 2)
      have hxy_prod : x * y = Real.sqrt 2 := hprod
      have hxsq_eq : x^2 = 2 + Real.sqrt 2 := hxsq
      have hysq_eq : y^2 = 2 - Real.sqrt 2 := hysq
      -- xy(x² - y²) = √2 · (2√2) = 4
      have hxy_times : x * y * (x^2 - y^2) = 4 := by
        rw [hxsq_eq, hysq_eq, hxy_prod]
        ring_nf
        nlinarith [hsqrt2]
      -- x² + y² = 4
      have hxy_sum : x^2 + y^2 = 4 := by rw [hxsq_eq, hysq_eq]; ring
      linarith
    · -- 4 = x² + y²
      have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)
      have h2pos : (2 : ℝ) + Real.sqrt 2 ≥ 0 := by
        have : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
        linarith
      have h2neg : (2 : ℝ) - Real.sqrt 2 ≥ 0 := by
        have : Real.sqrt 2 ≤ 2 := by
          rw [show (2 : ℝ) = Real.sqrt 4 from by rw [show (4 : ℝ) = 2^2 from by norm_num]; exact (Real.sqrt_sq (by norm_num)).symm]
          exact Real.sqrt_le_sqrt (by norm_num)
        linarith
      rw [Real.sq_sqrt h2pos, Real.sq_sqrt h2neg]
      ring
  · -- Lower bound: for any v ∈ solution_set, 4 ≤ v.
    rintro v ⟨x, y, hx_ne, hxy_eq, hv_eq⟩
    subst hv_eq
    -- Show x² + y² ≥ 4 given xy(x²-y²) = x²+y² and x ≠ 0.
    -- Use: (x²+y²)² = (xy)²(x²-y²)² = (xy(x²-y²))² × ... wait let me redo.
    -- From xy(x²-y²) = x²+y², squaring: x²y²(x²-y²)² = (x²+y²)².
    -- Expand (x²+y²)² = x⁴ + 2x²y² + y⁴.
    -- Expand x²y²(x²-y²)² = x²y²(x⁴ - 2x²y² + y⁴) = x⁶y² - 2x⁴y⁴ + x²y⁶.
    -- Hmm. Better: let u = x², v = y². Then xy(x²-y²) = x²+y² means x²y²(x²-y²)² = (x²+y²)²,
    -- uv(u-v)² = (u+v)².
    -- We want to show u+v ≥ 4 given u,v ≥ 0, u > 0, uv(u-v)² = (u+v)².
    -- Substitute s = u+v, p = uv, d = u-v (so s² = (u+v)², d² = s² - 4p).
    -- Equation: p·d² = s². p(s² - 4p) = s². ps² - 4p² = s². 4p² - ps² + s² = 0.
    -- Solving for p: p = (s² ± √(s⁴ - 16s²))/8 = (s² ± s√(s² - 16))/8.
    -- For p real, need s² ≥ 16, i.e. s ≥ 4 (since s > 0).
    -- So x² + y² ≥ 4.
    set u := x^2 with hu_def
    set v := y^2 with hv_def
    have hu_pos : 0 < u := by rw [hu_def]; positivity
    have hv_nn : 0 ≤ v := by rw [hv_def]; positivity
    have hxy_sq : u * v * (u - v)^2 = (u + v)^2 := by
      have : (x * y * (x^2 - y^2))^2 = (x^2 + y^2)^2 := by rw [hxy_eq]
      rw [← hu_def, ← hv_def] at this
      nlinarith [this]
    -- Need to show u + v ≥ 4.
    -- Let s = u + v, p = u * v. Then (u - v)² = s² - 4p.
    -- So p(s² - 4p) = s², i.e. 4p² - ps² + s² = 0.
    -- Discriminant: s⁴ - 16s² ≥ 0, i.e. s² ≥ 16 (since s > 0).
    by_contra h_lt
    push_neg at h_lt
    -- h_lt: u + v < 4
    have hs_pos : 0 < u + v := by linarith
    -- From 4p² - ps² + s² = 0, as quadratic in p, discriminant must be ≥ 0: s⁴ - 16s² ≥ 0.
    -- But s = u + v < 4, so s² < 16, so s⁴ - 16s² = s²(s² - 16) < 0. Contradiction.
    have hp_def : u * v * (u - v)^2 = (u + v)^2 := hxy_sq
    have hud : (u - v)^2 = (u + v)^2 - 4 * (u * v) := by ring
    rw [hud] at hp_def
    -- u*v * ((u+v)² - 4uv) = (u+v)²
    -- Let s = u+v, p = uv. p(s² - 4p) = s². p·s² - 4p² = s². 4p² - ps² + s² = 0.
    -- View as quadratic in p: 4p² - s²·p + s² = 0.
    -- For real p (which we have), discriminant ≥ 0: s⁴ - 16·s² ≥ 0, s² ≥ 16.
    have hpoly : 4 * (u*v)^2 - (u+v)^2 * (u*v) + (u+v)^2 = 0 := by nlinarith [hp_def]
    -- Discriminant of 4P² - S²·P + S² = 0 in P is S⁴ - 16 S² = S²(S² - 16).
    -- Since P exists (and equals u*v ≥ 0), we need S⁴ - 16 S² ≥ 0.
    -- From 4p² - s²p + s² = 0: (4p - s²/... )... Let's use: (8p - s²)² = s⁴ - 16s²
    -- Check: (8p - s²)² = 64p² - 16p·s² + s⁴, and 16·(4p² - s²·p + s²) = 64p² - 16s²p + 16s².
    -- So (8p - s²)² - s⁴ + 16s² = 16·(4p² - s²p + s²) = 0. Thus (8p-s²)² = s⁴ - 16s².
    have hdisc : (8 * (u*v) - (u+v)^2)^2 = (u+v)^4 - 16 * (u+v)^2 := by nlinarith [hpoly]
    have h_nn : (u+v)^4 - 16 * (u+v)^2 ≥ 0 := by
      rw [← hdisc]; positivity
    -- But s < 4, so s² < 16, so s⁴ - 16s² = s²(s²-16) < 0. Contradiction.
    have hs_sq_lt : (u+v)^2 < 16 := by nlinarith [hs_pos, h_lt]
    have hfactor : (u+v)^4 - 16 * (u+v)^2 = (u+v)^2 * ((u+v)^2 - 16) := by ring
    have hs_sq_pos : 0 < (u+v)^2 := by positivity
    have : (u+v)^2 * ((u+v)^2 - 16) < 0 := by nlinarith
    linarith [hfactor ▸ h_nn]

end UK2006R2P1
