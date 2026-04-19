/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2011, Round 1, Problem 2

Let s be an integer greater than 6. A solid cube of side s has a square
hole of side x < 6 drilled directly through from one face to the opposite
face (so the drill removes a cuboid). The volume of the remaining solid is
numerically equal to the total surface area of the remaining solid.
Determine all possible integer values of x.

Volume of remaining solid: s³ − x²·s.
Surface area: 6s² − 2x² + 4xs (two faces lose an x² square; the hole adds
four x·s rectangles inside).
Equation: s³ − x²·s = 6s² − 2x² + 4xs.
-/

namespace UK2011R1P2

def valid_x : Set ℤ :=
  { x | 0 < x ∧ x < 6 ∧ ∃ s : ℤ, s > 6 ∧ s^3 - x^2 * s = 6 * s^2 - 2 * x^2 + 4 * x * s }

determine answer : Set ℤ := {5}

problem uk2011_r1_p2 : valid_x = answer := by
  ext x
  simp only [valid_x, answer, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx_pos, hx_lt, s, hs_gt, heq⟩
    -- Rewrite equation as x²(s-2) + 4sx - s²(s-6) = 0
    -- i.e. x²(s-2) = s²(s-6) - 4sx, which is quadratic in x with discriminant (2s(s-4))²
    -- Giving x = s(s-6)/(s-2) (positive branch) or x = -s²/(s-2) (negative branch; excluded).
    -- Since 0 < x < 6, s must satisfy: s(s-6)/(s-2) < 6 → s² - 12s + 12 < 0 → s ≤ 10.
    -- So s ∈ {7,8,9,10}, and we check each.
    have hkey : x^2 * (s - 2) + 4 * s * x - s^2 * (s - 6) = 0 := by linarith
    -- Factor: (x(s-2) - s(s-6))(x + s) = x²(s-2) + x(-(s)(s-6)) + xs(s-2) - s²(s-6)
    -- Actually: (x(s-2) + s²)(x - something)...
    -- Let me just use: (x(s-2) - s(s-6))·((s-2)x + s²)  ??
    -- Expand: x·(s-2)·(s-2)·x + x(s-2)s² - s(s-6)(s-2)x - s(s-6)s²
    --   = (s-2)² x² + (s-2)s² x - s(s-6)(s-2) x - s³(s-6)
    -- Compare to (s-2)·(original) = (s-2)(x²(s-2) + 4sx - s²(s-6))
    --   = (s-2)²x² + 4s(s-2)x - s²(s-6)(s-2)
    -- Not quite matching. Try factoring directly.
    -- Key identity: (x·(s-2) - s·(s-6))(x·(s-2) + s²) = (s-2)(x²(s-2) + 4sx - s²(s-6))·(???)
    -- Let's verify at x=5, s=10: (5·8 - 10·4)(5·8 + 100) = (40-40)(140) = 0. Good.
    -- Let a = x(s-2), b = s². Then (a - s(s-6))(a + b) = a² + ab - s(s-6)a - s(s-6)b.
    -- a² = x²(s-2)². ab = x(s-2)s². s(s-6)a = x(s-2)s(s-6). s(s-6)b = s³(s-6).
    -- So expression = x²(s-2)² + x(s-2)s² - x(s-2)s(s-6) - s³(s-6)
    --               = x²(s-2)² + x(s-2)(s² - s(s-6)) - s³(s-6)
    --               = x²(s-2)² + x(s-2)(s·(s - (s-6))) - s³(s-6)
    --               = x²(s-2)² + x(s-2)(6s) - s³(s-6)
    --               = (s-2)[x²(s-2) + 6sx - s²(s-6)·s/(s-2)]... doesn't cleanly factor.
    -- Try: compare to (s-2) · original:
    --   (s-2)(x²(s-2) + 4sx - s²(s-6)) = x²(s-2)² + 4sx(s-2) - s²(s-6)(s-2)
    -- vs (x(s-2) - s(s-6))(x(s-2) + s²):
    --   = x²(s-2)² + x(s-2)s² - s(s-6)x(s-2) - s³(s-6)
    --   = x²(s-2)² + x(s-2)[s² - s(s-6)] - s³(s-6)
    --   = x²(s-2)² + x(s-2)·6s - s³(s-6)
    -- Diff: (s-2)·orig - factored = 4sx(s-2) - 6sx(s-2) + s³(s-6) - s²(s-6)(s-2)
    --   = -2sx(s-2) + s²(s-6)[s - (s-2)] = -2sx(s-2) + 2s²(s-6)
    --   = 2s[-x(s-2) + s(s-6)] = -2s[x(s-2) - s(s-6)]
    -- So (x(s-2) - s(s-6))(x(s-2) + s²) = (s-2)·orig + 2s·(x(s-2) - s(s-6))
    -- i.e. (x(s-2) - s(s-6))(x(s-2) + s² - 2s) = (s-2)·orig
    -- i.e. (x(s-2) - s(s-6))(x(s-2) + s(s-2)) = (s-2)·orig
    -- i.e. (s-2)·(x(s-2) - s(s-6))(x + s) = (s-2)·orig
    -- So since s > 2, we get: (x(s-2) - s(s-6))(x + s) = orig = 0.
    have hfact : (x * (s - 2) - s * (s - 6)) * (x + s) = 0 := by
      have h1 : (s - 2) * ((x * (s - 2) - s * (s - 6)) * (x + s)) =
                (s - 2) * (x^2 * (s - 2) + 4 * s * x - s^2 * (s - 6)) := by ring
      rw [hkey] at h1
      have hs2 : s - 2 ≠ 0 := by omega
      have : (s - 2) * ((x * (s - 2) - s * (s - 6)) * (x + s)) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · omega
      · exact h
    rcases mul_eq_zero.mp hfact with h | h
    · -- x(s-2) = s(s-6)
      have hxs : x * (s - 2) = s * (s - 6) := by linarith
      -- Need 0 < x < 6 and s > 6. Show s ≤ 10.
      have hs_le : s ≤ 10 := by
        by_contra hs_big
        push_neg at hs_big
        -- s ≥ 11 ⇒ x(s-2) = s(s-6) ≥ 11·5 = 55, but x(s-2) ≤ 5·(s-2) = 5s - 10.
        -- So s(s-6) ≤ 5s - 10 ⇒ s² - 11s + 10 ≤ 0 ⇒ (s-1)(s-10) ≤ 0 ⇒ s ≤ 10.
        nlinarith
      interval_cases s
      all_goals (simp at hxs; omega)
    · -- x + s = 0 ⇒ x = -s, but x > 0 and s > 6, contradiction.
      exfalso
      omega
  · rintro rfl
    refine ⟨by norm_num, by norm_num, 10, by norm_num, by norm_num⟩

end UK2011R1P2
