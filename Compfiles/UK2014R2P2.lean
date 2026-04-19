/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2014, Round 2, Problem 2

Prove that it is impossible to have a cuboid for which the volume, the
surface area and the perimeter are numerically equal. The perimeter of a
cuboid is the sum of the lengths of all its twelve edges.
-/

namespace UK2014R2P2

problem uk2014_r2_p2 :
    ¬ ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      a * b * c = 2 * (a * b + b * c + c * a) ∧
      a * b * c = 4 * (a + b + c) := by
  rintro ⟨a, b, c, ha, hb, hc, h1, h2⟩
  -- Let s = a+b+c, p = ab+bc+ca, q = abc.
  -- h1: q = 2p, h2: q = 4s, so p = 2s.
  -- AM-GM: (ab+bc+ca)² ≥ 3abc(a+b+c), i.e. p² ≥ 3qs = 3·4s·s = 12s².
  -- But p = 2s, so 4s² ≥ 12s², contradiction (since s > 0).
  have hs_pos : 0 < a + b + c := by linarith
  -- Key inequality: (ab + bc + ca)² ≥ 3abc(a + b + c)
  -- Equivalent: (ab)² + (bc)² + (ca)² ≥ abc(a+b+c) (by expanding and reducing).
  -- Actually (ab+bc+ca)² = (ab)²+(bc)²+(ca)² + 2abc(a+b+c), so
  -- (ab+bc+ca)² ≥ 3abc(a+b+c) ⇔ (ab)²+(bc)²+(ca)² ≥ abc(a+b+c).
  -- And (ab)² + (bc)² ≥ 2·ab·bc = 2ab²c, summing: 2·[(ab)²+(bc)²+(ca)²] ≥ 2(ab²c + a²bc + abc²) = 2abc(a+b+c). ✓
  have hkey : (a*b + b*c + c*a)^2 ≥ 3 * (a*b*c) * (a + b + c) := by
    nlinarith [sq_nonneg (a*b - b*c), sq_nonneg (b*c - c*a), sq_nonneg (c*a - a*b),
               mul_pos ha hb, mul_pos hb hc, mul_pos hc ha,
               mul_pos (mul_pos ha hb) hc]
  -- From h1: a*b+b*c+c*a = (a*b*c)/2, from h2: a*b*c = 4(a+b+c)
  -- So (a*b+b*c+c*a) = 2(a+b+c), squared: 4(a+b+c)² ≥ 3·4(a+b+c)·(a+b+c) = 12(a+b+c)².
  have hp : a*b + b*c + c*a = 2 * (a + b + c) := by linarith
  rw [hp, h2] at hkey
  -- (2(a+b+c))² ≥ 3·4(a+b+c)·(a+b+c)
  -- 4(a+b+c)² ≥ 12(a+b+c)²
  have : 4 * (a+b+c)^2 ≥ 12 * (a+b+c)^2 := by nlinarith [hkey]
  nlinarith [sq_nonneg (a+b+c), hs_pos]

end UK2014R2P2
